-- Mathlib: Set y List
import Mathlib
-- Paperproof: Pinta las demostraciones de forma bonita
import Paperproof

-- Ambiente global de la biblioteca
namespace AyLF

open Set List

-- Definiciones de tipos
def alphabet := Type*
def Word(α) := List α
def Language(α : alphabet) := Set (Word α)

namespace Language

def ε {α : Type} := @List.nil α

-- En el resto del archivo podemos utilizar que `l` y `m` son lenguajes.
variable {l m : Language α} {a b x : List α}

-- Instancia de clase para Pertenencia a un Lenguaje (visto como conjunto).
instance : Membership (List α) (Language α) := ⟨Set.Mem⟩

-- Definiciones de operaciones
def reverse (l : Language α) : Language α := { w : List α | w.reverse ∈ l }
def concat (l₁ l₂ : Language α) : Language α := { u : List α | ∃ v ∈ l₁, ∃ w ∈ l₂, u = v ++ w }
def union (l₁ l₂ : Language α) : Language α := { u : List α | (∃ v ∈ l₁, u = v) ∨ (∃ v ∈ l₂, u = v) }

-- Instancias de clases
instance : Singleton (List α) (Language α) := ⟨Set.singleton⟩
instance : Insert (List α) (Language α) := ⟨Set.insert⟩
instance : EmptyCollection (Language α) := ⟨(∅ : Set _)⟩
instance : Mul (Language α) := ⟨concat⟩


-- Teoremas


-- La reversa de una palabra w es elemento de la reversa del
-- lenguaje L <-> la palabra w es elemento de L.
lemma word_reverse : w.reverse ∈ l.reverse ↔ w ∈ l := by
  let h (w : Word α) : w.reverse ∈ l ↔ w ∈ (reverse l) := by rfl
  rw [← h]
  rw [List.reverse_reverse]

-- La operación reversa sobre palabras es una involución.
-- Podemos utilizar este teorema a través de la táctica `simp`.
@[simp]
theorem reverse_involutive : w ∈ l.reverse.reverse ↔ w ∈ l := by
  nth_rewrite 2 [← word_reverse]
  nth_rewrite 2 [← word_reverse]
  rw [List.reverse_reverse]

-- La operación de reversa sobre lenguajes es una involución.
theorem rev_involutive : l.reverse.reverse = l := by
  apply Set.eq_of_subset_of_subset
  rw [Set.subset_def]
  intro x h
  rw [← reverse_involutive]
  assumption
  rw [Set.subset_def]
  intro a h
  rw [reverse_involutive]
  assumption

-- No existen palabras en el lenguaje vacío.
-- Podemos utilizar este teorema a través de la táctica `simp`.
@[simp]
lemma not_mem_empty (w : Word α) : w ∉ (∅ : Language α) := by
  exact fun a ↦ a

-- Concatenación con vacío por la izquierda.
theorem empty_concat : (concat ∅ l) = ∅ := by
  rw [Set.eq_empty_iff_forall_not_mem]
  intro x
  rw [concat]
  rw [@Set.nmem_setOf_iff (List α) _] -- Basta ver qué elementos cumplen la def de concatenación
  intro h
  cases' h with x hx
  cases' hx with fail _  -- Suponer que hay elementos en ∅ genera una contradicción
  exact fail

-- Concatenación con vacío por la derecha.
theorem concat_empty : (concat l ∅) = ∅ := by
  rw [Set.eq_empty_iff_forall_not_mem] -- Basta ver qué elementos cumplen la def de concatenación
  intro x
  rw [concat]
  intro h
  cases' h with x hx
  cases' hx with _ hx2
  cases' hx2 with _ hx3
  cases' hx3 with fail _  -- Suponer que hay elementos en ∅ genera una contradicción
  exact fail

-- El lenguaje { ε } es neutro por la izquierda
theorem ε_concat : (concat {ε} l) = l := by
  apply Set.eq_of_subset_of_subset -- Doble contención
  . rw [Set.subset_def] -- Contención ⊆
    intro x h
    simp only [concat] at h
    rw [@Set.mem_setOf (List α)] at h
    cases' h with empty h
    cases' h with he h
    rw [Set.mem_singleton_iff] at he -- ε es el único elemento en { ε }
    rw [he] at h
    cases' h with w h
    cases' h with hw h -- Concatenación con ε
    rw [ε] at h
    rw [List.nil_append w] at h -- Concatenación con `nil` en listas
    rw [h]
    assumption
  . rw [Set.subset_def] -- Contención ⊇
    intro x h
    simp only [concat]
    rw [@Set.mem_setOf (List α)]
    use ε  -- Mostramos existencia con ε
    constructor
    . rfl
    . use x
      constructor
      . assumption
      . rfl

-- El lenguaje { ε } es neutro por la derecha
theorem concat_ε : (concat l {ε}) = l := by
  apply Set.eq_of_subset_of_subset -- Doble contención
  . rw [Set.subset_def] -- Contención ⊆
    intro x h
    simp only [concat] at h
    rw [@Set.mem_setOf (List α)] at h

    -- Destruimos iteradamente todas las suposiciones
    cases' h with w h
    cases' h with hw h
    cases' h with empty h
    cases' h with he h

    rw [Set.mem_singleton_iff] at he -- ε es el único elemento en { ε }
    rw [he] at h
    rw [ε] at h
    rw [List.append_nil w] at h -- Concatenación con `nil` en listas
    rw [h]
    assumption
  . rw [Set.subset_def] -- Contención ⊇
    intro x h
    simp only [concat]
    rw [@Set.mem_setOf (List α)] -- Basta mostrar que es posible construir w = w ++ ε
    use x
    constructor
    . assumption
    . use ε       -- Existencia con ε
      constructor
      . rfl
      . rw [ε]
        rw [List.append_nil x]


-- La concatenación de lenguajes es asociativa
theorem concat_assoc : concat l (concat m n) = concat (concat l m) n := by
  apply Set.eq_of_subset_of_subset -- Doble contención
  . rw [Set.subset_def] -- Contención ⊆
    intro w hw
    rw [concat] at hw
    rw [@Set.mem_setOf (List α)] at hw

    -- Destrucción de hipótesis
    cases' hw with u h
    cases' h with hu h
    rw [concat] at h
    cases' h with v h

    -- Probar una contención equivale a probar que se cumple la
    -- proposición que genera al conjunto.
    rw [@Set.mem_setOf (List α)] at h

    -- Destrucción de hipótesis
    cases' h with h hw
    cases' h with a ha
    cases' ha with ha h
    cases' h with b hb
    cases' hb with hb hv

    rw [hv] at hw
    rw [concat]
    rw [@Set.mem_setOf (List α)]

    -- Esta es la parte relevante de la prueba:
    use (u ++ a)
    constructor
    . rw [concat]
      rw [@Set.mem_setOf (List α)]
      use u
      constructor
      . assumption
      . use a
    . use b
      constructor
      . assumption
      . rw [List.append_assoc] -- La concatenación de cadenas (listas) es asociativa
        assumption

  . rw [Set.subset_def] -- Contención ⊇
    intro w h
    rw [concat] at h
    rw [@Set.mem_setOf (List α)] at h

    -- Destrucción de hipótesis
    cases' h with v h
    cases' h with hv h
    cases' h with c h
    cases' h with hc hw

    -- Probar una contención equivale a probar que se cumple la
    -- proposición que genera al conjunto.
    rw [concat] at hv
    rw [@Set.mem_setOf (List α)] at hv

    -- Destrucción de hipótesis
    cases' hv with a h
    cases' h with ha h
    cases' h with b h
    cases' h with hb hv

    rw [hv] at hw
    rw [concat]
    rw [@Set.mem_setOf (List α)]

    -- Esta es la parte relevante de la prueba:
    use a
    constructor
    . assumption
    . use (b ++ c)
      constructor
      . rw [concat]
        rw [@Set.mem_setOf (List α)]
        use b
        constructor
        . assumption
        . use c
      . rw [← List.append_assoc] -- La concatenación de cadenas (listas) es asociativa
        assumption

-- La concatenación distribuye por la izquierda sobre la unión
theorem distr_concat_union : (concat l (union m n)) = union (concat l m) (concat l n) := by
  apply Set.eq_of_subset_of_subset -- Doble contención
  . rw [Set.subset_def] -- Contención ⊆
    intro w h
    rw [concat] at h
    rw [@Set.mem_setOf (List α)] at h

    -- Destrucción de hipótesis
    cases' h with u h
    cases' h with hu h
    cases' h with v h
    cases' h with hv h
    rw [union] at hv
    rw [@Set.mem_setOf (List α)] at hv
    rw [union]
    rw [@Set.mem_setOf (List α)]

    -- Análisis de casos: unión izquierda, unión derecha
    cases' hv with h₁ h₂
    cases' h₁ with a h₁
    cases' h₁ with ha h₁

    -- Caso: unión con lenguaje izquierdo
    left
    . use (u ++ v)
      -- Simplificacíon de la meta
      rw [concat]
      rw [@Set.mem_setOf (List α)]
      constructor

      -- Demostración: se puede construir cadena en la unión
      . use u
        constructor
        . assumption
        . use a
          constructor
          assumption
          rw [h₁]
      . assumption

    cases' h₂ with a h₂
    cases' h₂ with ha h₂

    -- Caso: unión con lenguaje derecho
    right
    . use (u ++ v)
      -- Simplificacíon de la meta
      rw [concat]
      rw [@Set.mem_setOf (List α)]
      constructor

      -- Demostración: se puede construir cadena en la unión
      . use u
        constructor
        . assumption
        . use a
          constructor
          assumption
          rw [h₂]
      . assumption

  . rw [Set.subset_def] -- Contención ⊇
    intro w h
    rw [union] at h
    rw [@Set.mem_setOf (List α)] at h

    -- Análisis de casos: unión izquierda, unión derecha
    cases' h with h₁ h₂

    -- Destrucción de hipótesis
    . cases' h₁ with v h₁
      cases' h₁ with hv h₁
      rw [concat] at hv
      rw [@Set.mem_setOf (List α)] at hv
      cases' hv with x h
      cases' h with hx h
      cases' h with y h
      cases' h with hy h
      rw [h] at h₁

      -- Simplificación de la meta
      rw [concat]
      rw [@Set.mem_setOf (List α)]

      -- Demostración: se puede construir cadena en la unión
      use x
      constructor
      . assumption
      . use y
        constructor
        . rw [union]
          rw [@Set.mem_setOf (List α)]
          left
          use y
        . assumption

    -- Destrucción de hipótesis
    . cases' h₂ with v h₂
      cases' h₂ with hv h₂
      rw [concat] at hv
      rw [@Set.mem_setOf (List α)] at hv
      cases' hv with x h
      cases' h with hx h
      cases' h with y h
      cases' h with hy h
      rw [h] at h₂

      -- Simplificación de la meta
      rw [concat]
      rw [@Set.mem_setOf (List α)]

      -- Demostración: se puede construir cadena en la unión
      use x
      constructor
      . assumption
      . use y
        constructor
        . rw [union]
          rw [@Set.mem_setOf (List α)]
          right
          use y
        . assumption

-- La concatenación distribuye por la derecha sobre la unión
theorem distr_union_concat : (concat (union m n) l) = union (concat m l) (concat n l) := by
  apply Set.eq_of_subset_of_subset -- Doble contención

  . rw [Set.subset_def] -- Contención ⊆
    intro w h
    rw [concat] at h
    rw [@Set.mem_setOf (List α)] at h

    -- Destrucción de hipótesis
    cases' h with u h
    cases' h with hu h
    cases' h with v h
    cases' h with hv h
    rw [union] at hu
    rw [@Set.mem_setOf (List α)] at hu
    rw [union]
    rw [@Set.mem_setOf (List α)]

    -- Análisis de casos: unión izquierda, unión derecha
    cases' hu with h₁ h₂

    -- Caso: unión con lenguaje izquierdo
    . left
      -- Destrucción de hipótesis
      cases' h₁ with x h₁
      cases' h₁ with hx h₁
      rw [h₁] at h

      -- Demostración: se puede construir cadena en la unión
      use (x ++ v)
      constructor
      . rw [concat]
        rw [@Set.mem_setOf (List α)]
        use x
        constructor
        . assumption
        . use v
      . assumption

    -- Caso: unión con lenguaje derecho
    . right
      -- Destrucción de hipótesis
      cases' h₂ with x h₂
      cases' h₂ with hx h₂
      rw [h₂] at h
      use (x ++ v)

      -- Demostración: se puede construir cadena en la unión
      constructor
      . rw [concat]
        rw [@Set.mem_setOf (List α)]
        use x
        constructor
        . assumption
        . use v
      . assumption

  . rw [Set.subset_def] -- Contención ⊇
    intro w h
    rw [union] at h
    rw [@Set.mem_setOf (List α)] at h
    rw [concat]
    rw [@Set.mem_setOf (List α)]

    -- Análisis de casos: unión izquierda, unión derecha
    cases' h with h₁ h₂

    -- Destrucción de hipótesis
    . rw [concat] at h₁
      cases' h₁ with u h₁
      rw [@Set.mem_setOf (List α)] at h₁
      cases' h₁ with h₁ hw
      cases' h₁ with x h₁
      cases' h₁ with hx h₁
      cases' h₁ with y h₁
      cases' h₁ with hy hu
      rw [hu] at hw

      -- Demostración: se puede construir cadena en la unión
      use x
      constructor
      . rw [union]
        rw [@Set.mem_setOf (List α)]
        left
        use x
      . use y

    -- Destrucción de hipótesis
    . rw [concat] at h₂
      cases' h₂ with u h₂
      rw [@Set.mem_setOf (List α)] at h₂
      cases' h₂ with h₂ hw
      cases' h₂ with x h₂
      cases' h₂ with hx h₂
      cases' h₂ with y h₂
      cases' h₂ with hy hu
      rw [hu] at hw

      -- Demostración: se puede construir cadena en la unión
      use x
      constructor
      . rw [union]
        rw [@Set.mem_setOf (List α)]
        right
        use x
      . use y
