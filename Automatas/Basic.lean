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
  rw [← h, List.reverse_reverse]

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
  rwa [← reverse_involutive]
  rw [Set.subset_def]
  intro a h
  rwa [reverse_involutive]

-- No existen palabras en el lenguaje vacío.
-- Podemos utilizar este teorema a través de la táctica `simp`.
@[simp]
lemma not_mem_empty (w : Word α) : w ∉ (∅ : Language α) := by
  exact fun a ↦ a

-- Concatenación con vacío por la izquierda.
theorem empty_concat : (concat ∅ l) = ∅ := by
  rw [Set.eq_empty_iff_forall_not_mem]
  intro x
  rw [concat, @Set.nmem_setOf_iff (List α) _] -- Basta ver qué elementos cumplen la def de concatenación
  rintro ⟨_, fail, _⟩
  exact fail

-- Concatenación con vacío por la derecha.
theorem concat_empty : (concat l ∅) = ∅ := by
  rw [Set.eq_empty_iff_forall_not_mem] -- Basta ver qué elementos cumplen la def de concatenación
  intro x
  rw [concat]
  rintro ⟨_, _, _, fail, _⟩ -- Suponer que hay elementos en ∅ genera una contradicción
  exact fail

-- El lenguaje { ε } es neutro por la izquierda
theorem ε_concat : (concat {ε} l) = l := by
  apply Set.eq_of_subset_of_subset -- Doble contención
  . rw [Set.subset_def] -- Contención ⊆
    intro x h
    rw [concat, @Set.mem_setOf (List α)] at h
    rcases h with ⟨empty, he, h⟩
    rw [Set.mem_singleton_iff] at he -- ε es el único elemento en { ε }
    rw [he] at h
    rcases h with ⟨w, hw, h⟩
    rw [ε, List.nil_append w] at h -- Concatenación con `nil` en listas
    rwa [h]
  . rw [Set.subset_def] -- Contención ⊇
    intro x h
    rw [concat, @Set.mem_setOf (List α)]
    use ε  -- Mostramos existencia con ε
    constructor
    . rfl
    . use x
      constructor
      . exact h
      . rfl

-- El lenguaje { ε } es neutro por la derecha
theorem concat_ε : (concat l {ε}) = l := by
  apply Set.eq_of_subset_of_subset -- Doble contención
  . rw [Set.subset_def] -- Contención ⊆
    intro x h
    rw [concat, @Set.mem_setOf (List α)] at h

    -- Destruimos iteradamente todas las suposiciones
    rcases h with ⟨w, hw, empty, hempty, h⟩

    rw [Set.mem_singleton_iff] at hempty -- ε es el único elemento en { ε }
    rw [hempty, ε, List.append_nil w] at h -- Concatenación con `nil` en listas
    rwa [h]
  . rw [Set.subset_def] -- Contención ⊇
    intro x h
    rw [concat, @Set.mem_setOf (List α)] -- Basta mostrar que es posible construir w = w ++ ε
    use x
    constructor
    . exact h
    . use ε       -- Existencia con ε
      constructor
      . rfl
      . rw [ε, List.append_nil x]


-- La concatenación de lenguajes es asociativa
theorem concat_assoc : concat l (concat m n) = concat (concat l m) n := by
  apply Set.eq_of_subset_of_subset -- Doble contención
  . rw [Set.subset_def] -- Contención ⊆
    intro w hw
    rw [concat, @Set.mem_setOf (List α)] at hw

    -- Destrucción de hipótesis
    rcases hw with ⟨u, hu, h⟩
    rw [concat] at h
    cases' h with v h

    -- Probar una contención equivale a probar que se cumple la
    -- proposición que genera al conjunto.
    rw [@Set.mem_setOf (List α)] at h

    -- Destrucción de hipótesis
    rcases h with ⟨⟨a, ha, b, hb, hv⟩, hw⟩

    rw [hv] at hw
    rw [concat, @Set.mem_setOf (List α)]

    -- Esta es la parte relevante de la prueba:
    use (u ++ a)
    constructor
    . rw [concat, @Set.mem_setOf (List α)]
      use u
      constructor
      . exact hu
      . use a
    . use b
      constructor
      . exact hb
      . rwa [List.append_assoc] -- La concatenación de cadenas (listas) es asociativa

  . rw [Set.subset_def] -- Contención ⊇
    intro w h
    rw [concat, @Set.mem_setOf (List α)] at h

    -- Destrucción de hipótesis
    rcases h with ⟨v, hv, c, hc, hw⟩

    -- Probar una contención equivale a probar que se cumple la
    -- proposición que genera al conjunto.
    rw [concat, @Set.mem_setOf (List α)] at hv

    -- Destrucción de hipótesis
    rcases hv with ⟨a, ha, b, hb, hv⟩

    rw [hv] at hw
    rw [concat, @Set.mem_setOf (List α)]

    -- Esta es la parte relevante de la prueba:
    use a
    constructor
    . exact ha
    . use (b ++ c)
      constructor
      . rw [concat, @Set.mem_setOf (List α)]
        use b
        constructor
        . exact hb
        . use c
      . rwa [← List.append_assoc] -- La concatenación de cadenas (listas) es asociativa

-- La concatenación distribuye por la izquierda sobre la unión
theorem distr_concat_union : (concat l (union m n)) = union (concat l m) (concat l n) := by
  apply Set.eq_of_subset_of_subset -- Doble contención
  . rw [Set.subset_def] -- Contención ⊆
    intro w h
    rw [concat, @Set.mem_setOf (List α)] at h

    -- Destrucción de hipótesis
    rcases h with ⟨u, hu, v, hv, h⟩
    rw [union, @Set.mem_setOf (List α)] at hv ⊢

    -- Análisis de casos: unión izquierda, unión derecha
    rcases hv with ⟨a, ha, h₁⟩ | ⟨a, ha, h₂⟩

    -- Caso: unión con lenguaje izquierdo
    left
    . use (u ++ v)
      -- Simplificacíon de la meta
      rw [concat, @Set.mem_setOf (List α)]
      constructor

      -- Demostración: se puede construir cadena en la unión
      . use u
        constructor
        . exact hu
        . use a
          constructor
          exact ha
          rw [h₁]
      . exact h

    -- Caso: unión con lenguaje derecho
    right
    . use (u ++ v)
      -- Simplificacíon de la meta
      rw [concat, @Set.mem_setOf (List α)]
      constructor

      -- Demostración: se puede construir cadena en la unión
      . use u
        constructor
        . exact hu
        . use a
          constructor
          exact ha
          rw [h₂]
      . exact h

  . rw [Set.subset_def] -- Contención ⊇
    intro w h
    rw [union, @Set.mem_setOf (List α)] at h

    -- Análisis de casos: unión izquierda, unión derecha
    -- y destrucción de hipótesis.
    rcases h with ⟨v, hv, h₁⟩ | ⟨v, hv, h₂⟩

    -- Destrucción de hipótesis
    . rw [concat, @Set.mem_setOf (List α)] at hv
      rcases hv with ⟨x, hx, y, hy, h⟩
      rw [h] at h₁

      -- Simplificación de la meta
      rw [concat, @Set.mem_setOf (List α)]

      -- Demostración: se puede construir cadena en la unión
      use x
      constructor
      . exact hx
      . use y
        constructor
        . rw [union, @Set.mem_setOf (List α)]
          left
          use y
        . exact h₁

    -- Destrucción de hipótesis
    . rw [concat, @Set.mem_setOf (List α)] at hv
      rcases hv with ⟨x, hx, y, hy, h⟩
      rw [h] at h₂

      -- Simplificación de la meta
      rw [concat, @Set.mem_setOf (List α)]

      -- Demostración: se puede construir cadena en la unión
      use x
      constructor
      . exact hx
      . use y
        constructor
        . rw [union, @Set.mem_setOf (List α)]
          right
          use y
        . exact h₂

-- La concatenación distribuye por la derecha sobre la unión
theorem distr_union_concat : (concat (union m n) l) = union (concat m l) (concat n l) := by
  apply Set.eq_of_subset_of_subset -- Doble contención

  . rw [Set.subset_def] -- Contención ⊆
    intro w h
    rw [concat, @Set.mem_setOf (List α)] at h

    -- Destrucción de hipótesis
    rcases h with ⟨u, hu, v, hv, h⟩
    rw [union, @Set.mem_setOf (List α)] at hu ⊢

    -- Análisis de casos: unión izquierda, unión derecha
    -- y destrucción de hipótesis.
    rcases hu with ⟨x, hx, h₁⟩ | ⟨x, hx, h₂⟩

    -- Caso: unión con lenguaje izquierdo
    . left
      rw [h₁] at h

      -- Demostración: se puede construir cadena en la unión
      use (x ++ v)
      constructor
      . rw [concat, @Set.mem_setOf (List α)]
        use x
        constructor
        . exact hx
        . use v
      . exact h

    -- Caso: unión con lenguaje derecho
    . right
      rw [h₂] at h
      use (x ++ v)

      -- Demostración: se puede construir cadena en la unión
      constructor
      . rw [concat, @Set.mem_setOf (List α)]
        rw []
        use x
        constructor
        . exact hx
        . use v
      . exact h

  . rw [Set.subset_def] -- Contención ⊇
    intro w h
    rw [union, @Set.mem_setOf (List α)] at h
    rw [concat, @Set.mem_setOf (List α)]

    -- Análisis de casos: unión izquierda, unión derecha
    rcases h with ⟨u, h₁⟩ | ⟨u, h₂⟩

    -- Destrucción de hipótesis
    . rw [concat, @Set.mem_setOf (List α)] at h₁
      rcases h₁ with ⟨⟨x, hx, y, hy, hu⟩, hw⟩
      rw [hu] at hw

      -- Demostración: se puede construir cadena en la unión
      use x
      constructor
      . rw [union, @Set.mem_setOf (List α)]
        left
        use x
      . use y

    -- Destrucción de hipótesis
    . rw [concat, @Set.mem_setOf (List α)] at h₂
      rcases h₂ with ⟨⟨x, hx, y, hy, hu⟩, hw⟩
      rw [hu] at hw

      -- Demostración: se puede construir cadena en la unión
      use x
      constructor
      . rw [union, @Set.mem_setOf (List α)]
        right
        use x
      . use y
