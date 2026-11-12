import Langlands.LinearAlgebra.EvenPathDistance
import Langlands.LinearAlgebra.RootDatumPathWeights

/-! # Even-path families and orbit orderings of their remaining simple roots -/

noncomputable section

universe u v w z

open Langlands.LinearAlgebra.RootDatumPathWeights

namespace Langlands.LinearAlgebra.RootDatumEvenPathGeometry

set_option autoImplicit false

variable {I : Type u} {M : Type v} {N : Type w}
    [AddCommGroup M] [AddCommGroup N] {P : RootDatum I M N} (b : P.Base)

/-- Disjoint even type-A components, before any merged-root maps are chosen. -/
structure EvenPathFamily (J : Type u) where
  half : J → ℕ
  path : (c : J) → Fin (2 * half c) → b.support
  isPathComponent : ∀ c, IsPathComponent (P := P) (b := b) (path c)
  disjoint : ∀ (c c' : J) (i : Fin (2 * half c)) (i' : Fin (2 * half c')),
    path c i = path c' i' → c = c'

namespace EvenPathFamily

variable {b} {J : Type u} (C : EvenPathFamily b J)

/-- The left vertex of the middle pair. -/
def middleLeft (c : J) : b.support :=
  C.path c ⟨C.half c - 1, by have := (C.isPathComponent c).pos; omega⟩

/-- The right vertex of the middle pair. -/
def middleRight (c : J) : b.support :=
  C.path c ⟨C.half c, by have := (C.isPathComponent c).pos; omega⟩

/-- Simple roots left after deleting the middle pairs of all selected paths. -/
abbrev Rest : Type u :=
  {a : b.support // ∀ c, a ≠ C.middleLeft c ∧ a ≠ C.middleRight c}

/-- The remaining vertices of each selected path occur in increasing distance
from its middle pair. Vertices of equal distance can occur in either order. -/
def IsMiddleOut {q : ℕ} (e : Fin q ≃ C.Rest) : Prop :=
  ∀ (c : J) (i i' : Fin (2 * C.half c)) (j j' : Fin q),
    (e j).val = C.path c i → (e j').val = C.path c i' →
      Langlands.GroupScheme.SplitPinning.middleDistance (C.half c) i <
        Langlands.GroupScheme.SplitPinning.middleDistance (C.half c) i' → j < j'

variable {Γ : Type z} [Group Γ] (ρ : Γ →* Equiv.Perm b.support)

/-- An action on the chosen paths which preserves lengths and maps each path
in order or in reverse order, compatibly with the simple-root action. -/
structure CompatibleAction where
  action : Γ →* Equiv.Perm J
  half_eq : ∀ (γ : Γ) (c : J), C.half (action γ c) = C.half c
  path_eq : ∀ (γ : Γ) (c : J), ∃ reverse : Bool, ∀ i : Fin (2 * C.half c),
    ρ γ (C.path c i) = C.path (action γ c)
      (Fin.cast (congrArg (fun m => 2 * m) (half_eq γ c)).symm
        (if reverse then i.rev else i))

/-- A middle-out ordering in actual invariant orbit blocks. Distinct roots
inside a block are orthogonal, so their canonical factors can commute. -/
structure OrbitOrdering where
  length : ℕ
  order : Fin length ≃ C.Rest
  middleOut : C.IsMiddleOut order
  blocks : List (List C.Rest)
  flatten_eq : blocks.flatten = List.ofFn order
  invariant : ∀ (γ : Γ) (l : List C.Rest), l ∈ blocks →
    (l.map (fun a => ρ γ a.val)).Perm (l.map Subtype.val)
  same_orbit : ∀ (l : List C.Rest), l ∈ blocks →
    ∀ (a a' : C.Rest), a ∈ l → a' ∈ l → ∃ γ : Γ, ρ γ a.val = a'.val
  pairwise : ∀ (l : List C.Rest), l ∈ blocks →
    l.Pairwise (fun a a' => a ≠ a' ∧ P.IsOrthogonal (a.val : I) (a'.val : I))

end EvenPathFamily

end Langlands.LinearAlgebra.RootDatumEvenPathGeometry
