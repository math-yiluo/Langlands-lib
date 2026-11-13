import Langlands.Representation.Category.Basic
import Mathlib.Basic.Complex.Basic

/-!
# Characteristic subspaces of a finite-length representation (Renard III.1.10, Proposition)

For a t.d. group countable at infinity, a subgroup `Z` of the centre and a smooth
representation of finite length, the representation is the direct sum of its characteristic
subspaces `V_χ = {v | ∃ m, ∀ z ∈ Z, (π(z) - χ(z))^m v = 0}`, and only finitely many of them
are nonzero.
-/

namespace Langlands

universe uG uV

/-- Renard III.1.10, Proposition, finite-length case: let `G` be a t.d. group countable at
infinity, `Z` a subgroup of the centre of `G` and `(π, V)` a smooth complex representation of
finite length. For a character `χ` of `Z` let
`V_χ = ⋃_m ⋂_{z ∈ Z} ker (π(z) - χ(z))^m`. Then the `V_χ` are independent, they span `V`,
and only finitely many of them are nonzero. -/
def FiniteLengthCharacteristicDecompositionStatement : Prop :=
  ∀ (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G] [SigmaCompactSpace G]
    (Z : Subgroup G), Z ≤ Subgroup.center G →
    ∀ A : SmoothRep.{0, uG, uV} ℂ G, A.HasFiniteLength →
      let V : (Z →* ℂˣ) → Submodule ℂ A := fun χ =>
        ⨆ m : ℕ, ⨅ z : Z,
          LinearMap.ker ((A.representation (z : G) - (χ z : ℂ) • LinearMap.id) ^ m)
      iSupIndep V ∧ (⨆ χ, V χ) = ⊤ ∧ {χ | V χ ≠ ⊥}.Finite

end Langlands
