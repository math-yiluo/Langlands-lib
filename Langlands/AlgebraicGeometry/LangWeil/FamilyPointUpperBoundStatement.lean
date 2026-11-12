import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.Topology.KrullDimension
import Mathlib.Basic.Real.Basic

/-!
# A uniform upper bound for point counts in families over the integers

For a morphism `f : X ⟶ S` of finite type, with `S` of finite type over `ℤ`, the number of
`κ`-points of `X` lying over a `κ`-point `s` of `S` is at most `C (#κ) ^ e` whenever the fibre
of `f` over the image of `s` has dimension at most `e`, with one constant `C` for all finite
fields `κ`, all `κ`-points `s` and all `e`.
-/

universe u

open CategoryTheory CategoryTheory.Limits
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.LangWeil

/-- The uniform Schwartz–Zippel type upper bound in families: for every morphism `f : X ⟶ S`
locally of finite type and quasi-compact, with `S` of finite type over `ℤ`, there is `C > 0`
such that for every finite field `κ`, every `κ`-point `s` of `S` and every `e : ℕ` for which the
fibre of `f` over the point `s (closedPoint κ)` of `S` has topological Krull dimension at most
`e`, the number of `κ`-points `x` of `X` with `f ∘ x = s` is at most `C (#κ) ^ e`. -/
def FamilyPointUpperBoundStatement : Prop :=
  ∀ (S X : Scheme.{u}) (f : X ⟶ S),
    LocallyOfFiniteType (specULiftZIsTerminal.{u}.from S) → CompactSpace S →
    LocallyOfFiniteType f → QuasiCompact f →
    ∃ C : ℝ, 0 < C ∧ ∀ (κ : Type u) [Field κ] [Finite κ]
      (s : Spec (CommRingCat.of κ) ⟶ S) (e : ℕ),
      topologicalKrullDim (f.fiber (s (IsLocalRing.closedPoint κ))) ≤ (e : WithBot ℕ∞) →
      (Nat.card {x : Spec (CommRingCat.of κ) ⟶ X // x ≫ f = s} : ℝ) ≤
        C * (Nat.card κ : ℝ) ^ e

end Langlands.AlgebraicGeometry.LangWeil
