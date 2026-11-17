import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Stalk

/-! # Statement: spreading out a factorization from the local scheme at a point -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry

/-- **Spreading out factorizations through a morphism locally of finite presentation** (EGA
IV₃, 8.8.2 (i), for the limit `Spec 𝒪_{S,s} = lim U` over the affine open neighbourhoods
`U` of `s`). Let `p : X ⟶ S` be quasi-compact and quasi-separated, `k : K ⟶ X` locally of
finite presentation and `s ∈ S`. If the projection `X ×_S Spec 𝒪_{S,s} ⟶ X` factors through
`k`, then there is an open neighbourhood `U` of `s` such that the projection
`X ×_S U ⟶ X` factors through `k`. -/
def SpecStalkFactorizationSpreadingStatement : Prop :=
  ∀ (S X K : Scheme.{u}) (p : X ⟶ S) (k : K ⟶ X) (s : S),
    QuasiCompact p → QuasiSeparated p → LocallyOfFinitePresentation k →
    (∃ y : pullback p (S.fromSpecStalk s) ⟶ K, y ≫ k = pullback.fst p (S.fromSpecStalk s)) →
    ∃ U : S.Opens, s ∈ U ∧ ∃ y : pullback p U.ι ⟶ K, y ≫ k = pullback.fst p U.ι

end Langlands.AlgebraicGeometry
