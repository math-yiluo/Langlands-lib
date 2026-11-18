import Langlands.AlgebraicGeometry.EtaleLocalSystem
import Mathlib.AlgebraicGeometry.Stalk
import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-! # Statement: isotriviality of local systems spreads out from local rings -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry

open EtaleLocalSystem

/-- **Spreading out isotriviality from a local ring.** Let `F` be an étale local system with
finitely generated values on a scheme `S`, and let `s` be a point of `S`. If the restriction of
`F` to `Spec 𝒪_{S,s}` becomes constant over a finite étale surjective cover of `Spec 𝒪_{S,s}`,
then `F` becomes constant over a finite étale surjective cover of some open neighbourhood of
`s`. -/
def EtaleLocalSystemIsotrivialSpreadingStatement : Prop :=
  ∀ (S : Scheme.{u}) (F : (Over S)ᵒᵖ ⥤ AddCommGrpCat.{u}),
    IsFinitelyGeneratedLocallyConstant.{u, u} F → ∀ s : S,
      (∃ (L : Scheme.{u}) (p : L ⟶ Spec (S.presheaf.stalk s)), IsFinite p ∧ Etale p ∧
        Surjective p ∧ ∃ M : AddCommGrpCat.{u}, AddGroup.FG M ∧
          Nonempty (restrict (p ≫ S.fromSpecStalk s) F ≅ constant L M)) →
      ∃ U : S.Opens, s ∈ U ∧
        ∃ (U' : Scheme.{u}) (p : U' ⟶ U.toScheme), IsFinite p ∧ Etale p ∧ Surjective p ∧
          ∃ M : AddCommGrpCat.{u}, AddGroup.FG M ∧
            Nonempty (restrict (p ≫ U.ι) F ≅ constant U' M)

end Langlands.AlgebraicGeometry
