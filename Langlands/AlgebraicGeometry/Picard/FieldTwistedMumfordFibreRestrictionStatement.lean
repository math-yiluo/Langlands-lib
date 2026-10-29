import Langlands.AlgebraicGeometry.Picard.MumfordBundle
import Langlands.AlgebraicGeometry.Picard.GeometricPicardZero

/-! # Both field fibre restrictions of a twisted ordinary Mumford tensor -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules

/-- The two actual fibre restrictions of the ordinary three-factor Mumford
expression followed by a second-projection twist. The factors `N` and `R`
are arbitrary line bundles; no inverse evaluation is needed for this calculation.
This definition states the proposition and does not prove it. -/
def FieldTwistedMumfordFibreRestrictionStatement : Prop :=
  ∀ (preservation : pullbackTensorComparisonIsIsoStatement.{u})
    (K : Type u) [Field K] (A : AbelianScheme (Spec (CommRingCat.of K)))
    (L N R : LineBundle A.X.left),
    let Z : Scheme.{u} := pullback A.X.hom A.X.hom
    let p1 : Z ⟶ A.X.left := pullback.fst A.X.hom A.X.hom
    let p2 : Z ⟶ A.X.left := pullback.snd A.X.hom A.X.hom
    let m : Z ⟶ A.X.left := mumfordAddition A
    let Q : LineBundle Z :=
      LineBundle.tensor preservation
        (LineBundle.tensor preservation
          (LineBundle.tensor preservation
            ((LineBundle.pullback m).obj L)
            ((LineBundle.pullback p1).obj N))
          ((LineBundle.pullback p2).obj N))
        ((LineBundle.pullback p2).obj R)
    ∀ x : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ A.X,
      let i1 : A.X.left ⟶ Z :=
        pullback.lift (A.X.hom ≫ x.left) (𝟙 A.X.left)
          (by simp [Category.assoc, Over.w x])
      let i2 : A.X.left ⟶ Z :=
        pullback.lift (𝟙 A.X.left) (A.X.hom ≫ x.left)
          (by simp [Category.assoc, Over.w x])
      let D : LineBundle A.X.left :=
        LineBundle.tensor preservation
          ((LineBundle.pullback (Langlands.GroupScheme.translation A.toGrp x).left).obj L) N
      Nonempty ((LineBundle.pullback i1).obj Q ≅
        LineBundle.tensor preservation D R) ∧
      Nonempty ((LineBundle.pullback i2).obj Q ≅ D)

end Langlands.AbelianScheme
