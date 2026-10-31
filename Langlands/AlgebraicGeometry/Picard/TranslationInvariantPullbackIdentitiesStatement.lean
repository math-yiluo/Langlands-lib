import Langlands.AlgebraicGeometry.Modules.Tensor
import Langlands.AlgebraicGeometry.Picard.GeometricPicardZero

/-! # Multiplication and inversion pullbacks of translation-invariant line bundles -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard

/-- Ordinary translation invariance over an algebraically closed field implies the
multiplication pullback identity and makes the inversion pullback a tensor inverse.
This proposition is a statement target, not a proof. -/
def AlgClosedFieldTranslationInvariantPullbackIdentitiesStatement : Prop :=
  ∀ (K : Type u) [Field K] [IsAlgClosed K] (A : AbelianScheme (Spec (CommRingCat.of K)))
    (L : LineBundle A.X.left),
    GroupScheme.IsTranslationInvariant A.toGrp L →
      let P : Over (Spec (CommRingCat.of K)) := A.X ⨯ A.X
      let p1 : P ⟶ A.X := Limits.prod.fst
      let p2 : P ⟶ A.X := Limits.prod.snd
      let m : P ⟶ A.X := p1 * p2
      let i : A.X.left ⟶ A.X.left := ((𝟙 A.X : A.X ⟶ A.X)⁻¹).left
      Nonempty ((Scheme.Modules.pullback m.left).obj L.obj ≅
        Langlands.Scheme.Modules.tensorObj
          ((Scheme.Modules.pullback p1.left).obj L.obj)
          ((Scheme.Modules.pullback p2.left).obj L.obj)) ∧
      Nonempty (Langlands.Scheme.Modules.tensorObj L.obj
        ((Scheme.Modules.pullback i).obj L.obj) ≅
          Langlands.Scheme.Modules.structureSheaf A.X.left)

end Langlands.AbelianScheme
