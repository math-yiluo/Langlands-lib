import Langlands.AlgebraicGeometry.Picard.MumfordBundle
import Langlands.AlgebraicGeometry.Picard.Ample

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules

/-- The field input used by the diagonal assembly of ample extension. -/
def FieldAmpleDiagonalCorrespondenceStatement : Prop :=
  ∀ (K : Type u) [Field K] (A : AbelianScheme (Spec (CommRingCat.of K))),
    (∃ L : LineBundle A.X.left, L.IsAmple) →
    ∃ D : LineBundle (mumfordProduct A).left,
      Nonempty ((Scheme.Modules.pullback (mumfordSection A)).obj D.obj ≅
        structureSheaf A.X.left) ∧
      Nonempty ((Scheme.Modules.pullback
        (pullback.lift (A.X.hom ≫ unitSection A) (𝟙 A.X.left)
          (by simp [Category.assoc, unitSection_comp]))).obj D.obj ≅
        structureSheaf A.X.left) ∧
      ((LineBundle.pullback (pullback.diagonal A.X.hom)).obj D).IsAmple

end Langlands.AbelianScheme
