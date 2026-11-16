import Langlands.AlgebraicGeometry.Picard.Rosati
import Langlands.AlgebraicGeometry.Picard.MixedLineBundleEuler
import Langlands.AlgebraicGeometry.Picard.LineBundlePullback
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! # The actual Mumford Rosati trace formula in Euler coefficients -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AbelianScheme.Rosati

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules

/-- The geometric Rosati diagonal trace formula for an actual ample Mumford
presentation, expressed using canonical coherent Euler coefficients.
This is an unproved geometric comparison target. -/
def MumfordMixedEulerTraceStatement : Prop :=
  ∀ (P : Prerequisites.{u})
    (k : Type u) [Field k] [IsAlgClosed k] [CharZero k]
    (A : AbelianScheme (Scheme.Spec.obj (Opposite.op (CommRingCat.of k))))
    (W : DualData A) (hadd : W.Additivity P) (lam : A ⟶ W.dual P)
    [HasRationalInverse P W lam]
    (g : ℕ), 0 < g → A.HasRelativeDimension g →
    ∀ (L : LineBundle A.X.left)
      (B : LineBundle (Scheme.Spec.obj (Opposite.op (CommRingCat.of k))))
      (evaluationB : tensorObj ((Scheme.Modules.pullback (unitSection A)).obj L.obj)
        B.obj ≅ structureSheaf (Scheme.Spec.obj (Opposite.op (CommRingCat.of k))))
      (M : LineBundle A.X.left)
      (evaluation : tensorObj
        (LineBundle.normalize P.preservation A.X.hom (unitSection A)
          (unitSection_comp A) L B evaluationB).obj.carrier M.obj ≅
            structureSheaf A.X.left),
      L.IsAmple →
      (groupHom lam).hom.hom =
        mumfordSchemeMapOfLineBundle P.preservation A L B evaluationB M evaluation
          P.square W.hasDual →
      ∀ (f : A ⟶ A),
        traceForm P W hadd lam (homToHom0 f) (homToHom0 f) *
            (lineBundleEulerPolynomial A.X.hom L g).coeff g =
          2 * mixedLineBundleEulerCoefficient A.X.hom L
            ((LineBundle.pullback (hom f)).obj L) g

end Langlands.AbelianScheme.Rosati
