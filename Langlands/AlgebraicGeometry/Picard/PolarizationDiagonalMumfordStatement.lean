import Langlands.AlgebraicGeometry.Picard.MumfordLineBundle
import Langlands.AlgebraicGeometry.Picard.RelativePolarization

/-! # The Mumford map of the diagonal Poincare pullback of a polarization -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

noncomputable section

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules Langlands.SchemeModule

/-- The diagonal of `A` into the parameter-first relative space `A ×_S A`. -/
def relativeDiagonal {S : Scheme.{u}} (A : AbelianScheme S) :
    A.X.left ⟶ (relativeSpace A.X.hom).obj A.X :=
  pullback.lift (𝟙 A.X.left) (𝟙 A.X.left) rfl

/-- The line bundle `(1, f)^* P` on `A`: the Poincare family pulled back along `f` in its
parameter variable, then restricted to the diagonal of `A ×_S A`. -/
def poincareDiagonalBundle {S : Scheme.{u}} (A : AbelianScheme S) (hA : HasDualScheme A)
    (f : A.X ⟶ dualScheme A hA) : LineBundle A.X.left :=
  (LineBundle.pullback (relativeDiagonal A)).obj
    ((RigidifiedLineBundle.forget _).obj
      ((RigidifiedLineBundle.relativePullback A.X.hom (unitSection A) (unitSection_comp A)
        f).obj (poincareFamily A hA)))

/-- For a relative polarization `lam`, the diagonal Poincare pullback `(1, lam)^* P` admits
unit-section normalization data, and its Mumford map is the scheme map of `2 • lam`.
This is a relative theorem target (GIT Proposition 6.10), not a proof. -/
def PolarizationDiagonalMumfordStatement : Prop :=
  ∀ (preservation : pullbackTensorComparisonIsIsoStatement.{u})
    (square : MumfordBundlePicardZeroStatement.{u})
    (universality : PicardZeroUniversalBaseChangeStatement.{u})
    (composition : PullbackTensorCompositionStatement.{u})
    (unitCoherence : PullbackTensorUnitCoherenceStatement.{u})
    (associativity : ExplicitPullbackTensorAssociativityStatement.{u})
    (comparison : TensorMonoidalLeftUnitorComparisonStatement.{u})
    (symmetry : PullbackTensorSymmetryStatement.{u})
    (stability : PicardZeroPullbackStatement.{u})
    (S : Scheme.{u}) [QuasiSeparatedSpace S] (A : AbelianScheme S)
    (hA : HasDualScheme A) (geometryA : DualSchemeGeometry A hA)
    (MA : LineBundle ((relativeSpace A.X.hom).obj (dualScheme A hA)))
    (evaluationA : tensorObj (poincareFamily A hA).obj.carrier MA.obj ≅
      structureSheaf ((relativeSpace A.X.hom).obj (dualScheme A hA)))
    (lam : A ⟶ dualAbelianSchemeFromEvaluation A hA geometryA preservation MA
      evaluationA stability composition unitCoherence associativity comparison symmetry),
      IsPolarization preservation square universality A hA geometryA MA evaluationA
        stability composition unitCoherence associativity comparison symmetry lam →
      ∃ (B : LineBundle S)
        (evaluationB : tensorObj ((Scheme.Modules.pullback (unitSection A)).obj
          (poincareDiagonalBundle A hA (groupHom lam).hom.hom).obj) B.obj ≅ structureSheaf S)
        (M : LineBundle A.X.left)
        (evaluation : tensorObj (LineBundle.normalize preservation A.X.hom (unitSection A)
          (unitSection_comp A) (poincareDiagonalBundle A hA (groupHom lam).hom.hom) B
            evaluationB).obj.carrier M.obj ≅ structureSheaf A.X.left),
        mumfordSchemeMapOfLineBundle preservation A
            (poincareDiagonalBundle A hA (groupHom lam).hom.hom) B evaluationB M evaluation
            square hA =
          (groupHom (2 • lam)).hom.hom

end Langlands.AbelianScheme
