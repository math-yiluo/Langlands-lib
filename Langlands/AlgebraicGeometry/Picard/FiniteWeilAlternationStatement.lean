import Langlands.AlgebraicGeometry.Picard.FiniteWeilAlongHom

/-! # Alternation of the actual finite pairing of a relative polarization -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

noncomputable section

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules Langlands.SchemeModule
open Langlands.GroupScheme

/-- The actual finite pairing of a relative polarization is trivial on the diagonal.
This is a relative theorem target, not a proof of alternation. -/
def RelativeFiniteWeilAlternationStatement : Prop :=
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
      ∀ (n : ℕ), 0 < n →
        prod.lift (𝟙 _) (𝟙 _) ≫
          finiteWeilAlongHomPairing preservation composition unitCoherence associativity
            comparison symmetry stability hA geometryA MA evaluationA lam n =
        (1 : (kernelCommGroupScheme (multiplication A (n : ℤ))).X ⟶ (mu S n).X)

end Langlands.AbelianScheme
