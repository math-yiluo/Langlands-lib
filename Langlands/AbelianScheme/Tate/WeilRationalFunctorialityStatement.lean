import Langlands.AbelianScheme.Tate.WeilRational
import Langlands.AlgebraicGeometry.Picard.DualMapRational

/-! # Rational dual-homomorphism compatibility of the actual Weil pairing -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

noncomputable section

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules Langlands.SchemeModule

/-- Adjunction of the actual rational Tate maps of a rational homomorphism and
its constructed rational dual, with values in the unchanged actual Tate twist. -/
def RationalWeilFunctorialityStatement : Prop :=
  ∀ (preservation : pullbackTensorComparisonIsIsoStatement.{u})
    (composition : PullbackTensorCompositionStatement.{u})
    (unitCoherence : PullbackTensorUnitCoherenceStatement.{u})
    (associativity : ExplicitPullbackTensorAssociativityStatement.{u})
    (comparison : TensorMonoidalLeftUnitorComparisonStatement.{u})
    (symmetry : PullbackTensorSymmetryStatement.{u})
    (stability : PicardZeroPullbackStatement.{u})
    (compatibility : RelativeFiniteWeilTransitionStatement.{u})
    (S : Scheme.{u}) [QuasiSeparatedSpace S] (A B : AbelianScheme S)
    (hA : HasDualScheme A) (hB : HasDualScheme B)
    (geometryA : DualSchemeGeometry A hA) (geometryB : DualSchemeGeometry B hB)
    (MA : LineBundle ((relativeSpace A.X.hom).obj (dualScheme A hA)))
    (evaluationA : tensorObj (poincareFamily A hA).obj.carrier MA.obj ≅
      structureSheaf ((relativeSpace A.X.hom).obj (dualScheme A hA)))
    (MB : LineBundle ((relativeSpace B.X.hom).obj (dualScheme B hB)))
    (evaluationB : tensorObj (poincareFamily B hB).obj.carrier MB.obj ≅
      structureSheaf ((relativeSpace B.X.hom).obj (dualScheme B hB)))
    (additivity : DualSchemeMapAdditivity preservation stability A B hA hB)
    (T : Over S) (P : ℕ → Prop) (f : Hom0 A B),
    let DB := dualAbelianSchemeFromEvaluation B hB geometryB preservation MB
      evaluationB stability composition unitCoherence associativity comparison symmetry
    let df := dualHom0 preservation composition unitCoherence associativity comparison
      symmetry stability hA hB additivity MA evaluationA MB evaluationB geometryA geometryB f
    ∀ (x : Tate.Rational A T P) (y : Tate.Rational DB T P),
      rationalWeilBilinearMap preservation composition unitCoherence associativity
        comparison symmetry stability hB MB evaluationB compatibility T P
        (Tate.rationalHomMap T P f x) y =
      rationalWeilBilinearMap preservation composition unitCoherence associativity
        comparison symmetry stability hA MA evaluationA compatibility T P x
        (Tate.rationalHomMap T P df y)

end Langlands.AbelianScheme
