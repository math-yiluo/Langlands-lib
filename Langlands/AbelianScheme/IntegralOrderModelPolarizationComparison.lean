import Langlands.AbelianScheme.IntegralOrderModelComparison
import Langlands.AlgebraicGeometry.Picard.IntegralDualPullback

/-! # Dual-valued maps on the actual integral order model -/

noncomputable section

universe u v w

open CategoryTheory AlgebraicGeometry Module
open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules
open scoped TensorProduct

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.AbelianScheme.IntegralOrderModel

variable {S : Scheme.{u}} {A : AbelianScheme S}
  {R : Type v} [Ring R] [Algebra ℚ R]
  {O : Subalgebra ℤ R} [Submodule.IsLattice ℚ O.toSubmodule]
  {I : Type w} (b : Basis I ℤ O) (α : R →ₐ[ℚ] End0 A)
  (M : IntegralOrderModel (IntegralOrderExtension.restrict (O := O) α))

local notation "β" => integralActionRationalExtension M.B b M.action

/-- The actual reverse map intertwines the entire rational algebra action. -/
theorem rationalExtension_inv_intertwines (x : R) :
    comp0 M.B M.B A (β x) (homToHom0 M.inverseData.inv) =
      comp0 M.B A A (homToHom0 M.inverseData.inv) (α x) := by
  have hn : (M.inverseData.multiple : ℚ) ≠ 0 :=
    Int.cast_ne_zero.mpr M.inverseData.multiple_ne_zero
  have h := RationalAlgebraAction.intertwines (rationalAlgebraIso b α M).inv x
  change comp0 M.B M.B A (β x)
      ((M.inverseData.multiple : ℚ)⁻¹ • homToHom0 M.inverseData.inv) =
    comp0 M.B A A
      ((M.inverseData.multiple : ℚ)⁻¹ • homToHom0 M.inverseData.inv) (α x) at h
  have h' := congrArg (fun t : Hom0 M.B A => (M.inverseData.multiple : ℚ) • t) h
  simpa only [map_smul, LinearMap.smul_apply, smul_smul, mul_inv_cancel₀ hn, one_smul]
    using h'

/-- Faithfulness is retained for every element of the original rational algebra. -/
theorem rationalExtension_injective_iff :
    Function.Injective β ↔ Function.Injective α :=
  (RationalAlgebraAction.action_injective_iff (rationalAlgebraIso b α M)).symm

variable (preservation : pullbackTensorComparisonIsIsoStatement.{u})
  (composition : PullbackTensorCompositionStatement.{u})
  (unitCoherence : PullbackTensorUnitCoherenceStatement.{u})
  (associativity : ExplicitPullbackTensorAssociativityStatement.{u})
  (comparison : TensorMonoidalLeftUnitorComparisonStatement.{u})
  (symmetry : PullbackTensorSymmetryStatement.{u})
  (stability : PicardZeroPullbackStatement.{u})
  (hA : HasDualScheme A) (hB : HasDualScheme M.B)
  (geometryA : DualSchemeGeometry A hA) (geometryB : DualSchemeGeometry M.B hB)
  (MA : LineBundle ((relativeSpace A.X.hom).obj (dualScheme A hA)))
  (evaluationA : tensorObj (poincareFamily A hA).obj.carrier MA.obj ≅
    structureSheaf ((relativeSpace A.X.hom).obj (dualScheme A hA)))
  (MB : LineBundle ((relativeSpace M.B.X.hom).obj (dualScheme M.B hB)))
  (evaluationB : tensorObj (poincareFamily M.B hB).obj.carrier MB.obj ≅
    structureSheaf ((relativeSpace M.B.X.hom).obj (dualScheme M.B hB)))

local notation "DA" => dualAbelianSchemeFromEvaluation A hA geometryA preservation MA
  evaluationA stability composition unitCoherence associativity comparison symmetry
local notation "DB" => dualAbelianSchemeFromEvaluation M.B hB geometryB preservation MB
  evaluationB stability composition unitCoherence associativity comparison symmetry
/-- Pull back the original integral dual-valued map along the model's actual reverse map. -/
def dualPullbackHom (lamA : A ⟶ DA) : M.B ⟶ DB :=
  integralDualPullbackHom preservation composition unitCoherence associativity comparison
    symmetry stability hB hA geometryB geometryA MB evaluationB MA evaluationA
    M.inverseData.inv lamA

local notation "modelPullback" => dualPullbackHom α M preservation composition unitCoherence
  associativity comparison symmetry stability hA hB geometryA geometryB MA evaluationA
  MB evaluationB

omit [Submodule.IsLattice ℚ O.toSubmodule] in
/-- The square of the exact inverse-multiple integer is a positive rational multiplier. -/
theorem dualPullback_multiple_pos : 0 < (M.inverseData.multiple : ℚ) ^ 2 :=
  sq_pos_of_ne_zero (Int.cast_ne_zero.mpr M.inverseData.multiple_ne_zero)

variable (additivityAA : DualSchemeMapAdditivity preservation stability A A hA hA)
  (additivityAB : DualSchemeMapAdditivity preservation stability A M.B hA hB)
  (additivityBA : DualSchemeMapAdditivity preservation stability M.B A hB hA)
  (additivityBB : DualSchemeMapAdditivity preservation stability M.B M.B hB hB)

include additivityAA additivityBA

omit [Submodule.IsLattice ℚ O.toSubmodule] in
/-- The forward comparison pulls the constructed integral map back to exactly N squared
times the original map. -/
theorem dualPullback_multiple (lamA : A ⟶ DA) :
    IsRationalDualPullbackMultiple preservation composition unitCoherence associativity
      comparison symmetry stability hA hB geometryA geometryB MA evaluationA MB evaluationB
      additivityAB ((M.inverseData.multiple : ℚ) ^ 2)
      (homToHom0 M.inverseData.hom) (homToHom0 lamA)
      (homToHom0 (modelPullback lamA)) :=
  integralInverseData_dualPullback_multiple preservation composition unitCoherence
    associativity comparison symmetry stability hA hB geometryA geometryB MA evaluationA
    MB evaluationB additivityAB additivityAA additivityBA M.inverseData lamA

/-- Involution compatibility of the original map transports to the constructed map
for the full rational extension of the integral model action. -/
theorem dualPullback_involutionCompatible [StarRing R] (lamA : A ⟶ DA)
    (hlam : IsInvolutionCompatible preservation composition unitCoherence associativity
      comparison symmetry stability hA additivityAA MA evaluationA geometryA
      α.toRingHom (homToHom0 lamA)) :
    IsInvolutionCompatible preservation composition unitCoherence associativity
      comparison symmetry stability hB additivityBB MB evaluationB geometryB
      (β).toRingHom (homToHom0 (modelPullback lamA)) := by
  change IsInvolutionCompatible preservation composition unitCoherence associativity
    comparison symmetry stability hB additivityBB MB evaluationB geometryB (β).toRingHom
    (homToHom0 (integralDualPullbackHom preservation composition unitCoherence
      associativity comparison symmetry stability hB hA geometryB geometryA MB evaluationB
      MA evaluationA M.inverseData.inv lamA))
  rw [← rationalDualPullbackHom0_homToHom0 preservation composition unitCoherence
    associativity comparison symmetry stability hB hA geometryB geometryA MB evaluationB
    MA evaluationA additivityBA]
  exact IsInvolutionCompatible.rationalDualPullback preservation composition unitCoherence
    associativity comparison symmetry stability hB hA geometryB geometryA MB evaluationB
    MA evaluationA additivityBA additivityBB additivityAA (β).toRingHom α.toRingHom
    (homToHom0 M.inverseData.inv) (rationalExtension_inv_intertwines b α M)
    (homToHom0 lamA) hlam

end Langlands.AbelianScheme.IntegralOrderModel
