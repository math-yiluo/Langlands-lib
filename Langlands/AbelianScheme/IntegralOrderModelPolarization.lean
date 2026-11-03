import Langlands.AbelianScheme.IntegralOrderModelPolarizationComparison
import Langlands.AlgebraicGeometry.Picard.DualIntegralInverse
import Langlands.AlgebraicGeometry.Picard.DualPullbackPolarization

/-! # Geometric polarizations on the actual integral order model -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry Module
open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AbelianScheme.IntegralOrderModel

variable {S : Scheme.{u}} {A : AbelianScheme S}
  {R : Type v} [Ring R] [Algebra ℚ R]
  {O : Subalgebra ℤ R}
  (α : R →ₐ[ℚ] End0 A)
  (M : IntegralOrderModel (IntegralOrderExtension.restrict (O := O) α))

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
local notation "modelPullback" => dualPullbackHom α M preservation composition unitCoherence
  associativity comparison symmetry stability hA hB geometryA geometryB MA evaluationA
  MB evaluationB

variable (square : MumfordBundlePicardZeroStatement.{u})
  (universality : PicardZeroUniversalBaseChangeStatement.{u})
  (additivityAA : DualSchemeMapAdditivity preservation stability A A hA hA)
  (additivityBB : DualSchemeMapAdditivity preservation stability M.B M.B hB hB)

include additivityAA additivityBB in
/-- The model's actual dual pullback is a relative polarization when the common integer is
invertible; its positivity is already part of the supplied integral order model. -/
theorem dualPullback_isPolarization
    (hn : IsUnit (M.inverseData.multiple : Γ(S, ⊤))) (lamA : A ⟶ DA)
    (hlam : IsPolarization preservation square universality A hA geometryA MA evaluationA
      stability composition unitCoherence associativity comparison symmetry lamA) :
    IsPolarization preservation square universality M.B hB geometryB MB evaluationB stability
      composition unitCoherence associativity comparison symmetry (modelPullback lamA) := by
  have hmaps := integralInverseData_finiteEtaleIsogenies M.inverseData M.multiple_pos hn
  have hduals := dualIntegralInverseData_finiteEtaleIsogenies preservation composition
    unitCoherence associativity comparison symmetry stability hA hB geometryA geometryB
    MA evaluationA MB evaluationB additivityAA additivityBB M.inverseData M.multiple_pos hn
  exact isPolarization_integralDualPullbackHom preservation square universality composition
    unitCoherence associativity comparison symmetry stability hB hA geometryB geometryA
    MB evaluationB MA evaluationA M.inverseData.inv hmaps.2.2.1 hduals.1 lamA hlam

include additivityAA additivityBB in
/-- Over a characteristic-zero field scheme, invertibility of the model's common integer
follows from its nonzero value, so the actual dual pullback is a polarization. -/
theorem dualPullback_isPolarization_overField
    {K : Type u} [Field K] [CharZero K] (p : S ⟶ Spec (.of K)) (lamA : A ⟶ DA)
    (hlam : IsPolarization preservation square universality A hA geometryA MA evaluationA
      stability composition unitCoherence associativity comparison symmetry lamA) :
    IsPolarization preservation square universality M.B hB geometryB MB evaluationB stability
      composition unitCoherence associativity comparison symmetry (modelPullback lamA) := by
  have hnK : IsUnit (M.inverseData.multiple : K) :=
    isUnit_iff_ne_zero.mpr (Int.cast_ne_zero.mpr M.inverseData.multiple_ne_zero)
  have hnS : IsUnit (M.inverseData.multiple : Γ(S, ⊤)) := by
    simpa only [map_intCast] using hnK.map ((Scheme.ΓSpecIso (.of K)).inv ≫ p.appTop).hom
  exact dualPullback_isPolarization α M preservation composition unitCoherence associativity
    comparison symmetry stability hA hB geometryA geometryB MA evaluationA MB evaluationB
    square universality additivityAA additivityBB hnS lamA hlam

/-- Bundle the unchanged actual model pullback with its geometric polarization proof over a
characteristic-zero field scheme. -/
def polarizationOverField
    {K : Type u} [Field K] [CharZero K] (p : S ⟶ Spec (.of K)) (lamA : A ⟶ DA)
    (hlam : IsPolarization preservation square universality A hA geometryA MA evaluationA
      stability composition unitCoherence associativity comparison symmetry lamA) :
    {lam : M.B ⟶ DB // IsPolarization preservation square universality M.B hB geometryB MB
      evaluationB stability composition unitCoherence associativity comparison symmetry lam} :=
  ⟨modelPullback lamA, dualPullback_isPolarization_overField α M preservation composition
    unitCoherence associativity comparison symmetry stability hA hB geometryA geometryB
    MA evaluationA MB evaluationB square universality additivityAA additivityBB p lamA hlam⟩

end Langlands.AbelianScheme.IntegralOrderModel
