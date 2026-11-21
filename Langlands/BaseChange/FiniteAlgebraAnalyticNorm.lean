import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Topology.MetricSpace.Ultra.Pi
import Mathlib.Algebra.Algebra.Bilinear

/-! # An ultrametric algebra norm for finite algebras -/

noncomputable section

namespace Langlands.BaseChange

universe u v

section CompleteField

variable (F : Type u) [NontriviallyNormedField F] [CompleteSpace F]
  (R : Type v) [Ring R] [algebra : Algebra F R] [Module.Finite F R]

private abbrev Coordinates := Fin (Module.finrank F R) → F

private def regularRepresentation : R →ₐ[F] (Coordinates F R →L[F] Coordinates F R) :=
  let e := (Module.finBasis F R).equivFun
  ((e.conjAlgEquiv F).trans (Module.End.toContinuousLinearMap (Coordinates F R))).toAlgHom.comp
    (Algebra.lmul F R)

private theorem regularRepresentation_injective : Function.Injective (regularRepresentation F R) :=
  (Module.End.toContinuousLinearMap (Coordinates F R)).injective.comp
    (((Module.finBasis F R).equivFun.conjAlgEquiv F).injective.comp Algebra.lmul_injective)

@[instance_reducible]
private def operatorNormedRing : NormedRing R :=
  NormedRing.induced R _ (regularRepresentation F R) (regularRepresentation_injective F R)

private theorem operatorNormedRing_moduleTopology :
    let := operatorNormedRing F R
    IsModuleTopology F R := by
  let := operatorNormedRing F R
  let : NormedAlgebra F R := NormedAlgebra.induced F R _ (regularRepresentation F R)
  exact isModuleTopologyOfFiniteDimensional

variable [TopologicalSpace R] [IsModuleTopology F R]

/-- The operator norm of left multiplication in finite coordinates, with the supplied
module topology as its topology. -/
@[instance_reducible]
def finiteAlgebraNormedRing : NormedRing R :=
  let r := operatorNormedRing F R
  let h := (eq_moduleTopology F R).trans
    (@eq_moduleTopology F _ R _ _ r.toMetricSpace.toUniformSpace.toTopologicalSpace
      (operatorNormedRing_moduleTopology F R)).symm
  { r with toMetricSpace := r.toMetricSpace.replaceTopology h }

/-- The finite algebra norm is compatible with scalar multiplication. -/
@[instance_reducible]
def finiteAlgebraNormedAlgebra :
    letI := finiteAlgebraNormedRing F R
    NormedAlgebra F R := by
  letI := finiteAlgebraNormedRing F R
  refine { toAlgebra := algebra, norm_smul_le := ?_ }
  intro a b
  change ‖regularRepresentation F R (a • b)‖ ≤ ‖a‖ * ‖regularRepresentation F R b‖
  rw [map_smul]
  exact norm_smul_le a (regularRepresentation F R b)

omit [CompleteSpace F] [Module.Finite F R] [TopologicalSpace R] [IsModuleTopology F R] in
private theorem opNorm_add_le_max [IsUltrametricDist F] {ι : Type*} [Fintype ι]
    (f g : (ι → F) →L[F] (ι → F)) :
    ‖f + g‖ ≤ max ‖f‖ ‖g‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ ((norm_nonneg f).trans (le_max_left _ _))
  intro x
  refine (IsUltrametricDist.norm_add_le_max (f x) (g x)).trans (max_le ?_ ?_)
  · exact (f.le_opNorm x).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg x))
  · exact (g.le_opNorm x).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg x))

/-- The finite algebra norm is ultrametric over an ultrametric field. -/
theorem finiteAlgebraNormedRing_ultrametric [IsUltrametricDist F] :
    let := finiteAlgebraNormedRing F R
    IsUltrametricDist R := by
  let := finiteAlgebraNormedRing F R
  apply IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm
  intro x y
  change ‖regularRepresentation F R (x + y)‖ ≤
    max ‖regularRepresentation F R x‖ ‖regularRepresentation F R y‖
  rw [map_add]
  exact opNorm_add_le_max F _ _

end CompleteField

end Langlands.BaseChange
