import Langlands.Representation.Plancherel.RationalImageComplexExponential

/-! # Pointwise topologies on actual real and complex parameters -/

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Plancherel

universe u

private def additiveHomEvaluation (A K : Type*) [AddCommGroup A] [AddCommGroup K] :
    (A →+ K) →+ (A → K) where
  toFun f := f
  map_zero' := rfl
  map_add' _ _ := rfl

@[instance_reducible]
private def additiveHomPointwiseTopology (A K : Type*) [AddCommGroup A] [AddCommGroup K]
    [TopologicalSpace K] : TopologicalSpace (A →+ K) :=
  TopologicalSpace.induced (additiveHomEvaluation A K) inferInstance

private def additiveHomBasisCoordinates {A K : Type*} [AddCommGroup A] [Field K]
    {n : ℕ} (b : Module.Basis (Fin n) ℤ A) : (A →+ K) ≃ₗ[K] (Fin n → K) where
  toFun f i := f (b i)
  invFun c := ((b.constr K) c).toAddMonoidHom
  left_inv f := by
    apply AddMonoidHom.toIntLinearMap_injective
    exact (b.constr K).apply_symm_apply f.toIntLinearMap
  right_inv c := funext (b.constr_basis K c)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def additiveHomBasisContinuousCoordinates {A K : Type*} [AddCommGroup A]
    [NormedField K] {n : ℕ} (b : Module.Basis (Fin n) ℤ A) :
    letI := additiveHomPointwiseTopology A K
    (A →+ K) ≃L[K] (Fin n → K) := by
  letI := additiveHomPointwiseTopology A K
  refine
    { toLinearEquiv := additiveHomBasisCoordinates b
      continuous_toFun := ?_
      continuous_invFun := ?_ }
  · apply continuous_pi
    intro i
    exact (continuous_apply (b i)).comp continuous_induced_dom
  · apply continuous_induced_rng.mpr
    apply continuous_pi
    intro a
    change Continuous (fun c : Fin n → K => ((b.constr K) c) a)
    simp_rw [Module.Basis.constr_apply_fintype]
    exact continuous_finsetSum _ fun i _ => (continuous_apply i).const_smul (b.equivFun a i)

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
variable (G : GroupScheme (Spec (CommRingCat.of F)))

/-- The topology of pointwise convergence on the actual complex additive dual.
It is defined without choosing a basis or assuming connected reductivity. -/
@[instance_reducible]
def rationalImageComplexParameterTopology :
    TopologicalSpace (rationalImageComplexFunctionals G) :=
  additiveHomPointwiseTopology (Additive (rationalDiscreteValuationImage G)) ℂ

/-- The corresponding pointwise topology on the actual real additive dual. -/
@[instance_reducible]
def rationalImageRealParameterTopology :
    TopologicalSpace (rationalImageRealFunctionals G) :=
  additiveHomPointwiseTopology (Additive (rationalDiscreteValuationImage G)) ℝ

/-- Evaluation at the published actual image basis gives complex linear coordinates. -/
def rationalImageComplexParameterCoordinates (hG : GroupScheme.IsConnectedReductive G) :
    rationalImageComplexFunctionals G ≃ₗ[ℂ] (Fin (rationalImageRank G) → ℂ) :=
  additiveHomBasisCoordinates (rationalReductiveValuationBasis G hG)

/-- Evaluation at the same actual image basis gives real linear coordinates. -/
def rationalImageRealParameterCoordinates (hG : GroupScheme.IsConnectedReductive G) :
    rationalImageRealFunctionals G ≃ₗ[ℝ] (Fin (rationalImageRank G) → ℝ) :=
  additiveHomBasisCoordinates (rationalReductiveValuationBasis G hG)

/-- The pointwise complex parameter topology is exactly the finite-dimensional
coordinate topology for a connected reductive group. -/
def rationalImageComplexParameterContinuousCoordinates
    (hG : GroupScheme.IsConnectedReductive G) :
    letI := rationalImageComplexParameterTopology G
    rationalImageComplexFunctionals G ≃L[ℂ] (Fin (rationalImageRank G) → ℂ) :=
  additiveHomBasisContinuousCoordinates (rationalReductiveValuationBasis G hG)

/-- The same comparison for the actual real parameter space. -/
def rationalImageRealParameterContinuousCoordinates
    (hG : GroupScheme.IsConnectedReductive G) :
    letI := rationalImageRealParameterTopology G
    rationalImageRealFunctionals G ≃L[ℝ] (Fin (rationalImageRank G) → ℝ) :=
  additiveHomBasisContinuousCoordinates (rationalReductiveValuationBasis G hG)

section ComplexTopology

local instance rationalParameterTopologyComplex :
    TopologicalSpace (rationalImageComplexFunctionals G) :=
  rationalImageComplexParameterTopology G

theorem isTopologicalAddGroup_rationalImageComplexParameters :
    IsTopologicalAddGroup (rationalImageComplexFunctionals G) :=
  isTopologicalAddGroup_induced
    (additiveHomEvaluation (Additive (rationalDiscreteValuationImage G)) ℂ)

theorem continuous_rationalImageComplexParameter_eval
    (a : Additive (rationalDiscreteValuationImage G)) :
    Continuous (fun lam : rationalImageComplexFunctionals G => lam a) :=
  (continuous_apply a).comp continuous_induced_dom

/-- The complex exponential is continuous in its parameter for the pointwise
topology and the existing compact-open character topology. -/
theorem continuous_rationalImageComplexCharacter :
    Continuous (rationalImageComplexCharacter G) := by
  apply (ContinuousMonoidHom.isClosedEmbedding_coe
    (A := rationalDiscreteValuationImage G) (B := ℂˣ)).isInducing.continuous_iff.mpr
  apply continuous_pi
  intro a
  apply Units.isEmbedding_val₀.isInducing.continuous_iff.mpr
  change Continuous (fun lam : rationalImageComplexFunctionals G =>
    Complex.exp (-lam (Additive.ofMul a) *
      (Real.log (LocalField.residueCardinality F : ℝ) : ℂ)))
  exact Complex.continuous_exp.comp
    ((continuous_rationalImageComplexParameter_eval G (Additive.ofMul a)).neg.mul_const _)

end ComplexTopology

end Langlands.Plancherel
