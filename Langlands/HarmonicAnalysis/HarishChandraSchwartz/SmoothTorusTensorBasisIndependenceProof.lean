import Langlands.HarmonicAnalysis.HarishChandraSchwartz.SmoothTorusTensorTopology

/-! # Independence of the finite coefficient basis -/

noncomputable section

open Langlands.Plancherel
open scoped TensorProduct

namespace Langlands.HarishChandraSchwartz

universe uJ uV uB uC

section

variable (J : Type uJ) [Fintype J] [DecidableEq J]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {B : Type uB} [Fintype B] [DecidableEq B]
  {C : Type uC} [Fintype C] [DecidableEq C]
  (b : Module.Basis B ℂ V) (c : Module.Basis C ℂ V)

omit [DecidableEq J] in
private theorem smoothTensorCoordinates_changeBasis
    (t : smoothFiniteTorusFunctions J ⊗[ℂ] V) (k : C) :
    smoothTensorCoordinates J c t k =
      ∑ i, c.coord k (b i) • smoothTensorCoordinates J b t i := by
  apply Subtype.ext
  funext z
  simpa only [AddSubmonoidClass.coe_finsetSum, Finset.sum_apply, Subalgebra.coe_smul,
    Pi.smul_apply, smoothTensorCoordinates_apply, Module.Basis.coord_apply, smul_eq_mul] using
    (c.sum_repr_mul_repr b (smoothTensorEvaluation J V t z) k).symm

private theorem smoothTensorFiniteProductTopology_le :
    smoothTensorFiniteProductTopology J b ≤ smoothTensorFiniteProductTopology J c := by
  let _ := smoothTorusFunctionTopology J
  have hSeminorms : WithSeminorms (smoothTorusSeminorm J) := ⟨rfl⟩
  let _ := hSeminorms.isTopologicalAddGroup
  let _ := hSeminorms.continuousSMul
  let _ := smoothTensorFiniteProductTopology J b
  have hb : Continuous (smoothTensorCoordinates J b) := continuous_induced_dom
  have hc : Continuous (smoothTensorCoordinates J c) := by
    apply continuous_pi
    intro k
    simp_rw [smoothTensorCoordinates_changeBasis J b c]
    exact continuous_finsetSum _ fun i _ =>
      ((continuous_apply i).comp hb).const_smul (c.coord k (b i))
  exact continuous_iff_le_induced.mp hc

end

/-- All finite coefficient bases induce the same topology on the smooth tensor. -/
theorem smoothTensorBasisIndependence (J : Type uJ) [Fintype J] [DecidableEq J]
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {B : Type uB} [Fintype B] [DecidableEq B] (b : Module.Basis B ℂ V)
    {C : Type uC} [Fintype C] [DecidableEq C] (c : Module.Basis C ℂ V) :
    SmoothTensorBasisIndependenceStatement J b c :=
  le_antisymm (smoothTensorFiniteProductTopology_le J b c)
    (smoothTensorFiniteProductTopology_le J c b)

end Langlands.HarishChandraSchwartz
