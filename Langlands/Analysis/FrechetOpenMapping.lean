import Mathlib.Analysis.LocallyConvex.AbsConvex
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.IsUniformGroup.Basic
import Mathlib.Topology.Baire.CompleteMetrizable

/-! # The open mapping theorem for Fréchet spaces -/

noncomputable section

open Filter Set
open scoped Topology Uniformity Pointwise

set_option autoImplicit false

namespace Langlands.Analysis

universe uE uF

/-- A continuous surjective real-linear map from a complete first-countable locally convex
space to a Hausdorff first-countable Baire topological vector space is open. -/
def FrechetOpenMappingStatement : Prop :=
  ∀ (E : Type uE) (F : Type uF) [AddCommGroup E] [AddCommGroup F] [Module ℝ E] [Module ℝ F]
    [UniformSpace E] [IsUniformAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]
    [FirstCountableTopology E] [CompleteSpace E]
    [TopologicalSpace F] [IsTopologicalAddGroup F] [ContinuousSMul ℝ F]
    [FirstCountableTopology F] [T2Space F] [BaireSpace F]
    (Q : E →L[ℝ] F), Function.Surjective Q → IsOpenMap Q

section Proof

variable {E : Type uE} {F : Type uF} [AddCommGroup E] [AddCommGroup F] [Module ℝ E] [Module ℝ F]
  [UniformSpace E] [IsUniformAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]
  [FirstCountableTopology E] [CompleteSpace E]
  [TopologicalSpace F] [IsTopologicalAddGroup F] [ContinuousSMul ℝ F]
  [FirstCountableTopology F] [T2Space F] [BaireSpace F]

omit [FirstCountableTopology E] [CompleteSpace E] [FirstCountableTopology F] [T2Space F] in
private theorem closure_image_mem_nhds_zero (Q : E →L[ℝ] F) (hQ : Function.Surjective Q)
    {U : Set E} (hU : U ∈ 𝓝 0) : closure (Q '' U) ∈ 𝓝 (0 : F) := by
  obtain ⟨V₀, hV₀, hVV₀⟩ := exists_nhds_zero_half hU
  obtain ⟨V, ⟨hV, hVbal, _⟩, hV'⟩ := (nhds_hasBasis_absConvex ℝ E).mem_iff.mp hV₀
  let B := closure (Q '' V)
  let c (n : ℕ) := (1 / 2 : ℝ) ^ n
  have hc : Tendsto c atTop (𝓝 0) := tendsto_pow_atTop_nhds_zero_of_norm_lt_one (by norm_num)
  have c_ne_zero (n : ℕ) : c n ≠ 0 := by dsimp [c]; positivity
  let A (n : ℕ) := (fun y : F => c n • y) ⁻¹' B
  have hcover : (⋃ n, A n) = univ := by
    refine eq_univ_of_forall fun y => ?_
    obtain ⟨x, rfl⟩ := hQ y
    obtain ⟨n, hn⟩ := ((hc.zero_smul_const x).eventually_mem hV).exists
    refine mem_iUnion.mpr ⟨n, ?_⟩
    change c n • Q x ∈ closure (Q '' V)
    rw [← map_smul]
    exact subset_closure ⟨_, hn, rfl⟩
  obtain ⟨n, y, hy⟩ := nonempty_interior_of_iUnion_of_closed
    (fun n => isClosed_closure.preimage (continuous_const_smul (c n))) hcover
  let W := (fun z : F => c n • z) '' interior (A n)
  have hW : IsOpen W := (isOpenMap_smul₀ (c_ne_zero n)) _ isOpen_interior
  have hWB : W ⊆ B := by
    rintro _ ⟨z, hz, rfl⟩
    have hz' : z ∈ A n := interior_subset hz
    exact hz'
  let w : F := c n • y
  have hw : w ∈ W := ⟨y, hy, rfl⟩
  have h0 : (fun z : F => z + w) ⁻¹' W ∈ 𝓝 (0 : F) :=
    (hW.preimage (continuous_id.add continuous_const)).mem_nhds (by simpa using hw)
  apply mem_of_superset h0
  intro z hz
  have hzB : z + w ∈ B := hWB hz
  have hwB : w ∈ B := hWB hw
  have hpair : (z + w, w) ∈ closure ((Q '' V) ×ˢ (Q '' V)) := by
    rw [closure_prod_eq]
    exact ⟨hzB, hwB⟩
  have hsub := mem_closure_image (f := fun p : F × F => p.1 - p.2)
    (continuous_fst.sub continuous_snd).continuousAt hpair
  rw [add_sub_cancel_right] at hsub
  refine closure_mono ?_ hsub
  rintro _ ⟨⟨_, _⟩, ⟨⟨v, hv, rfl⟩, ⟨v', hv', rfl⟩⟩, rfl⟩
  refine ⟨v - v', ?_, map_sub Q v v'⟩
  have hv'neg : -v' ∈ V := by
    simpa using hVbal.smul_mem (a := (-1 : ℝ)) (by norm_num) hv'
  simpa only [sub_eq_add_neg] using hVV₀ v (hV' hv) (-v') (hV' hv'neg)

omit [Module ℝ E] [UniformSpace E] [IsUniformAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]
  [FirstCountableTopology E] [CompleteSpace E] [ContinuousSMul ℝ F]
  [FirstCountableTopology F] [T2Space F] [BaireSpace F] in
private theorem difference_mem_of_successive {U : ℕ → Set E} (h0 : ∀ n, 0 ∈ U n)
    (hU : ∀ n, U (n + 1) + U (n + 1) ⊆ U n) {x : ℕ → E}
    (hx : ∀ n, x (n + 1) - x n ∈ U (n + 1)) (n m : ℕ) (hnm : n ≤ m) :
    x m - x n ∈ U n := by
  exact Nat.decreasingInduction'
    (fun k _ _ ih => hU k ⟨_, ih, _, hx k, sub_add_sub_cancel _ _ _⟩) hnm
    (by simpa only [sub_self] using h0 m)

private theorem image_mem_nhds_zero (Q : E →L[ℝ] F) (hQ : Function.Surjective Q)
    {O : Set E} (hO : O ∈ 𝓝 0) : Q '' O ∈ 𝓝 (0 : F) := by
  classical
  obtain ⟨U, hU, hUprops⟩ := exists_nhds_hasAntitoneBasis_absConvex_open_add_closure_subset
    (𝕜 := ℝ) (E := E)
  obtain ⟨i, hi⟩ := hU.mem_iff.mp hO
  obtain ⟨V, hV, _⟩ := IsTopologicalAddGroup.exists_antitone_basis_nhds_zero F
  let W (n : ℕ) := V n ∩ closure (Q '' U (i + 1 + (n + 1)))
  have hW (n : ℕ) : W n ∈ 𝓝 (0 : F) :=
    inter_mem (hV.mem_of_mem trivial) (closure_image_mem_nhds_zero Q hQ (hU.mem_of_mem trivial))
  apply mem_of_superset (hW 0)
  intro y hy
  let L (n : ℕ) := {x : E // y - Q x ∈ W n}
  have hLift (n : ℕ) (x : L n) : ∃ z : L (n + 1),
      z.val - x.val ∈ U (i + 1 + (n + 1)) := by
    let r := y - Q x.val
    have hr : r ∈ closure (Q '' U (i + 1 + (n + 1))) := x.prop.2
    have hV' : (fun q : F => r - q) ⁻¹' W (n + 1) ∈ 𝓝 r := by
      have hc : Continuous (fun q : F => r - q) := continuous_const.sub continuous_id
      have hw : W (n + 1) ∈ 𝓝 (r - r) := by rw [sub_self]; exact hW (n + 1)
      exact hc.continuousAt.preimage_mem_nhds hw
    obtain ⟨_, hnew, z, hz, rfl⟩ := mem_closure_iff_nhds.mp hr _ hV'
    have hxz : y - Q (x.val + z) ∈ W (n + 1) := by
      rwa [map_add, ← sub_sub]
    exact ⟨⟨x.val + z, hxz⟩, by simpa only [add_sub_cancel_left] using hz⟩
  let x : ∀ n, L n :=
    Nat.rec ⟨0, by simpa only [map_zero, sub_zero] using hy⟩ (fun n x => (hLift n x).choose)
  have hx (n : ℕ) : (x (n + 1)).val - (x n).val ∈ U (i + 1 + (n + 1)) :=
    (hLift n (x n)).choose_spec
  have htails (a b : ℕ) (hab : a ≤ b) : (x b).val - (x a).val ∈ U (i + 1 + a) := by
    apply difference_mem_of_successive (U := fun n => U (i + 1 + n))
      (fun n => mem_of_mem_nhds (hU.mem_of_mem trivial)) _ hx a b hab
    intro n
    exact (hUprops (i + 1 + n)).2.2.1
  have h𝓤 : (𝓤 E).HasBasis (fun _ : ℕ => True) fun j =>
      (fun p : E × E => p.1 - p.2) ⁻¹' U j := by
    rw [uniformity_eq_comap_nhds_zero_swapped]
    exact hU.toHasBasis.comap _
  have hcauchy : CauchySeq (fun n => (x n).val) := by
    apply h𝓤.cauchySeq_iff'.mpr
    intro j _
    exact ⟨j, fun m hm => hU.antitone (by omega) (htails j m hm)⟩
  obtain ⟨z, hz⟩ := cauchySeq_tendsto_of_complete hcauchy
  have hzs : z ∈ closure (U (i + 1)) := isClosed_closure.mem_of_tendsto hz
    (Eventually.of_forall fun n => subset_closure (by
      have h := htails 0 n (Nat.zero_le n)
      change (x n).val - 0 ∈ U (i + 1) at h
      simpa only [sub_zero] using h))
  have hzO : z ∈ O := hi ((hUprops i).2.2.2 hzs)
  have hres : Tendsto (fun n => y - Q (x n).val) atTop (𝓝 0) := by
    apply (atTop_basis.tendsto_iff hV.toHasBasis).mpr
    intro j _
    exact ⟨j, trivial, fun n hn => hV.antitone hn (x n).prop.1⟩
  have hlim : y - Q z = 0 := tendsto_nhds_unique
    (tendsto_const_nhds.sub ((Q.continuous.tendsto z).comp hz)) hres
  exact ⟨z, hzO, (sub_eq_zero.mp hlim).symm⟩

end Proof

/-- Baire's theorem supplies neighborhoods in the closures of images. Successive
approximations and completeness give actual lifts into any prescribed neighborhood. -/
theorem frechetOpenMapping : FrechetOpenMappingStatement.{uE, uF} := by
  intro E F _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Q hQ
  rw [isOpenMap_iff_nhds_le]
  intro x
  rw [le_map_iff]
  intro O hO
  have hU : (fun z : E => x + z) ⁻¹' O ∈ 𝓝 (0 : E) :=
    (continuous_const.add continuous_id).continuousAt.preimage_mem_nhds (by simpa using hO)
  have hV := image_mem_nhds_zero Q hQ hU
  have hW : (fun y : F => y - Q x) ⁻¹' (Q '' ((fun z : E => x + z) ⁻¹' O)) ∈ 𝓝 (Q x) :=
    (continuous_id.sub continuous_const).continuousAt.preimage_mem_nhds (by simpa using hV)
  apply mem_of_superset hW
  intro y hy
  obtain ⟨z, hz, hzQ⟩ := hy
  change Q z = y - Q x at hzQ
  exact ⟨x + z, hz, by rw [map_add, hzQ, add_sub_cancel]⟩

end Langlands.Analysis
