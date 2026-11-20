import Langlands.HarmonicAnalysis.Distribution.FlatProductJets
import Langlands.HarmonicAnalysis.Distribution.ProductJetExtension

/-! # The finite transverse jet formula on a fixed compact support -/

noncomputable section

open Filter Set TopologicalSpace
open scoped ContDiff Distributions Topology

set_option autoImplicit false

namespace Langlands.HarmonicAnalysis

variable {E W F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {U : Opens E} {V : Opens W}

theorem tsupport_transverseProductJetCLM_subset (i : ℕ)
    (f : 𝓓(productTestDomain U V, F)) :
    tsupport (transverseProductJetCLM i f) ⊆ (fun x : E => (x, (0 : W))) ⁻¹' tsupport f := by
  refine closure_minimal ?_ ((isClosed_tsupport f).preimage (continuous_id.prodMk continuous_const))
  intro x hx
  by_contra hz
  have hD : iteratedFDeriv ℝ i f (x, 0) = 0 :=
    Function.notMem_support.mp fun h => hz (support_iteratedFDeriv_subset (𝕜 := ℝ) i h)
  apply hx
  ext v
  rw [transverseProductJetCLM_apply, hD]
  rfl

theorem tsupport_productJetExtensionCLM_subset (χ : 𝓓(V, ℝ)) (i : ℕ)
    (a : 𝓓(U, W [×i]→L[ℝ] F)) :
    tsupport (productJetExtensionCLM χ i a) ⊆ tsupport a ×ˢ tsupport χ := by
  refine closure_minimal ?_ ((isClosed_tsupport a).prod (isClosed_tsupport χ))
  rintro ⟨x, y⟩ hz
  change productJetExtensionCLM χ i a (x, y) ≠ 0 at hz
  rw [productJetExtensionCLM_apply] at hz
  refine ⟨subset_tsupport (⇑a) ?_, subset_tsupport (⇑χ) ?_⟩
  · exact fun ha => hz (by simp [ha])
  · exact fun hχ => hz (by simp [hχ])

/-- The continuous functional on order-`i` multilinear coefficient tests obtained
by extending them and evaluating the original distribution. -/
def transverseProductJetCoefficient (T : 𝓓'(productTestDomain U V, F)) (χ : 𝓓(V, ℝ))
    (i : ℕ) : 𝓓(U, W [×i]→L[ℝ] ℝ) →L[ℝ] F :=
  T.comp (productJetExtensionCLM χ i)

@[simp]
theorem transverseProductJetCoefficient_apply (T : 𝓓'(productTestDomain U V, F)) (χ : 𝓓(V, ℝ))
    (i : ℕ) (a : 𝓓(U, W [×i]→L[ℝ] ℝ)) :
    transverseProductJetCoefficient T χ i a = T (productJetExtensionCLM χ i a) := rfl

/-- A distribution supported on the zero section is the sum of its coefficient
functionals applied to the transverse derivatives through the order on a fixed compact product. -/
theorem distribution_eval_sum_transverseProductJets [FiniteDimensional ℝ W]
    (T : 𝓓'(productTestDomain U V, F))
    (hT : Distribution.IsVanishingOn T {z : E × W | z.2 ≠ 0})
    {K : Compacts E} {L : Compacts W}
    (hKL : (↑(K ×ˢ L) : Set (E × W)) ⊆ productTestDomain U V)
    (χ : 𝓓(V, ℝ)) (hχ : (χ : W → ℝ) =ᶠ[𝓝 0] 1) (hχL : tsupport χ ⊆ L)
    (f : 𝓓_{K ×ˢ L}(E × W, ℝ)) :
    T (TestFunction.ofSupportedIn hKL f) =
      ∑ i ∈ Finset.range (smoothDistributionCompactOrder T hKL + 1),
        transverseProductJetCoefficient T χ i
          (transverseProductJetCLM i (TestFunction.ofSupportedIn hKL f)) := by
  let m := smoothDistributionCompactOrder T hKL
  let f' := TestFunction.ofSupportedIn hKL f
  let J (i : ℕ) := transverseProductJetCLM i f'
  let e (i : ℕ) := productJetExtensionCLM χ i (J i)
  let g := ∑ i ∈ Finset.range (m + 1), e i
  let r := f' - g
  have hJ (i : ℕ) : tsupport (J i) ⊆ K :=
    fun _ hx => (f.tsupport_subset (tsupport_transverseProductJetCLM_subset i f' hx)).1
  have he (i : ℕ) : tsupport (e i) ⊆ (↑(K ×ˢ L) : Set (E × W)) :=
    (tsupport_productJetExtensionCLM_subset χ i (J i)).trans
      (Set.prod_mono (hJ i) hχL)
  have hgs (z : E × W) (hz : z ∉ K ×ˢ L) : g z = 0 := by
    change (FunLike.coeAddMonoidHom 𝓓(productTestDomain U V, ℝ) (E × W) ℝ
      (∑ i ∈ Finset.range (m + 1), e i)) z = 0
    rw [map_sum, Finset.sum_apply]
    exact Finset.sum_eq_zero fun i _ =>
      Function.notMem_support.mp fun h => hz (he i (subset_tsupport (⇑(e i)) h))
  have hr : Function.support r ⊆ (↑(K ×ˢ L) : Set (E × W)) := by
    intro z h
    by_contra hz
    apply h
    change f z - g z = 0
    rw [show f z = 0 from f.zero_on_compl hz, hgs z hz, sub_zero]
  let rest : 𝓓_{K ×ˢ L}(E × W, ℝ) := ContDiffMapSupportedIn.of_support_subset r.contDiff hr
  have hrest : TestFunction.ofSupportedIn hKL rest = r := by ext z; rfl
  have hjet (i : ℕ) (hi : i ≤ m) : transverseProductJetCLM i r = 0 := by
    have hi' : i ∈ Finset.range (m + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hi)
    change transverseProductJetCLM i (f' - ∑ j ∈ Finset.range (m + 1), e j) = 0
    rw [map_sub, sub_eq_zero, map_sum, Finset.sum_eq_single_of_mem i hi']
    · exact (transverseProductJetCLM_productJetExtensionCLM_self χ hχ i (J i)
        (transverseProductJetCLM_comp_perm i f')).symm
    · intro j _ hji
      exact transverseProductJetCLM_productJetExtensionCLM_of_ne χ hχ hji (J j)
  have hzero := distribution_eq_zero_of_transverseProductJet T hT hKL rest (by
    intro x i hi v
    change iteratedFDeriv ℝ i (TestFunction.ofSupportedIn hKL rest) (x, 0)
      (fun k => (0, v k)) = 0
    rw [← transverseProductJetCLM_apply, hrest, hjet i hi]
    rfl)
  rw [hrest] at hzero
  simpa only [r, g, e, J, f', m, map_sub, sub_eq_zero, map_sum,
    transverseProductJetCoefficient_apply] using hzero

end Langlands.HarmonicAnalysis
