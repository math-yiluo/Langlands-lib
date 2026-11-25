import Langlands.BaseChange.CyclicProductConvolution
import Langlands.HarmonicAnalysis.Basic

/-!
# Fibre integrals over the ordered product: Schwartz–Bruhat functions and unit tensors

For a group `G` with a measure `μ` and `Φ : (Fin (m + 1) → G) → ℂ`, the fibre integral
`splitFiberIntegral μ Φ y = ∫ Φ(w₀, …, w_{m-1}, (w₀ ⋯ w_{m-1})⁻¹ y) dμ^m(w)` of the module
`Langlands.BaseChange.CyclicProductConvolution` integrates `Φ` over the fibre of the ordered product
`x ↦ x₀ ⋯ x_m` above `y`; that module also proves that the twisted orbital integrals of `Φ ∘ κ` in
cyclic product coordinates are those of the fibre integral
(`cyclicProductOrbitalIntegral_eq_splitFiberIntegral`). This file proves that the fibre integral of
a Schwartz–Bruhat function is Schwartz–Bruhat, with support in a subgroup `K₀` when `Φ` has support
in `K₀^{m+1}`, and that the tensor of normalized indicators of a compact open subgroup `K` with a
function `ψ` that is left invariant under `K` has fibre integral `ψ`. See the paired Markdown.
-/

noncomputable section

namespace Langlands.BaseChange

open MeasureTheory _root_.Topology
open Langlands.QuotientIntegration Langlands.TraceFormula Langlands.HarmonicAnalysis

attribute [local instance high] leftQuotientMeasurableSpace
attribute [local instance] leftQuotient_borelSpace

universe u v

section FiberIntegral

variable {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] {m : ℕ}

/-- The fibre integral of a Schwartz–Bruhat function on `G^{m+1}` is a Schwartz–Bruhat function
on `G`. -/
theorem splitFiberIntegral_mem_schwartzBruhat [T2Space G] (μ : Measure G)
    (Φ : SchwartzBruhat (Fin (m + 1) → G)) :
    splitFiberIntegral μ Φ ∈ schwartzBruhatSubmodule G := by
  let K (p : G × (Fin m → G)) : ℂ := Φ (splitProductFiberChart m p)
  have hKl : IsLocallyConstant K :=
    Φ.locallyConstant.comp_continuous (splitProductFiberChart m).continuous
  have hKs : HasCompactSupport K := Φ.hasCompactSupport.comp_homeomorph (splitProductFiberChart m)
  let Y := Prod.snd '' tsupport K
  have hY : IsCompact Y := hKs.image continuous_snd
  have hzero (y : G) (w : Fin m → G) (hw : w ∉ Y) : K (y, w) = 0 := by
    by_contra hz
    exact hw ⟨(y, w), subset_tsupport K hz, rfl⟩
  refine ⟨?_, HasCompactSupport.of_support_subset_isCompact (hKs.image continuous_fst) ?_⟩
  · rw [IsLocallyConstant.iff_eventually_eq]
    intro y₀
    have hev : ∀ᶠ y in nhds y₀, ∀ w ∈ Y, K (y, w) = K (y₀, w) := by
      refine hY.eventually_forall_of_forall_eventually fun w _ => ?_
      have h1 := hKl.eventually_eq (y₀, w)
      have h2 := (hKl.comp_continuous (f := fun z : G × (Fin m → G) => (y₀, z.2))
        (by fun_prop)).eventually_eq (y₀, w)
      filter_upwards [h1, h2] with z hz1 hz2
      exact hz1.trans hz2.symm
    filter_upwards [hev] with y hy
    change (∫ w, K (y, w) ∂Measure.pi (fun _ : Fin m => μ)) =
      ∫ w, K (y₀, w) ∂Measure.pi (fun _ : Fin m => μ)
    congr 1
    funext w
    by_cases hw : w ∈ Y
    · exact hy w hw
    · rw [hzero y w hw, hzero y₀ w hw]
  · intro y hy
    by_contra h
    apply hy
    apply integral_eq_zero_of_ae
    exact Filter.Eventually.of_forall fun w => by
      change K (y, w) = 0
      by_contra hz
      exact h ⟨(y, w), subset_tsupport K hz, rfl⟩

omit [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] in
private theorem mem_of_forall_snoc_mem (K₀ : Subgroup G) (w : Fin m → G) (y : G)
    (h : ∀ i, @Fin.snoc m (fun _ => G) w ((List.ofFn w).prod⁻¹ * y) i ∈ K₀) : y ∈ K₀ := by
  have hw (i : Fin m) : w i ∈ K₀ := by simpa only [Fin.snoc_castSucc] using h i.castSucc
  have hlast : (List.ofFn w).prod⁻¹ * y ∈ K₀ := by simpa only [Fin.snoc_last] using h (Fin.last m)
  have hprod : (List.ofFn w).prod ∈ K₀ := by
    apply K₀.list_prod_mem
    intro a ha
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
    exact hw i
  simpa using K₀.mul_mem hprod hlast

/-- If `Φ` vanishes off `K₀^{m+1}` for a subgroup `K₀`, its fibre integral vanishes off `K₀`. -/
theorem support_splitFiberIntegral_subset (μ : Measure G) (K₀ : Subgroup G)
    (Φ : (Fin (m + 1) → G) → ℂ)
    (hΦ : Function.support Φ ⊆ Set.pi Set.univ fun _ => (K₀ : Set G)) :
    Function.support (splitFiberIntegral μ Φ) ⊆ K₀ := by
  intro y hy
  by_contra h
  apply hy
  apply integral_eq_zero_of_ae
  refine Filter.Eventually.of_forall fun w => ?_
  by_contra hz
  have hmem := hΦ hz
  rw [splitProductFiberChart_apply] at hmem
  exact h (mem_of_forall_snoc_mem K₀ w y fun i => hmem i (Set.mem_univ i))

/-- The tensor of `m` copies of the normalized indicator `μ(K)⁻¹ 1_K` (in the first `m`
coordinates) with `ψ` (in the last coordinate). -/
def splitUnitTensor (μ : Measure G) (K : Set G) (ψ : G → ℂ) (x : Fin (m + 1) → G) : ℂ :=
  (((μ K).toReal⁻¹ ^ m : ℝ) : ℂ) *
    (Set.pi Set.univ fun _ : Fin m => K).indicator (fun _ => (1 : ℂ)) (Fin.init x) *
      ψ (x (Fin.last m))

/-- The unit tensor of a compact open subgroup and a Schwartz–Bruhat function is a
Schwartz–Bruhat function on `G^{m+1}`. -/
theorem splitUnitTensor_mem_schwartzBruhat [T2Space G] (μ : Measure G) (K : Subgroup G)
    (hKo : IsOpen (K : Set G)) (hKc : IsCompact (K : Set G)) (ψ : SchwartzBruhat G) :
    splitUnitTensor (m := m) μ K ψ ∈ schwartzBruhatSubmodule (Fin (m + 1) → G) := by
  classical
  have hclopen : IsClopen (Set.pi Set.univ fun _ : Fin m => (K : Set G)) :=
    ⟨isClosed_set_pi fun _ _ => K.isClosed_of_isOpen hKo,
      isOpen_set_pi Set.finite_univ fun _ _ => hKo⟩
  have hind : IsLocallyConstant
      ((Set.pi Set.univ fun _ : Fin m => (K : Set G)).indicator (fun _ => (1 : ℂ))) := by
    rw [IsLocallyConstant.iff_isOpen_fiber]
    intro z
    by_cases h1 : z = 1
    · subst h1
      convert hclopen.isOpen using 1
      ext x
      by_cases hx : x ∈ Set.pi Set.univ fun _ : Fin m => (K : Set G) <;> simp [hx]
    · by_cases h0 : z = 0
      · subst h0
        convert hclopen.compl.isOpen using 1
        ext x
        by_cases hx : x ∈ Set.pi Set.univ fun _ : Fin m => (K : Set G) <;> simp [hx]
      · convert isOpen_empty
        ext x
        by_cases hx : x ∈ Set.pi Set.univ fun _ : Fin m => (K : Set G) <;>
          simp [hx, Ne.symm h1, Ne.symm h0]
  have hinit : Continuous (Fin.init : (Fin (m + 1) → G) → Fin m → G) :=
    continuous_pi fun i => continuous_apply i.castSucc
  refine ⟨?_, ?_⟩
  · have h1 := hind.comp_continuous hinit
    have h2 := ψ.locallyConstant.comp_continuous
      (continuous_apply (Fin.last m) : Continuous fun x : Fin (m + 1) → G => x (Fin.last m))
    exact ((IsLocallyConstant.const _).comp₂ h1 (· * ·)).comp₂ h2 (· * ·)
  · have hc : IsCompact ((Fin.init : (Fin (m + 1) → G) → Fin m → G) ⁻¹'
        (Set.pi Set.univ fun _ : Fin m => (K : Set G)) ∩
          (fun x : Fin (m + 1) → G => x (Fin.last m)) ⁻¹' tsupport ψ) := by
      have he : (Fin.init : (Fin (m + 1) → G) → Fin m → G) ⁻¹'
          (Set.pi Set.univ fun _ : Fin m => (K : Set G)) ∩
            (fun x : Fin (m + 1) → G => x (Fin.last m)) ⁻¹' tsupport ψ =
          Set.pi Set.univ (Fin.lastCases (tsupport ψ) fun _ => (K : Set G)) := by
        ext x
        simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_pi, Set.mem_univ,
          true_implies, Fin.init]
        constructor
        · rintro ⟨hK, hψ⟩ i
          induction i using Fin.lastCases with
          | last => simpa using hψ
          | cast i => simpa using hK i
        · intro h
          refine ⟨fun i => by simpa using h i.castSucc, by simpa using h (Fin.last m)⟩
      rw [he]
      refine isCompact_univ_pi fun i => ?_
      induction i using Fin.lastCases with
      | last => simpa using ψ.hasCompactSupport.isCompact
      | cast i => simpa using hKc
    refine HasCompactSupport.of_support_subset_isCompact hc ?_
    intro x hx
    refine ⟨?_, subset_tsupport _ ?_⟩
    · by_contra h
      apply hx
      have h0 : (Set.pi Set.univ fun _ : Fin m => (K : Set G)).indicator (fun _ => (1 : ℂ))
          (Fin.init x) = 0 :=
        Set.indicator_of_notMem (show Fin.init x ∉ Set.pi Set.univ fun _ => (K : Set G) from h) _
      simp only [splitUnitTensor, h0, mul_zero, zero_mul]
    · intro h0
      apply hx
      simp [splitUnitTensor, h0]

/-- If `ψ` is left invariant under a subgroup `K` with `0 < μ K < ∞`, the fibre integral of the
unit tensor of `K` and `ψ` is `ψ`. -/
theorem splitFiberIntegral_splitUnitTensor (μ : Measure G) [SigmaFinite μ] (K : Subgroup G)
    (hKm : MeasurableSet (K : Set G)) (hK0 : μ K ≠ 0) (hKt : μ K ≠ ⊤) (ψ : G → ℂ)
    (hψ : ∀ k ∈ K, ∀ x, ψ (k * x) = ψ x) :
    splitFiberIntegral μ (splitUnitTensor (m := m) μ K ψ) = ψ := by
  classical
  funext y
  let S : Set (Fin m → G) := Set.pi Set.univ fun _ => (K : Set G)
  have hS : MeasurableSet S := MeasurableSet.pi Set.countable_univ fun _ _ => hKm
  have hval (w : Fin m → G) : splitUnitTensor μ K ψ (splitProductFiberChart m (y, w)) =
      S.indicator (fun _ => (((μ K).toReal⁻¹ ^ m : ℝ) : ℂ) * ψ y) w := by
    rw [splitProductFiberChart_apply]
    simp only [splitUnitTensor, Fin.init_snoc, Fin.snoc_last]
    by_cases hw : w ∈ S
    · have hprod : (List.ofFn w).prod ∈ K := by
        apply K.list_prod_mem
        intro a ha
        obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
        exact hw i (Set.mem_univ i)
      rw [Set.indicator_of_mem hw, Set.indicator_of_mem hw, hψ _ (K.inv_mem hprod)]
      ring
    · rw [Set.indicator_of_notMem hw, Set.indicator_of_notMem hw]
      ring
  have hpi : (Measure.pi fun _ : Fin m => μ) S = μ K ^ m := by
    simp [S, Measure.pi_pi]
  have hreal : (Measure.pi fun _ : Fin m => μ).real S = (μ K).toReal ^ m := by
    rw [measureReal_def, hpi, ENNReal.toReal_pow]
  have hpos : (μ K).toReal ≠ 0 := ENNReal.toReal_ne_zero.mpr ⟨hK0, hKt⟩
  change (∫ w, splitUnitTensor μ K ψ (splitProductFiberChart m (y, w))
    ∂Measure.pi fun _ : Fin m => μ) = ψ y
  simp_rw [hval]
  rw [integral_indicator_const _ hS, hreal, Complex.real_smul]
  push_cast
  rw [← mul_assoc, ← mul_pow, mul_inv_cancel₀ (by exact_mod_cast hpos), one_pow, one_mul]

end FiberIntegral

end Langlands.BaseChange
