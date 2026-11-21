import Langlands.HarmonicAnalysis.Distribution.BoxDistributionFactorization
import Langlands.HarmonicAnalysis.Distribution.ProductJetCovariance
import Langlands.HarmonicAnalysis.Distribution.WeightedProductJets
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-! # Integration over the orbit coordinate of a product test -/

noncomputable section

open Function MeasureTheory Set TopologicalSpace
open scoped ContDiff Distributions

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.HarmonicAnalysis

variable {O Z N F : Type*}
  [NormedAddCommGroup O] [NormedSpace ℝ O]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [NormedAddCommGroup N] [NormedSpace ℝ N]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {Q : Opens O} {U : Opens Z} {V : Opens N}

local notation "Coord" => ((O × Z) × N)
local notation "Domain" => productTestDomain (productTestDomain Q U) V
local notation "Slice" => productTestDomain U V

/-- Move the orbit coordinate from the last to the first place. -/
def orbitTestCoordinates : ((Z × N) × O) ≃L[ℝ] Coord :=
  (ContinuousLinearEquiv.prodComm ℝ (Z × N) O).trans
    (ContinuousLinearEquiv.prodAssoc ℝ O Z N).symm

@[simp]
theorem orbitTestCoordinates_apply (x : (Z × N) × O) :
    orbitTestCoordinates x = ((x.2, x.1.1), x.1.2) := rfl

@[simp]
theorem orbitTestCoordinates_symm_apply (x : Coord) :
    orbitTestCoordinates.symm x = ((x.1.2, x.2), x.1.1) := rfl

private theorem orbitTestCoordinates_preimage :
    orbitTestCoordinates ⁻¹' (Domain : Set Coord) =
      (productTestDomain Slice Q : Set ((Z × N) × O)) := by
  ext x
  change orbitTestCoordinates x ∈ Domain ↔ x ∈ productTestDomain Slice Q
  simp only [orbitTestCoordinates_apply, mem_productTestDomain]
  tauto

private theorem orbitTestCoordinates_symm_preimage :
    orbitTestCoordinates.symm ⁻¹' (productTestDomain Slice Q : Set ((Z × N) × O)) =
      (Domain : Set Coord) := by
  rw [← orbitTestCoordinates_preimage, ← preimage_comp]
  simp

/-- Insert an orbit test as a scalar factor of a slice test. -/
def orbitProductTestCLM (χ : 𝓓(Q, ℝ)) : 𝓓(Slice, ℝ) →L[ℝ] 𝓓(Domain, ℝ) :=
  (openLinearTestPullbackCLM orbitTestCoordinates.symm orbitTestCoordinates_symm_preimage).comp
    (productKernelTestCLM (TestFunction.postcompCLM (ContinuousLinearMap.mul ℝ ℝ) χ))

@[simp]
theorem orbitProductTestCLM_apply (χ : 𝓓(Q, ℝ)) (f : 𝓓(Slice, ℝ))
    (t : O) (z : Z) (y : N) : orbitProductTestCLM χ f ((t, z), y) = χ t * f (z, y) := by
  simp only [orbitProductTestCLM, ContinuousLinearMap.comp_apply, openLinearTestPullbackCLM_apply,
    orbitTestCoordinates_symm_apply]
  rfl

theorem tsupport_orbitProductTestCLM_subset (χ : 𝓓(Q, ℝ)) (f : 𝓓(Slice, ℝ)) :
    tsupport (orbitProductTestCLM χ f) ⊆
      {p : Coord | p.1.1 ∈ tsupport χ ∧ (p.1.2, p.2) ∈ tsupport f} := by
  apply closure_minimal
  · rintro ⟨⟨t, z⟩, y⟩ hp
    change orbitProductTestCLM χ f ((t, z), y) ≠ 0 at hp
    rw [orbitProductTestCLM_apply] at hp
    obtain ⟨ht, hy⟩ := mul_ne_zero_iff.mp hp
    exact ⟨subset_tsupport χ ht, subset_tsupport f hy⟩
  · exact (isClosed_tsupport χ).preimage continuous_fst.fst |>.inter
      ((isClosed_tsupport f).preimage (continuous_fst.snd.prodMk continuous_snd))

/-- Transverse differentiation acts on the slice factor of a product test. -/
theorem transverseProductJetCLM_orbitProductTestCLM (χ : 𝓓(Q, ℝ)) (f : 𝓓(Slice, ℝ))
    (i : ℕ) (t : O) (z : Z) (v : Fin i → N) :
    transverseProductJetCLM i (orbitProductTestCLM χ f) (t, z) v =
      χ t • transverseProductJetCLM i f z v := by
  rw [transverseProductJetCLM_apply_section, transverseProductJetCLM_apply_section]
  have h : (fun y : N => orbitProductTestCLM χ f ((t, z), y)) = fun y : N => χ t • f (z, y) :=
    funext fun y => orbitProductTestCLM_apply χ f t z y
  rw [h, iteratedFDeriv_const_smul_apply', smul_apply]
  exact (f.contDiff.comp (contDiff_const.prodMk contDiff_id)).contDiffAt.of_le (by simp)

/-- The slice functional obtained by inserting a fixed orbit test. -/
def orbitSliceDistribution (T : 𝓓'(Domain, F)) (χ : 𝓓(Q, ℝ)) : 𝓓'(Slice, F) :=
  T.comp (orbitProductTestCLM χ)

theorem hasTransverseJetOrder_orbitSliceDistribution (T : 𝓓'(Domain, F)) (χ : 𝓓(Q, ℝ))
    {i : ℕ} (hT : HasTransverseJetOrder T i) : HasTransverseJetOrder (orbitSliceDistribution T χ) i := by
  intro f hf
  apply hT
  intro j hj
  ext ⟨t, z⟩ v
  change transverseProductJetCLM j (orbitProductTestCLM χ f) (t, z) v = 0
  rw [transverseProductJetCLM_orbitProductTestCLM χ f j t z v, hf j hj]
  simp

section Integrate

variable [MeasurableSpace O] [BorelSpace O] (μ : Measure O) [IsLocallyFiniteMeasure μ]

/-- Integrate a test in its first coordinate using the given measure. -/
def orbitIntegratedTest (f : 𝓓(Domain, ℝ)) : 𝓓(Slice, ℝ) :=
  productFiberIntegralTest μ (openLinearTestPullbackCLM orbitTestCoordinates orbitTestCoordinates_preimage f)

@[simp]
theorem orbitIntegratedTest_apply (f : 𝓓(Domain, ℝ)) (z : Z) (y : N) :
    orbitIntegratedTest μ f (z, y) = ∫ t : O, f ((t, z), y) ∂μ := by
  simp [orbitIntegratedTest, productFiberIntegralTest_apply]

theorem orbitIntegratedTest_orbitProductTestCLM (χ : 𝓓(Q, ℝ)) (hχ : (∫ t, χ t ∂μ) = 1)
    (f : 𝓓(Slice, ℝ)) : orbitIntegratedTest μ (orbitProductTestCLM χ f) = f := by
  ext ⟨z, y⟩
  simp only [orbitIntegratedTest_apply, orbitProductTestCLM_apply, integral_mul_const, hχ, one_mul]

/-- Transverse derivatives of the integrated test are integrals of transverse derivatives. -/
theorem transverseProductJetCLM_orbitIntegratedTest (i : ℕ) (f : 𝓓(Domain, ℝ)) (z : Z)
    (v : Fin i → N) : transverseProductJetCLM i (orbitIntegratedTest μ f) z v =
      ∫ t : O, transverseProductJetCLM i f (t, z) v ∂μ := by
  rw [orbitIntegratedTest, ← productFiberNormalJet, productFiberNormalJet_apply]
  congr 1
  funext t
  let J : (Z × N) →L[ℝ] Coord :=
    ((ContinuousLinearMap.inr ℝ O Z).comp (ContinuousLinearMap.fst ℝ Z N)).prod
      (ContinuousLinearMap.snd ℝ Z N)
  let p : Coord := ((t, 0), 0)
  let g : Coord → ℝ := fun x => f (p + x)
  have hJ (x : Z × N) : J x = ((0, x.1), x.2) := rfl
  have hg : ContDiff ℝ ∞ g := f.contDiff.comp (contDiff_const.add contDiff_id)
  have h : (fun x : Z × N => openLinearTestPullbackCLM orbitTestCoordinates
      orbitTestCoordinates_preimage f (x, t)) = g ∘ J := by
    funext x
    simp [g, hJ, p]
  rw [h, J.iteratedFDeriv_comp_right hg (z, 0) (by simp)]
  change iteratedFDeriv ℝ i g (J (z, 0)) (fun k => J (0, v k)) = _
  rw [transverseProductJetCLM_apply, show g = fun x => f (p + x) from rfl,
    iteratedFDeriv_comp_add_left]
  simp [hJ, p]
  rfl

/-- The order-`i` derivative of the integrated test, as a multilinear form,
is the Bochner integral of the forms in the orbit fibers. -/
theorem transverseProductJetCLM_orbitIntegratedTest_form (i : ℕ) (f : 𝓓(Domain, ℝ)) (z : Z) :
    transverseProductJetCLM i (orbitIntegratedTest μ f) z =
      ∫ t : O, transverseProductJetCLM i f (t, z) ∂μ := by
  let g := transverseProductJetCLM i f
  have hg : Integrable (fun t : O => g (t, z)) μ := by
    apply (g.continuous.comp (continuous_id.prodMk continuous_const)).integrable_of_hasCompactSupport
    apply HasCompactSupport.of_support_subset_isCompact (g.hasCompactSupport.image continuous_fst)
    intro t ht
    exact ⟨(t, z), subset_tsupport g ht, rfl⟩
  ext v
  rw [ContinuousMultilinearMap.integral_apply hg, transverseProductJetCLM_orbitIntegratedTest]

end Integrate

section Box

variable [FiniteDimensional ℝ O] [MeasurableSpace O] [BorelSpace O]

/-- The Haar measure in orbit coordinates transported from Lebesgue measure on a box. -/
def orbitCoordinateMeasure {d : ℕ} (b : (Fin d → ℝ) ≃L[ℝ] O) : Measure O := Measure.map b volume

instance {d : ℕ} (b : (Fin d → ℝ) ≃L[ℝ] O) : (orbitCoordinateMeasure b).IsAddHaarMeasure :=
  b.isAddHaarMeasure_map volume

/-- A distribution annihilating constant orbit derivatives factors through the
orbit integral on a product whose orbit component is an open coordinate box. -/
theorem eval_eq_orbitSliceDistribution {d : ℕ} (b : (Fin d → ℝ) ≃L[ℝ] O) {a c : ℝ} (hac : a < c)
    (hQ : b ⁻¹' (Q : Set O) = openIntervalBox d a c)
    (T : 𝓓'(Domain, F))
    (hT : ∀ (v : O) (f : 𝓓(Domain, ℝ)), T (TestFunction.lineDerivCLM ℝ ((v, 0), 0) f) = 0)
    (χ : 𝓓(Q, ℝ)) (hχ : (∫ t, χ t ∂orbitCoordinateMeasure b) = 1) (f : 𝓓(Domain, ℝ)) :
    T f = orbitSliceDistribution T χ (orbitIntegratedTest (orbitCoordinateMeasure b) f) := by
  let k : ((Z × N) × (Fin d → ℝ)) ≃L[ℝ] Coord :=
    ((ContinuousLinearEquiv.refl ℝ (Z × N)).prodCongr b).trans orbitTestCoordinates
  let W := productTestDomain Slice (openIntervalBox d a c)
  have hk (p : (Z × N) × (Fin d → ℝ)) : k p = ((b p.2, p.1.1), p.1.2) := rfl
  have hW : k ⁻¹' (Domain : Set Coord) = W := by
    ext p
    change k p ∈ Domain ↔ p ∈ W
    simp only [hk, W, mem_productTestDomain]
    have hqp : b p.2 ∈ Q ↔ p.2 ∈ openIntervalBox d a c := Set.ext_iff.mp hQ p.2
    tauto
  have hWs : k.symm ⁻¹' (W : Set ((Z × N) × (Fin d → ℝ))) = (Domain : Set Coord) := by
    rw [← hW, ← preimage_comp]
    simp
  let pull := openLinearTestPullbackCLM k hW
  let push := openLinearTestPullbackCLM k.symm hWs
  let S := T.comp push
  have hS (v : Fin d → ℝ) (φ : 𝓓(W, ℝ)) : S (TestFunction.lineDerivCLM ℝ (0, v) φ) = 0 := by
    have hv : k.symm ((b v, 0), 0) = (0, v) := k.symm_apply_apply (0, v)
    have h := openLinearTestPullbackCLM_lineDerivCLM k.symm hWs φ ((b v, 0), 0)
    rw [hv] at h
    change T (push (TestFunction.lineDerivCLM ℝ (0, v) φ)) = 0
    rw [h]
    exact hT (b v) (push φ)
  let χ₀ := openLinearTestPullbackCLM b hQ χ
  have hint (g : O → ℝ) : (∫ t, g (b t)) = ∫ t, g t ∂orbitCoordinateMeasure b :=
    (integral_map_equiv b.toHomeomorph.toMeasurableEquiv g).symm
  have hχ₀ : (∫ t, χ₀ t) = 1 := by
    simp only [χ₀, openLinearTestPullbackCLM_apply, hint χ, hχ]
  have hi : productFiberIntegralTest volume (pull f) = orbitIntegratedTest (orbitCoordinateMeasure b) f := by
    ext ⟨z, y⟩
    rw [productFiberIntegralTest_apply, orbitIntegratedTest_apply]
    simp only [pull, openLinearTestPullbackCLM_apply, hk]
    exact hint fun t => f ((t, z), y)
  have hpush (g : 𝓓(Slice, ℝ)) :
      push (productKernelTestCLM (TestFunction.postcompCLM (ContinuousLinearMap.mul ℝ ℝ) χ₀) g) =
        orbitProductTestCLM χ g := by
    ext x
    obtain ⟨p, rfl⟩ := k.surjective x
    change push (productKernelTestCLM (TestFunction.postcompCLM (ContinuousLinearMap.mul ℝ ℝ) χ₀) g) (k p) = _
    rw [show push = openLinearTestPullbackCLM k.symm hWs from rfl,
      openLinearTestPullbackCLM_apply, k.symm_apply_apply, hk, orbitProductTestCLM_apply]
    rcases p with ⟨⟨z, y⟩, t⟩
    change χ₀ t * g (z, y) = χ (b t) * g (z, y)
    rw [show χ₀ t = χ (b t) from openLinearTestPullbackCLM_apply b hQ χ t]
  have hpf : push (pull f) = f := by
    ext x
    simp [push, pull]
  have h := eval_eq_of_annihilates_boxDerivatives d hac S hS χ₀ hχ₀ (pull f)
  change T (push (pull f)) = T (push (productKernelTestCLM
    (TestFunction.postcompCLM (ContinuousLinearMap.mul ℝ ℝ) χ₀) (productFiberIntegralTest volume (pull f)))) at h
  rwa [hpf, hi, hpush] at h

end Box

end Langlands.HarmonicAnalysis
