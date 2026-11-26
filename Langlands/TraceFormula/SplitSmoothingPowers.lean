import Langlands.BaseChange.SplitContinuousMatching
import Langlands.Representation.Archimedean.DixmierMalliavin
import Langlands.Representation.Archimedean.GardingKernelOperations
import Langlands.Representation.Unitary.IntegratedConvolutionProof
import Mathlib.MeasureTheory.Integral.Pi

/-! # Convolution powers of matching tensors at split places -/

noncomputable section

namespace Langlands.TraceFormula

open Langlands.BaseChange Langlands.Hecke MeasureTheory
open scoped ContDiff Manifold Pointwise

universe u v

section Convolution

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] [T2Space G] [LocallyCompactSpace G]
  [SecondCountableTopology G]
  (μ : Measure G) [μ.IsHaarMeasure]

/-- The convolution of `k + 1` copies of `f`, using the ordered split fibre integral. -/
def positiveConvolutionPower (f : G → ℂ) (k : ℕ) : G → ℂ :=
  splitFiberConvolution μ (fun _ : Fin (k + 1) => f)

omit [LocallyCompactSpace G] [SecondCountableTopology G] [μ.IsHaarMeasure] in
@[simp]
theorem positiveConvolutionPower_zero (f : G → ℂ) : positiveConvolutionPower μ f 0 = f :=
  funext fun _ => splitFiberConvolution_zero _ _ _

theorem positiveConvolutionPower_succ {f : G → ℂ} (hc : Continuous f) (hs : HasCompactSupport f)
    (k : ℕ) : positiveConvolutionPower μ f (k + 1) =
      convolutionIntegral μ f (positiveConvolutionPower μ f k) :=
  funext fun _ => splitFiberConvolution_succ μ _ (fun _ => hc) (fun _ => hs) _

theorem positiveConvolutionPower_continuous_hasCompactSupport {f : G → ℂ}
    (hc : Continuous f) (hs : HasCompactSupport f) (k : ℕ) :
    Continuous (positiveConvolutionPower μ f k) ∧ HasCompactSupport (positiveConvolutionPower μ f k) :=
  splitFiberConvolution_continuous_hasCompactSupport μ _ (fun _ => hc) (fun _ => hs)

omit [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] in
private theorem convolutionIntegral_assoc {f g h : G → ℂ}
    (hf : Continuous f) (hg : Continuous g) (hh : Continuous h)
    (hfc : HasCompactSupport f) (hgc : HasCompactSupport g) :
    convolutionIntegral μ (convolutionIntegral μ f g) h =
      convolutionIntegral μ f (convolutionIntegral μ g h) := by
  funext x
  let I (p : G × G) := (f p.2 * g (p.2⁻¹ * p.1)) * h (p.1⁻¹ * x)
  have hI : Continuous I :=
    ((hf.comp continuous_snd).mul (hg.comp (continuous_snd.inv.mul continuous_fst))).mul
      (hh.comp (continuous_fst.inv.mul continuous_const))
  have hIs : HasCompactSupport I := by
    apply HasCompactSupport.of_support_subset_isCompact ((hfc.mul hgc).prod hfc)
    rintro ⟨z, y⟩ hy
    have hn := mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hy).1
    exact ⟨⟨y, subset_tsupport f hn.1, y⁻¹ * z, subset_tsupport g hn.2, mul_inv_cancel_left _ _⟩,
      subset_tsupport f hn.1⟩
  change (∫ z, (∫ y, f y * g (y⁻¹ * z) ∂μ) * h (z⁻¹ * x) ∂μ) =
    ∫ y, f y * (∫ z, g z * h (z⁻¹ * (y⁻¹ * x)) ∂μ) ∂μ
  calc
    _ = ∫ z, ∫ y, I (z, y) ∂μ ∂μ := by
      congr 1
      funext z
      exact (integral_mul_const _ _).symm
    _ = ∫ y, ∫ z, I (z, y) ∂μ ∂μ := integral_integral_swap_of_hasCompactSupport hI hIs
    _ = ∫ y, ∫ z, (f y * g z) * h (z⁻¹ * (y⁻¹ * x)) ∂μ ∂μ := by
      congr 1
      funext y
      rw [← integral_mul_left_eq_self (fun z => I (z, y)) y]
      simp only [I, inv_mul_cancel_left, mul_inv_rev, mul_assoc]
    _ = _ := by
      congr 1
      funext y
      simp_rw [mul_assoc]
      exact integral_const_mul _ _

theorem convolutionIntegral_positiveConvolutionPower {f : G → ℂ}
    (hc : Continuous f) (hs : HasCompactSupport f) (i j : ℕ) :
    convolutionIntegral μ (positiveConvolutionPower μ f i) (positiveConvolutionPower μ f j) =
      positiveConvolutionPower μ f (i + j + 1) := by
  induction i with
  | zero => rw [positiveConvolutionPower_zero, Nat.zero_add, positiveConvolutionPower_succ μ hc hs]
  | succ i ih =>
    obtain ⟨hi, his⟩ := positiveConvolutionPower_continuous_hasCompactSupport μ hc hs i
    have hj := (positiveConvolutionPower_continuous_hasCompactSupport μ hc hs j).1
    rw [positiveConvolutionPower_succ μ hc hs i, convolutionIntegral_assoc μ hc hi hj hs his, ih,
      show i + 1 + j + 1 = (i + j + 1) + 1 by omega]
    exact (positiveConvolutionPower_succ μ hc hs (i + j + 1)).symm

theorem positiveConvolutionPower_iterated {f : G → ℂ} (hc : Continuous f)
    (hs : HasCompactSupport f) (i j : ℕ) :
    positiveConvolutionPower μ (positiveConvolutionPower μ f i) j =
      positiveConvolutionPower μ f ((i + 1) * j + i) := by
  obtain ⟨hi, his⟩ := positiveConvolutionPower_continuous_hasCompactSupport μ hc hs i
  induction j with
  | zero => simp
  | succ j ih =>
    rw [positiveConvolutionPower_succ μ hi his, ih,
      convolutionIntegral_positiveConvolutionPower μ hc hs, Nat.mul_succ]
    congr 1
    omega

theorem integratedIsometricAction_positiveConvolutionPower
    {H : Type v} [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]
    (π : G →* (H →L[ℂ] H)) (hn : ∀ g x, ‖π g x‖ = ‖x‖)
    (hm : ∀ x, AEStronglyMeasurable (fun g => π g x) μ)
    {f : G → ℂ} (hc : Continuous f) (hs : HasCompactSupport f) (k : ℕ)
    (hi : Integrable (positiveConvolutionPower μ f k) μ) :
    Analysis.integratedIsometricAction μ π hn hm _ hi =
      (Analysis.integratedIsometricAction μ π hn hm f (hc.integrable_of_hasCompactSupport hs)) ^
        (k + 1) := by
  induction k with
  | zero =>
    ext1 x
    simp only [Nat.zero_add, pow_one, Analysis.integratedIsometricAction_apply,
      positiveConvolutionPower_zero]
  | succ k ih =>
    obtain ⟨hk, hks⟩ := positiveConvolutionPower_continuous_hasCompactSupport μ hc hs k
    obtain ⟨hkInt, he⟩ := Analysis.integratedActionConvolution G H μ π hn hm
      f (positiveConvolutionPower μ f k) (hc.integrable_of_hasCompactSupport hs)
      (hk.integrable_of_hasCompactSupport hks)
    have hp := ih (hk.integrable_of_hasCompactSupport hks)
    have hLeft :
        Analysis.integratedIsometricAction μ π hn hm _ hi =
        Analysis.integratedIsometricAction μ π hn hm _ hkInt := by
      ext1 x
      simp only [Analysis.integratedIsometricAction_apply,
        positiveConvolutionPower_succ μ hc hs, convolutionIntegral]
    rw [hLeft, he, hp]
    exact (pow_succ' _ (k + 1)).symm

end Convolution

section SmoothKernels

open Langlands.Archimedean

variable {A : Type u} [NormedAddCommGroup A] [NormedSpace ℝ A]
  {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [ChartedSpace A G] [LieGroup 𝓘(ℝ, A) ∞ G] [T2Space G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  (μ : Measure G) [μ.IsHaarMeasure]

/-- Positive convolution powers of smooth compact kernels are smooth compact kernels. -/
def positiveConvolutionPowerKernel (f : smoothCompactKernels A G) (k : ℕ) :
    smoothCompactKernels A G := by
  refine ⟨positiveConvolutionPower μ f.val k, ?_,
    (positiveConvolutionPower_continuous_hasCompactSupport μ f.property.1.continuous
      f.property.2 k).2⟩
  induction k with
  | zero => simpa only [positiveConvolutionPower_zero] using f.property.1
  | succ k ih =>
    let g : smoothCompactKernels A G := ⟨positiveConvolutionPower μ f.val k, ih,
      (positiveConvolutionPower_continuous_hasCompactSupport μ f.property.1.continuous
        f.property.2 k).2⟩
    rw [positiveConvolutionPower_succ μ f.property.1.continuous f.property.2]
    exact (gardingKernelConvolution μ f g).property.1

private theorem positiveConvolutionPowerKernel_succ (f : smoothCompactKernels A G) (k : ℕ) :
    positiveConvolutionPowerKernel μ f (k + 1) =
      gardingKernelConvolution μ f (positiveConvolutionPowerKernel μ f k) :=
  Subtype.ext (positiveConvolutionPower_succ μ f.property.1.continuous f.property.2 k)

/-- Conjugate inversion of a positive convolution power equals the power of the adjoint kernel. -/
theorem adjoint_positiveConvolutionPowerKernel (f : smoothCompactKernels A G) (k : ℕ) :
    adjointGardingKernel (positiveConvolutionPowerKernel μ f k) =
      positiveConvolutionPowerKernel μ (adjointGardingKernel f) k := by
  induction k with
  | zero =>
    have he (g : smoothCompactKernels A G) : positiveConvolutionPowerKernel μ g 0 = g :=
      Subtype.ext (positiveConvolutionPower_zero μ g.val)
    rw [he, he]
  | succ k ih =>
    rw [positiveConvolutionPowerKernel_succ, adjointGardingKernel_convolution, ih]
    apply Subtype.ext
    let g := adjointGardingKernel f
    change convolutionIntegral μ (positiveConvolutionPower μ g.val k) g.val =
      positiveConvolutionPower μ g.val (k + 1)
    have he := convolutionIntegral_positiveConvolutionPower μ g.property.1.continuous
      g.property.2 k 0
    simpa only [positiveConvolutionPower_zero, Nat.add_zero] using he

end SmoothKernels

private theorem convolutionIntegral_pi_tensor
    {G : Type u} [Group G] [MeasurableSpace G] (μ : Measure G) [SigmaFinite μ]
    {m : ℕ} (f g : Fin m → G → ℂ) (x : Fin m → G) :
    convolutionIntegral (Measure.pi fun _ : Fin m => μ) (fun y => ∏ i, f i (y i))
      (fun y => ∏ i, g i (y i)) x =
      ∏ i, convolutionIntegral μ (f i) (g i) (x i) := by
  simp only [convolutionIntegral, Pi.mul_apply, Pi.inv_apply, ← Finset.prod_mul_distrib]
  exact integral_fintype_prod_eq_prod (fun i y => f i y * g i (y⁻¹ * x i))

/-- An identical tensor at a split place and its matching ordered convolution
remain concordant after taking the same positive convolution power on both groups. -/
def SplitSmoothingPowersStatement : Prop :=
  ∀ (F : Type u) [Field F] [TopologicalSpace F] [IsTopologicalDivisionRing F] [T2Space F]
    (n m : ℕ)
    [LocallyCompactSpace (GeneralLinear n F)] [SecondCountableTopology (GeneralLinear n F)]
    [MeasurableSpace (GeneralLinear n F)] [BorelSpace (GeneralLinear n F)]
    [MeasurableSpace (GeneralLinear n (Fin (m + 1) → F))]
    [BorelSpace (GeneralLinear n (Fin (m + 1) → F))]
    (μF : Measure (GeneralLinear n F)) [μF.IsHaarMeasure]
    (f : GeneralLinear n F → ℂ), Continuous f → HasCompactSupport f →
    let μE := splitContinuousHaar (m := m) μF
    let φ := fun x => ∏ i, f (splitGLCoordinates F n (m + 1) x i)
    ∀ k : ℕ,
      AreConcordant (splitCyclicShift F (m + 1)) (m + 1) μF μE
        (positiveConvolutionPower μE φ k)
        (positiveConvolutionPower μF (positiveConvolutionPower μF f m) k)

theorem splitSmoothingPowers : SplitSmoothingPowersStatement.{u} := by
  intro F _ _ _ _ n m _ _ _ _ _ _ μF _ f hc hs μE φ k
  let κ := splitGLCoordinates F n (m + 1)
  let ψ (k : ℕ) := fun _ : Fin (m + 1) => positiveConvolutionPower μF f k
  let φ' (k : ℕ) := fun x => ∏ i, ψ k i (κ x i)
  let : LocallyCompactSpace (GeneralLinear n (Fin (m + 1) → F)) :=
    κ.toHomeomorph.isOpenEmbedding.locallyCompactSpace
  let : SecondCountableTopology (GeneralLinear n (Fin (m + 1) → F)) :=
    κ.toHomeomorph.isInducing.secondCountableTopology
  let : μE.IsHaarMeasure := splitContinuousHaar_isHaar μF
  have hμE : μE.map κ = Measure.pi (fun _ : Fin (m + 1) => μF) :=
    MeasurableEquiv.map_map_symm κ.toHomeomorph.toMeasurableEquiv
  have ⟨hφc, hφs⟩ := splitTensorInCoordinates_continuous_hasCompactSupport κ (fun _ => f)
    (fun _ => hc) (fun _ => hs)
  have hUpper (j : ℕ) : positiveConvolutionPower μE φ j = φ' j := by
    induction j with
    | zero =>
      rw [positiveConvolutionPower_zero]
      change (fun x => ∏ i, f (κ x i)) = φ' 0
      simp only [φ', ψ, positiveConvolutionPower_zero]
    | succ j ih =>
      rw [positiveConvolutionPower_succ μE hφc hφs, ih]
      funext x
      change convolutionIntegral μE ((fun y => ∏ i, f (y i)) ∘ ⇑κ)
        ((fun y => ∏ i, ψ j i (y i)) ∘ ⇑κ) x = φ' (j + 1) x
      rw [convolutionIntegral_comp_continuousMulEquiv κ, hμE, convolutionIntegral_pi_tensor]
      simp only [φ', ψ, positiveConvolutionPower_succ μF hc hs]
  have hLower :
      positiveConvolutionPower μF (positiveConvolutionPower μF f m) k =
        splitFiberConvolution μF (ψ k) := by
    change positiveConvolutionPower μF (positiveConvolutionPower μF f m) k =
      positiveConvolutionPower μF (positiveConvolutionPower μF f k) m
    rw [positiveConvolutionPower_iterated μF hc hs, positiveConvolutionPower_iterated μF hc hs]
    congr 1
    ring
  rw [hUpper, hLower]
  obtain ⟨hψc, hψs⟩ := positiveConvolutionPower_continuous_hasCompactSupport μF hc hs k
  exact (splitContinuousMatching F n m μF (ψ k) (fun _ => hψc) (fun _ => hψs)).2.2.2

end Langlands.TraceFormula
