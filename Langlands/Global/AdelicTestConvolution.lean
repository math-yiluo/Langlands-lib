import Langlands.Analysis.ConvolutionIntegral
import Langlands.Global.AdelicLocalFinitenessSolutionAutomorphy
import Langlands.Global.AdelicRightConvolutionDifferentiation

/-! # Products of smooth adelic test kernels

Left-Haar convolution preserves smooth compactly supported test functions and their separate
left and right compact finiteness. Its action on continuous functions composes by convolution. -/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory MeasureTheory NumberField
open scoped CategoryTheory.MonObj ContDiff Manifold Pointwise

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.AdelicGroupPoints

open InfiniteAdelicGroupPoints Langlands.Automorphic.GroupSchemeFunctions

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left]

local notation "A" => AdelicGroupPoints F G
local notation "A∞" => InfiniteAdelicGroupPoints F G
local notation "A_f" => FiniteAdelicGroupPoints F G

theorem isAdelicTestFunction_comp_inv {d : ℕ} (hsmooth : SmoothOfRelativeDimension d G.X.hom)
    {h : A → ℂ} (hh : IsAdelicTestFunction F G h) :
    IsAdelicTestFunction F G (fun g => h g⁻¹) := by
  let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hsmooth
  let := smoothLieGroup F G hsmooth
  obtain ⟨L, hLo, hL⟩ := hh.1.2.2
  obtain ⟨U, hUo, hU⟩ := hh.2.2
  refine ⟨⟨hh.1.1.comp continuous_inv, ?_, U, hUo, ?_⟩,
    hh.2.1.comp_homeomorph (Homeomorph.inv A), L, hLo, ?_⟩
  · intro b
    apply (isPlotSmooth_iff_contMDiff F G hsmooth _).2
    have hslice := (isPlotSmooth_iff_contMDiff F G hsmooth _).1 (hh.1.2.1 b⁻¹)
    have hinv (a : A∞) : (pair F G a b)⁻¹ = pair F G a⁻¹ b⁻¹ :=
      ((split F G).symm.map_inv (a, b)).symm
    have hs := hslice.comp (contMDiff_inv 𝓘(ℝ, smoothModel F d) ∞)
    change ContMDiff 𝓘(ℝ, smoothModel F d) 𝓘(ℝ, ℂ) ∞ (fun a => h (pair F G a b)⁻¹)
    simpa only [functionInfiniteSlice, Function.comp_def, hinv] using hs
  · intro l hl g
    change h (g * ofFinite F G l)⁻¹ = h g⁻¹
    rw [mul_inv_rev, ← map_inv]
    exact hU l⁻¹ (U.inv_mem hl) g⁻¹
  · intro l hl g
    change h (ofFinite F G l * g)⁻¹ = h g⁻¹
    rw [mul_inv_rev, ← map_inv]
    exact hL l⁻¹ (L.inv_mem hl) g⁻¹

variable [LocallyOfFiniteType G.X.hom]

local notation "μ" => (Measure.haar : Measure A)

/-- Left-Haar convolution of kernels is right convolution by the inverted
second kernel applied to the first one. -/
theorem convolutionIntegral_eq_rightConvolution (h k : A → ℂ) :
    Hecke.convolutionIntegral μ h k = rightConvolution F G (fun g => k g⁻¹) h := by
  funext x
  rw [rightConvolution_eq_integral_leftKernel]
  simp [Hecke.convolutionIntegral, mul_inv_rev]

/-- Left-Haar convolution is an algebra action on continuous functions.
The double integrand is supported in the product of the two kernel supports,
after the multiplication change of coordinates. -/
theorem rightConvolution_convolutionIntegral {h k f : A → ℂ}
    (hh : Continuous h) (hc : HasCompactSupport h)
    (hk : Continuous k) (hkc : HasCompactSupport k) (hf : Continuous f) (x : A) :
    rightConvolution F G (Hecke.convolutionIntegral μ h k) f x =
      rightConvolution F G h (rightConvolution F G k f) x := by
  let integrand (z y : A) := (h y * k (y⁻¹ * z)) * f (x * z)
  have hcont : Continuous (Function.uncurry integrand) :=
    ((hh.comp continuous_snd).mul (hk.comp (continuous_snd.inv.mul continuous_fst))).mul
      (hf.comp (continuous_const.mul continuous_fst))
  have hcompact : HasCompactSupport (Function.uncurry integrand) := by
    refine HasCompactSupport.of_support_subset_isCompact
      ((hc.isCompact.mul hkc.isCompact).prod hc.isCompact) ?_
    rintro ⟨z, y⟩ hz
    change (h y * k (y⁻¹ * z)) * f (x * z) ≠ 0 at hz
    obtain ⟨hy, hyz⟩ := mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hz).1
    have hy' : y ∈ tsupport h := subset_tsupport _ hy
    have hyz' : y⁻¹ * z ∈ tsupport k := subset_tsupport _ hyz
    exact ⟨⟨y, hy', y⁻¹ * z, hyz', by simp⟩, hy'⟩
  calc
    _ = ∫ z, (∫ y, integrand z y ∂μ) ∂μ := by
      simp only [rightConvolution, Hecke.convolutionIntegral, integrand, integral_mul_const]
    _ = ∫ y, (∫ z, integrand z y ∂μ) ∂μ :=
      integral_integral_swap_of_hasCompactSupport hcont hcompact
    _ = _ := by
      unfold rightConvolution
      congr 1 with y
      rw [← integral_mul_left_eq_self («μ» := μ) (fun z => integrand z y) y]
      simp only [integrand, inv_mul_cancel_left, mul_assoc, integral_const_mul]

/-- Left-Haar convolution preserves the smooth compactly supported adelic test functions. -/
theorem isAdelicTestFunction_convolutionIntegral {d : ℕ}
    (hsmooth : SmoothOfRelativeDimension d G.X.hom)
    {h k : A → ℂ} (hh : IsAdelicTestFunction F G h) (hk : IsAdelicTestFunction F G k) :
    IsAdelicTestFunction F G (Hecke.convolutionIntegral μ h k) := by
  have hconv := (adelicRightConvolutionDifferentiation F G d hsmooth _ _
    (isAdelicTestFunction_comp_inv hsmooth hk) hh.1.1.measurable
    hh.1.1.locallyIntegrable).2.1
  obtain ⟨L, hLo, hL⟩ := hh.2.2
  refine ⟨(convolutionIntegral_eq_rightConvolution h k).symm ▸ hconv, ?_, L, hLo, ?_⟩
  · refine HasCompactSupport.of_support_subset_isCompact (hh.2.1.isCompact.mul hk.2.1.isCompact) ?_
    intro x hx
    by_contra hout
    apply hx
    apply integral_eq_zero_of_ae
    exact Filter.Eventually.of_forall fun y => by
      by_contra hne
      obtain ⟨hy, hyx⟩ := mul_ne_zero_iff.mp hne
      exact hout ⟨y, subset_tsupport _ hy, y⁻¹ * x, subset_tsupport _ hyx, by simp⟩
  · intro l hl x
    rw [convolutionIntegral_eq_rightConvolution]
    simp only [rightConvolution, mul_assoc, hL l hl]

/-- Right compact finiteness of a kernel product follows from right compact
finiteness of its second factor. -/
theorem isInfiniteSubgroupFiniteFunction_convolutionIntegral
    (K : Subgroup A∞) {h k : A → ℂ} (hh : Continuous h)
    (hk : Continuous k) (hkc : HasCompactSupport k)
    (hK : IsInfiniteSubgroupFiniteFunction F G K k) :
    IsInfiniteSubgroupFiniteFunction F G K (Hecke.convolutionIntegral μ h k) := by
  rw [convolutionIntegral_eq_rightConvolution]
  exact isInfiniteSubgroupFiniteFunction_rightConvolution K (hk.comp continuous_inv)
    (hkc.comp_homeomorph (Homeomorph.inv A)) hh (by simpa only [inv_inv] using hK)

/-- Left compact finiteness of a kernel product follows from left compact
finiteness of its first factor, expressed using inversion. -/
theorem isInfiniteSubgroupFiniteFunction_convolutionIntegral_inv
    (K : Subgroup A∞) {h k : A → ℂ} (hh : Continuous h) (hc : HasCompactSupport h)
    (hk : Continuous k) (hK : IsInfiniteSubgroupFiniteFunction F G K (fun g => h g⁻¹)) :
    IsInfiniteSubgroupFiniteFunction F G K (fun g => Hecke.convolutionIntegral μ h k g⁻¹) := by
  have heq :
      (fun g => Hecke.convolutionIntegral μ h k g⁻¹) = rightConvolution F G h (fun g => k g⁻¹) := by
    funext g
    simp only [Hecke.convolutionIntegral, rightConvolution, mul_inv_rev]
  rw [heq]
  exact isInfiniteSubgroupFiniteFunction_rightConvolution K hh hc
    (hk.comp continuous_inv) hK

/-- Right convolution by a test kernel as a complex-linear endomorphism
of the continuous functions. -/
def rightConvolutionEnd {d : ℕ} (hsmooth : SmoothOfRelativeDimension d G.X.hom)
    {h : A → ℂ} (hh : IsAdelicTestFunction F G h) : Module.End ℂ C(A, ℂ) where
  toFun f := ⟨rightConvolution F G h f, (adelicRightConvolutionDifferentiation F G d hsmooth h f
    hh f.continuous.measurable f.continuous.locallyIntegrable).2.1.1⟩
  map_add' f g := by
    ext x
    change (∫ y, h y * (f (x * y) + g (x * y)) ∂μ) =
      (∫ y, h y * f (x * y) ∂μ) + (∫ y, h y * g (x * y) ∂μ)
    simp only [mul_add]
    exact integral_add
      ((hh.1.1.mul (f.continuous.comp (continuous_const.mul continuous_id))).integrable_of_hasCompactSupport
        hh.2.1.mul_right)
      ((hh.1.1.mul (g.continuous.comp (continuous_const.mul continuous_id))).integrable_of_hasCompactSupport
        hh.2.1.mul_right)
  map_smul' c f := by
    ext x
    change (∫ y, h y * (c * f (x * y)) ∂μ) = c * ∫ y, h y * f (x * y) ∂μ
    simp only [mul_left_comm (h _) c, integral_const_mul]

@[simp]
theorem rightConvolutionEnd_apply {d : ℕ} (hsmooth : SmoothOfRelativeDimension d G.X.hom)
    {h : A → ℂ} (hh : IsAdelicTestFunction F G h) (f : C(A, ℂ)) (x : A) :
    rightConvolutionEnd hsmooth hh f x = rightConvolution F G h f x := rfl

/-- `positiveConvolutionPower h j` is the convolution power of exponent `j + 1`. -/
def positiveConvolutionPower (h : A → ℂ) : ℕ → A → ℂ
  | 0 => h
  | j + 1 => Hecke.convolutionIntegral μ h (positiveConvolutionPower h j)

theorem isAdelicTestFunction_positiveConvolutionPower {d : ℕ}
    (hsmooth : SmoothOfRelativeDimension d G.X.hom) {h : A → ℂ}
    (hh : IsAdelicTestFunction F G h) (j : ℕ) :
    IsAdelicTestFunction F G (positiveConvolutionPower h j) := by
  induction j with
  | zero => exact hh
  | succ j ih => exact isAdelicTestFunction_convolutionIntegral hsmooth hh ih

theorem isInfiniteSubgroupFiniteFunction_positiveConvolutionPower {d : ℕ}
    (hsmooth : SmoothOfRelativeDimension d G.X.hom) (K : Subgroup A∞) {h : A → ℂ}
    (hh : IsAdelicTestFunction F G h) (hr : IsInfiniteSubgroupFiniteFunction F G K h)
    (hl : IsInfiniteSubgroupFiniteFunction F G K (fun g => h g⁻¹)) (j : ℕ) :
    IsInfiniteSubgroupFiniteFunction F G K (positiveConvolutionPower h j) ∧
      IsInfiniteSubgroupFiniteFunction F G K (fun g => positiveConvolutionPower h j g⁻¹) := by
  induction j with
  | zero => exact ⟨hr, hl⟩
  | succ j ih =>
    have hj := isAdelicTestFunction_positiveConvolutionPower hsmooth hh j
    exact ⟨isInfiniteSubgroupFiniteFunction_convolutionIntegral K hh.1.1 hj.1.1 hj.2.1 ih.1,
      isInfiniteSubgroupFiniteFunction_convolutionIntegral_inv K hh.1.1 hh.2.1 hj.1.1 hl⟩

theorem rightConvolution_positiveConvolutionPower {d : ℕ}
    (hsmooth : SmoothOfRelativeDimension d G.X.hom) {h : A → ℂ}
    (hh : IsAdelicTestFunction F G h) (j : ℕ) (f : C(A, ℂ)) (x : A) :
    rightConvolution F G (positiveConvolutionPower h j) f x =
      ((rightConvolutionEnd hsmooth hh ^ (j + 1)) f) x := by
  induction j generalizing x with
  | zero => simp [positiveConvolutionPower]
  | succ j ih =>
    have hj := isAdelicTestFunction_positiveConvolutionPower hsmooth hh j
    simp only [positiveConvolutionPower, pow_succ', Module.End.mul_apply]
    rw [rightConvolution_convolutionIntegral hh.1.1 hh.2.1 hj.1.1 hj.2.1 f.continuous]
    simp only [rightConvolutionEnd_apply]
    rw [show rightConvolution F G (positiveConvolutionPower h j) f =
      ((rightConvolutionEnd hsmooth hh ^ (j + 1)) f : A → ℂ) from funext ih]
    rw [pow_succ', Module.End.mul_apply]

end Langlands.Global.AdelicGroupPoints
