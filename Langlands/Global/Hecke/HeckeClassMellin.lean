import Langlands.Global.Hecke.ThetaUnfolding
import Langlands.Global.Hecke.MixedCharacter
import Langlands.Global.Factors.HeckeThetaCoefficients
import Langlands.Global.Factors.HeckeFiniteMellin
import Langlands.Global.Factors.HeckeThetaBridges
import Langlands.Global.Factors.HeckeConductorSupport

/-!
# Mellin integrals of the class theta series of a Hecke character

For an actual Hecke character `χ` of a number field `K` with archimedean presentation `dR, dC`
and a finite divisor `d`, this module builds the theta data on the fundamental cone of the theta
series `θ(a_d, F)` with the finite theta coefficients `a_d = thetaCoeff χ d` and the Gaussian
`F = gaussF` adapted to `χ_∞`, whose Poisson dual is `θ(b_d, G)` with the Fourier theta
coefficients `b_d = fourierThetaCoeff χ ψf μ d` and `G = gaussG = κ 𝓕F` (`exists_thetaData`).
It computes the meromorphically continued Mellin transform `M` of these theta data in a right
half-plane by unfolding (`classFactor_mul_M_eq`):
`classFactor(s) M(s) = w Z(s) ∑_{p principal} c_s(p + d)`, `c_s` the divisor Euler coefficients
of `χ` and `Z(s) = ∫_V F χ_∞ N^(s-1)`, and sums such identities over a set of representatives of
the ideal classes (`sum_classFactor_mul_M`, `sum_classFactor_one_sub_mul_M`).
-/

noncomputable section

open MeasureTheory NumberField NumberField.mixedEmbedding NumberField.InfinitePlace
open scoped nonZeroDivisors Classical
open Module
open Langlands.Global.HeckeDivisor Langlands.Global.HeckeTheta
open Langlands.Global.HeckeDivisorEulerProduct
open Langlands.LocalFactor.Archimedean Langlands.LocalFactor.PadicAbelian
open Langlands.Global.CompletionPadic Langlands.ClassField.Global
open Langlands.Global.HeckeFunctionalEquation Langlands.Global.Hecke Langlands.HarmonicAnalysis

namespace Langlands.Global.HeckeAssembly

universe u

variable {K : Type u} [Field K] [NumberField K]

/-- The archimedean component of a Hecke character presented by `dR, dC`, as a function on the
mixed space. -/
abbrev mixedChar (dR : {v : InfinitePlace K // v.IsReal} → RealCharacterData)
    (dC : {v : InfinitePlace K // v.IsComplex} → ComplexCharacterData) : mixedSpace K → ℂ :=
  Hecke.mixedCharFun (fun v => (dR v).parity) (fun v => (dR v).exponent)
    (fun v => (dC v).weight) (fun v => (dC v).exponent)

section Primal

variable (χ : HeckeCharacter K)
    (dR : {v : InfinitePlace K // v.IsReal} → RealCharacterData)
    (hR : ∀ v, IsRealCharacterPresentation v.2 (χ.infiniteComponent v.1) (dR v))
    (dC : {v : InfinitePlace K // v.IsComplex} → ComplexCharacterData)
    (hC : ∀ v, IsComplexCharacterPresentation v.2 (χ.infiniteComponent v.1) (dC v))

include hR hC in
/-- **Unfolding the class theta integral.** For a divisor `d`, the Mellin integral over the
fundamental cone of the theta series with the finite theta coefficients of `d`, multiplied by the
class factor, is `w Z(s) ∑_{p principal} c(p + d)`, `c` the divisor Euler coefficients and
`Z(s) = ∫_V F χ_∞ N^(s-1)`. -/
theorem classFactor_mul_integral_thetaSeries (d : FinitePlaceDivisor K)
    {F : mixedSpace K → ℂ} {C c : ℝ} (hc : 0 < c)
    (hF : ∀ z, ‖F z‖ ≤ C * Real.exp (-(c * ‖z‖ ^ 2))) (s : ℂ)
    (hcoef : Summable fun D : FinitePlace K →₀ ℤ =>
      ‖DivisorEulerProduct.coefficient ∅ (fun v => shellWeight χ v s) D‖)
    (hint : Integrable fun y => F y * mixedChar dR dC y * (mixedEmbedding.norm y : ℂ) ^ (s - 1)) :
    classFactor χ d s * ∫ x in fundamentalCone K,
        (thetaSeries (thetaCoeff χ d) F x - thetaCoeff χ d 0 * F 0) * mixedChar dR dC x *
          (mixedEmbedding.norm x : ℂ) ^ (s - 1) =
      (Units.torsionOrder K : ℂ) *
        (∫ y, F y * mixedChar dR dC y * (mixedEmbedding.norm y : ℂ) ^ (s - 1)) *
          ∑' p : principalDivisors K, DivisorEulerProduct.coefficient ∅
            (fun v => shellWeight χ v s) ((p : FinitePlaceDivisor K) + d) := by
  have hχmul : ∀ x y, mixedEmbedding.norm x ≠ 0 → mixedEmbedding.norm y ≠ 0 →
      mixedChar dR dC (x * y) = mixedChar dR dC x * mixedChar dR dC y :=
    fun x y _ _ => Hecke.mixedCharFun_mul _ _ _ _ x y
  have hχ1 : mixedChar dR dC 1 = 1 := Hecke.mixedCharFun_one _ _ _ _
  have hcf := HeckeTheta.classFactor_ne_zero χ d s
  have hident : ∀ p : principalDivisors K, thetaCoeff χ d (principalGenerator p) *
      (mixedChar dR dC (mixedEmbedding K (principalGenerator p : K)))⁻¹ *
        ((mixedEmbedding.norm (mixedEmbedding K (principalGenerator p : K)) : ℝ) : ℂ) ^ (-s) *
          classFactor χ d s =
      DivisorEulerProduct.coefficient ∅ (fun v => shellWeight χ v s)
        ((p : FinitePlaceDivisor K) + d) := fun p => by
    rw [thetaCoeff_mul_eq_coefficient χ dR hR dC hC d (principalGenerator p) s,
      principalDivisor_principalGenerator]
  have hsum : Summable fun p : principalDivisors K =>
      ‖thetaCoeff χ d (principalGenerator p)‖ *
        ‖mixedChar dR dC (mixedEmbedding K (principalGenerator p : K))‖⁻¹ *
          mixedEmbedding.norm (mixedEmbedding K (principalGenerator p : K)) ^ (-s.re) := by
    have hinj : Function.Injective fun p : principalDivisors K =>
        (p : FinitePlaceDivisor K) + d := fun p q h => Subtype.ext (add_right_cancel h)
    refine ((hcoef.comp_injective hinj).div_const ‖classFactor χ d s‖).congr fun p => ?_
    simp only [Function.comp_apply]
    rw [← hident p, norm_mul, norm_mul, norm_mul, norm_inv,
      Complex.norm_cpow_eq_rpow_re_of_pos (Hecke.norm_mixedEmbedding_units_pos _),
      Complex.neg_re, mul_div_assoc, div_self (norm_ne_zero_iff.mpr hcf), mul_one]
  have h := Hecke.integral_thetaSeries_unfold hχmul hχ1 principalGenerator principalUnitsEquiv
    (fun p u => rfl) (Hecke.latticeIdeal d) (mem_latticeIdeal_of_thetaCoeff_ne_zero χ d)
    (norm_thetaCoeff_le_one χ d) (thetaCoeff_unit_mul χ dR hR dC hC d) hc hF s hsum hint
  rw [h]
  simp_rw [← hident]
  rw [tsum_mul_right, tsum_mul_right]
  ring

end Primal

/-! ### Summation over the ideal classes -/

section Classes

theorem tsum_eq_sum_classes {f : FinitePlaceDivisor K → ℂ} (hf : Summable f) :
    ∑' D, f D = ∑ C : ClassGroup (𝓞 K), ∑' p : principalDivisors K,
      f ((p : FinitePlaceDivisor K) + classRepresentative C) := by
  have hf' : Summable (f ∘ classPrincipalEquiv) := classPrincipalEquiv.summable_iff.mpr hf
  rw [← classPrincipalEquiv.tsum_eq]
  calc ∑' c, f (classPrincipalEquiv c) = ∑' C, ∑' p, f (classPrincipalEquiv (C, p)) :=
        hf'.tsum_prod' fun C => hf'.prod_factor C
    _ = _ := by rw [tsum_fintype]; rfl

theorem tsum_eq_sum_classes_neg {f : FinitePlaceDivisor K → ℂ} (hf : Summable f) :
    ∑' D, f D = ∑ C : ClassGroup (𝓞 K), ∑' p : principalDivisors K,
      f ((p : FinitePlaceDivisor K) - classRepresentative C) := by
  have hf' : Summable (f ∘ classPrincipalNegEquiv) := classPrincipalNegEquiv.summable_iff.mpr hf
  rw [← classPrincipalNegEquiv.tsum_eq]
  calc ∑' c, f (classPrincipalNegEquiv c) = ∑' C, ∑' p, f (classPrincipalNegEquiv (C, p)) :=
        hf'.tsum_prod' fun C => hf'.prod_factor C
    _ = _ := by rw [tsum_fintype]; rfl

end Classes

/-! ### The theta data of a divisor -/

section ThetaData

open scoped FourierTransform Real

variable (aR : {v : InfinitePlace K // v.IsReal} → ℝˣ) (aC : {v : InfinitePlace K // v.IsComplex} → ℂˣ)
  (dR : {v : InfinitePlace K // v.IsReal} → RealCharacterData)
  (dC : {v : InfinitePlace K // v.IsComplex} → ComplexCharacterData)

/-- The Gaussian `F_{p,N}` adapted to the archimedean presentation. -/
def gaussF : mixedSpace K → ℂ :=
  Hecke.mixedGaussian (fun v => (aR v : ℝ)) (fun v => ((aC v : ℂˣ) : ℂ))
    (fun v => (dR v).parity) (fun v => (dC v).weight)

/-- The self-dual Fourier transform `κ 𝓕 F_{p,N}` of `gaussF`. -/
def gaussG : mixedSpace K → ℂ := fun w =>
  (Hecke.mixedGaussianConst (fun v => (aR v : ℝ)) (fun v => ((aC v : ℂˣ) : ℂ)) : ℂ) *
    VectorFourier.fourierIntegral 𝐞 volume
      (Hecke.tracePairing (fun v => (aR v : ℝ)) (fun v => ((aC v : ℂˣ) : ℂ))) (gaussF aR aC dR dC) w

theorem gaussG_eq (w : mixedSpace K) :
    gaussG aR aC dR dC w =
      (Hecke.mixedGaussianConst (fun v => (aR v : ℝ)) (fun v => ((aC v : ℂˣ) : ℂ)) : ℂ) *
        (Hecke.mixedGaussianFTConst (fun v => (aR v : ℝ)) (fun v => ((aC v : ℂˣ) : ℂ))
          (fun v => (dR v).parity) (fun v => (dC v).weight) *
          Hecke.mixedGaussian (fun v => (aR v : ℝ)) (fun v => ((aC v : ℂˣ) : ℂ))
            (fun v => (dR v).parity) (-(fun v => (dC v).weight)) w) := by
  rw [gaussG, gaussF, Hecke.fourierIntegral_mixedGaussian _ _ (fun v => (aR v).ne_zero)
    (fun v => (aC v).ne_zero)]

theorem continuous_gaussF : Continuous (gaussF aR aC dR dC) :=
  Hecke.continuous_mixedGaussian _ _ _ _

theorem continuous_gaussG : Continuous (gaussG aR aC dR dC) := by
  have : gaussG aR aC dR dC = fun w => _ := funext (gaussG_eq aR aC dR dC)
  rw [this]
  exact continuous_const.mul (continuous_const.mul (Hecke.continuous_mixedGaussian _ _ _ _))

theorem exists_gaussF_le :
    ∃ C c : ℝ, 0 < c ∧ ∀ z, ‖gaussF aR aC dR dC z‖ ≤ C * Real.exp (-(c * ‖z‖ ^ 2)) := by
  obtain ⟨C, c, -, hc, h⟩ := Hecke.exists_norm_mixedGaussian_le (fun v => (dR v).parity)
    (fun v => (dC v).weight) (fun v => (aR v).ne_zero) (fun v => (aC v).ne_zero)
  exact ⟨C, c, hc, h⟩

theorem exists_gaussG_le :
    ∃ C c : ℝ, 0 < c ∧ ∀ z, ‖gaussG aR aC dR dC z‖ ≤ C * Real.exp (-(c * ‖z‖ ^ 2)) := by
  obtain ⟨C, c, -, hc, h⟩ := Hecke.exists_norm_mixedGaussian_le (fun v => (dR v).parity)
    (-(fun v => (dC v).weight)) (fun v => (aR v).ne_zero) (fun v => (aC v).ne_zero)
  set k := (Hecke.mixedGaussianConst (fun v => (aR v : ℝ)) (fun v => ((aC v : ℂˣ) : ℂ)) : ℂ) *
    Hecke.mixedGaussianFTConst (fun v => (aR v : ℝ)) (fun v => ((aC v : ℂˣ) : ℂ))
      (fun v => (dR v).parity) (fun v => (dC v).weight)
  refine ⟨‖k‖ * C, c, hc, fun z => ?_⟩
  rw [gaussG_eq, ← mul_assoc, norm_mul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (h z) (norm_nonneg _)

/-- **The theta data of a divisor.** For a divisor `d`, the theta series with the finite theta
coefficients of `d` and the Gaussian `gaussF`, and the theta series with the Fourier theta
coefficients and `gaussG`, form theta data on the fundamental cone for the weight `χ_∞`. -/
theorem exists_thetaData (χ : HeckeCharacter K) (ψ : UnitaryAdditiveCharacter (Adeles K))
    (hdiag : ∀ x : K, ψ (diagonal K x) = 1)
    (ψf : ∀ v : FinitePlace K,
      @UnitaryAdditiveCharacter (CompletionPadic.padicField v).Carrier _
        (topologicalData v).topology)
    (hf : ∀ v, IsFiniteAdditiveComponent ψ v (ψf v))
    (μ : ∀ v : FinitePlace K, SelfDualHaar (topologicalData v) (ψf v))
    (hR : ∀ v, IsRealAdditiveComponent ψ v.1 v.2 (aR v))
    (hC : ∀ v, IsComplexAdditiveComponent ψ v.1 v.2 (aC v))
    (d : FinitePlaceDivisor K) :
    ∃ T : (Hecke.fundamentalDyadicCone (K := K)).ThetaData volume,
      T.χ = mixedChar dR dC ∧
      T.l = Hecke.mixedCharTwo (fun v => (dR v).parity) (fun v => (dR v).exponent)
        (fun v => (dC v).weight) (fun v => (dC v).exponent) ∧
      (∀ x : mixedSpace K, T.f x = Hecke.thetaSeries (thetaCoeff χ d) (gaussF aR aC dR dC) x -
        thetaCoeff χ d 0 * gaussF aR aC dR dC 0) ∧
      (∀ x : mixedSpace K, T.g x = Hecke.thetaSeries (fourierThetaCoeff χ ψf μ d) (gaussG aR aC dR dC) x⁻¹ -
        fourierThetaCoeff χ ψf μ d 0 * gaussG aR aC dR dC 0) := by
  have haR : ∀ v, (aR v : ℝ) ≠ 0 := fun v => (aR v).ne_zero
  have haC : ∀ v, ((aC v : ℂˣ) : ℂ) ≠ 0 := fun v => (aC v).ne_zero
  have hprod := additiveProductFormula_of_global ψ hdiag ψf hf aR hR aC hC
  set n := additiveConductorDivisor ψ hdiag ψf hf aR hR aC hC with hn_def
  have hn : ∀ v, (topologicalData v).additiveConductor (ψf v) = n v := fun v => rfl
  have hψn : ∀ v ∉ n.support, (topologicalData v).additiveConductor (ψf v) = 0 := fun v hv =>
    by rw [hn v]; exact Finsupp.notMem_support_iff.mp hv
  obtain ⟨Sram, hSram⟩ := exists_finset_conductor_eq_zero χ
  set S := d.support ∪ Sram ∪ n.support with hS_def
  have hdS : d.support ⊆ S := Finset.subset_union_left.trans Finset.subset_union_left
  have hramS : ∀ v ∉ S, (topologicalData v).multiplicativeConductor (χ.finiteComponent v) = 0 :=
    fun v hv => hSram v (fun h => hv (Finset.subset_union_right.trans Finset.subset_union_left h))
  have hnS : n.support ⊆ S := Finset.subset_union_right
  have hψS : ∀ v ∉ S, (topologicalData v).additiveConductor (ψf v) = 0 :=
    fun v hv => hψn v (fun h => hv (hnS h))
  -- polynomial decay for Poisson summation
  set r : ℝ := (finrank ℝ (mixedSpace K) : ℝ) + 1
  have hr : (finrank ℝ (mixedSpace K) : ℝ) < r := lt_add_one _
  obtain ⟨CF, hCF⟩ := Hecke.exists_norm_mixedGaussian_le_rpow (fun v => (dR v).parity)
    (fun v => (dC v).weight) haR haC r
  obtain ⟨CG, hCG⟩ := Hecke.exists_norm_mixedGaussian_le_rpow (fun v => (dR v).parity)
    (-(fun v => (dC v).weight)) haR haC r
  set c := Hecke.mixedGaussianFTConst (fun v => (aR v : ℝ)) (fun v => ((aC v : ℂˣ) : ℂ))
    (fun v => (dR v).parity) (fun v => (dC v).weight)
  let F' : C(mixedSpace K, ℂ) := ⟨gaussF aR aC dR dC, continuous_gaussF aR aC dR dC⟩
  have hFF : ∀ w, ‖VectorFourier.fourierIntegral 𝐞 volume
      (Hecke.tracePairing (fun v => (aR v : ℝ)) (fun v => ((aC v : ℂˣ) : ℂ))) F' w‖ ≤
        (‖c‖ * CG) * (1 + ‖w‖) ^ (-r) := fun w => by
    change ‖VectorFourier.fourierIntegral 𝐞 volume _ (gaussF aR aC dR dC) w‖ ≤ _
    rw [gaussF, Hecke.fourierIntegral_mixedGaussian _ _ haR haC, norm_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hCG w) (norm_nonneg _)
  -- the Poisson relation
  have ha_eq : thetaCoeff χ d = Hecke.tensorCoeff S (fun v y => dilatedEulerTest χ d v y) :=
    funext (thetaCoeff_eq_tensorCoeff χ d S hdS hramS)
  have hb_eq : fourierThetaCoeff χ ψf μ d =
      Hecke.tensorCoeff S (fun v => Hecke.localFourier ψf μ v (dilatedEulerTest χ d v)) := by
    rw [← fourierDilatedEulerTest_eq]
    exact funext (fourierThetaCoeff_eq_tensorCoeff χ ψf μ d S hdS hramS hψS)
  have hpoisson : ∀ x ∈ fundamentalCone K,
      Hecke.thetaSeries (thetaCoeff χ d) (gaussF aR aC dR dC) x =
        (mixedEmbedding.norm x : ℂ)⁻¹ *
          Hecke.thetaSeries (fourierThetaCoeff χ ψf μ d) (gaussG aR aC dR dC) x⁻¹ := by
    intro x hx
    rw [ha_eq, hb_eq]
    exact Hecke.thetaSeries_tensorCoeff_eq haR haC hprod n hn μ S hnS (dilatedEulerTest χ d) F'
      hr hCF hFF (fundamentalCone.norm_pos_of_mem hx).ne'
  obtain ⟨e, -, he⟩ := exists_fourierThetaCoeff_support χ ψf μ n.support hψn d
  obtain ⟨CFg, cFg, hcFg, hFg⟩ := exists_gaussF_le aR aC dR dC
  refine ⟨Hecke.coneThetaData (Hecke.latticeIdeal d) (Hecke.latticeIdeal e)
    (mem_latticeIdeal_of_thetaCoeff_ne_zero χ d) he ⟨1, norm_thetaCoeff_le_one χ d⟩
    (exists_norm_fourierThetaCoeff_le χ ψf μ n.support hψn d)
    (continuous_gaussF aR aC dR dC) (continuous_gaussG aR aC dR dC) ⟨CFg, cFg, hcFg, hFg⟩
    (exists_gaussG_le aR aC dR dC)
    (Hecke.measurable_mixedCharFun _ _ _ _).aestronglyMeasurable
    (Hecke.exists_norm_mixedCharFun_le_cone _ _ _ _) hpoisson
    (Hecke.mixedCharTwo_ne_zero _ _ _ _) (fun x _ => Hecke.mixedCharFun_two_smul _ _ _ _ x),
    rfl, rfl, fun x => rfl, fun x => rfl⟩

/-- **The primal Mellin identity of a divisor.** For theta data `T` of the divisor `d` and `s` in
the range of convergence, `classFactor(s) M(s) = w Z(s) ∑_p c(p + d)`. -/
theorem classFactor_mul_M_eq (χ : HeckeCharacter K)
    (hdR : ∀ v, IsRealCharacterPresentation v.2 (χ.infiniteComponent v.1) (dR v))
    (hdC : ∀ v, IsComplexCharacterPresentation v.2 (χ.infiniteComponent v.1) (dC v))
    (d : FinitePlaceDivisor K) (T : (Hecke.fundamentalDyadicCone (K := K)).ThetaData volume)
    (hTχ : T.χ = mixedChar dR dC)
    (hTf : ∀ x : mixedSpace K, T.f x = Hecke.thetaSeries (thetaCoeff χ d) (gaussF aR aC dR dC) x -
      thetaCoeff χ d 0 * gaussF aR aC dR dC 0)
    (s : ℂ) (hratio : 1 < ‖T.ratio (s - 1)‖)
    (hcoef : Summable fun D : FinitePlace K →₀ ℤ =>
      ‖DivisorEulerProduct.coefficient ∅ (fun v => shellWeight χ v s) D‖)
    (hint : Integrable fun y => gaussF aR aC dR dC y * mixedChar dR dC y *
      (mixedEmbedding.norm y : ℂ) ^ (s - 1)) :
    classFactor χ d s * T.M s =
      (Units.torsionOrder K : ℂ) *
        (∫ y, gaussF aR aC dR dC y * mixedChar dR dC y * (mixedEmbedding.norm y : ℂ) ^ (s - 1)) *
          ∑' p : principalDivisors K, DivisorEulerProduct.coefficient ∅
            (fun v => shellWeight χ v s) ((p : FinitePlaceDivisor K) + d) := by
  obtain ⟨CF, cF, hcF, hFb⟩ := exists_gaussF_le aR aC dR dC
  rw [(T.M_eq_integral hratio).2]
  have h := classFactor_mul_integral_thetaSeries χ dR hdR dC hdC d hcF hFb s hcoef hint
  rw [← h]
  congr 1
  refine setIntegral_congr_fun (measurableSet_fundamentalCone K) fun x _ => ?_
  simp only [hTf, hTχ, Hecke.fundamentalDyadicCone_N]

/-- **Sum over the ideal classes, primal side.** -/
theorem sum_classFactor_mul_M (χ : HeckeCharacter K)
    (hdR : ∀ v, IsRealCharacterPresentation v.2 (χ.infiniteComponent v.1) (dR v))
    (hdC : ∀ v, IsComplexCharacterPresentation v.2 (χ.infiniteComponent v.1) (dC v))
    (T : ClassGroup (𝓞 K) → (Hecke.fundamentalDyadicCone (K := K)).ThetaData volume)
    (hTχ : ∀ C, (T C).χ = mixedChar dR dC)
    (hTf : ∀ C, ∀ x : mixedSpace K, (T C).f x =
      Hecke.thetaSeries (thetaCoeff χ (classRepresentative C)) (gaussF aR aC dR dC) x -
        thetaCoeff χ (classRepresentative C) 0 * gaussF aR aC dR dC 0)
    (s : ℂ) (hratio : ∀ C, 1 < ‖(T C).ratio (s - 1)‖)
    (hcoef : Summable fun D : FinitePlace K →₀ ℤ =>
      ‖DivisorEulerProduct.coefficient ∅ (fun v => shellWeight χ v s) D‖)
    (hint : Integrable fun y => gaussF aR aC dR dC y * mixedChar dR dC y *
      (mixedEmbedding.norm y : ℂ) ^ (s - 1)) :
    ∑ C, classFactor χ (classRepresentative C) s * (T C).M s =
      (Units.torsionOrder K : ℂ) *
        (∫ y, gaussF aR aC dR dC y * mixedChar dR dC y * (mixedEmbedding.norm y : ℂ) ^ (s - 1)) *
          finiteMellin χ s := by
  rw [finiteMellin, tsum_eq_sum_classes hcoef.of_norm, Finset.mul_sum]
  exact Finset.sum_congr rfl fun C _ => classFactor_mul_M_eq aR aC dR dC χ hdR hdC
    (classRepresentative C) (T C) (hTχ C) (hTf C) s (hratio C) hcoef hint

/-- **Sum over the ideal classes, dual side**, from the dual identity of each class. -/
theorem sum_classFactor_one_sub_mul_M (χ : HeckeCharacter K)
    (ψf : ∀ v : FinitePlace K,
      @UnitaryAdditiveCharacter (CompletionPadic.padicField v).Carrier _
        (topologicalData v).topology)
    (μ : ∀ v : FinitePlace K, SelfDualHaar (topologicalData v) (ψf v))
    (T : ClassGroup (𝓞 K) → (Hecke.fundamentalDyadicCone (K := K)).ThetaData volume)
    (hTχ : ∀ C, (T C).χ = mixedChar dR dC)
    (hTg : ∀ C, ∀ x : mixedSpace K, (T C).g x =
      Hecke.thetaSeries (fourierThetaCoeff χ ψf μ (classRepresentative C)) (gaussG aR aC dR dC)
        x⁻¹ - fourierThetaCoeff χ ψf μ (classRepresentative C) 0 * gaussG aR aC dR dC 0)
    (s : ℂ) (hratio : ∀ C, ‖(T C).ratio (1 - s)‖ < 1) (S : Finset (FinitePlace K))
    (hcoef : Summable fun D : FinitePlace K →₀ ℤ =>
      ‖DivisorEulerProduct.coefficient S (fun v => fourierShellWeight χ ψf μ v s) D‖)
    (ZG : ℂ)
    (hdual : ∀ C, classFactor χ (classRepresentative C) (1 - s) *
      ∫ x in fundamentalCone K, (Hecke.thetaSeries
        (fourierThetaCoeff χ ψf μ (classRepresentative C)) (gaussG aR aC dR dC) x⁻¹ -
          fourierThetaCoeff χ ψf μ (classRepresentative C) 0 * gaussG aR aC dR dC 0) *
            mixedChar dR dC x * (mixedEmbedding.norm x : ℂ) ^ (-s - 1) =
      (Units.torsionOrder K : ℂ) * ZG * ∑' p : principalDivisors K,
        DivisorEulerProduct.coefficient S (fun v => fourierShellWeight χ ψf μ v s)
          (-(p : FinitePlaceDivisor K) - classRepresentative C)) :
    ∑ C, classFactor χ (classRepresentative C) (1 - s) * (T C).M (1 - s) =
      (Units.torsionOrder K : ℂ) * ZG * fourierFiniteMellin χ ψf μ S s := by
  rw [fourierFiniteMellin, tsum_eq_sum_classes_neg hcoef.of_norm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun C _ => ?_
  rw [((T C).M_one_sub_eq_integral (hratio C)).2]
  have hneg : ∑' p : principalDivisors K,
      DivisorEulerProduct.coefficient S (fun v => fourierShellWeight χ ψf μ v s)
        ((p : FinitePlaceDivisor K) - classRepresentative C) =
      ∑' p : principalDivisors K,
      DivisorEulerProduct.coefficient S (fun v => fourierShellWeight χ ψf μ v s)
        (-(p : FinitePlaceDivisor K) - classRepresentative C) := by
    rw [← (Equiv.neg (principalDivisors K)).tsum_eq]
    rfl
  rw [hneg, ← hdual C]
  congr 1
  refine setIntegral_congr_fun (measurableSet_fundamentalCone K) fun x _ => ?_
  simp only [hTg, hTχ, Hecke.fundamentalDyadicCone_N]

end ThetaData

end Langlands.Global.HeckeAssembly
