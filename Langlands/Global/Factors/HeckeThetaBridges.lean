import Langlands.Global.Factors.HeckeFourierTheta
import Langlands.Global.Factors.HeckeArchimedeanZeta
import Langlands.Global.Hecke.AdelicPoisson

/-! # Bridges from Hecke theta coefficients to adelic tensor coefficients -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Filter Topology NumberField NumberField.InfinitePlace
open scoped NumberField nonZeroDivisors Classical

namespace Langlands.Global.HeckeTheta

open Langlands.LocalFactor.PadicAbelian Langlands.Global.CompletionPadic
open Langlands.ClassField.Global Langlands.Global.HeckeDivisor
open Langlands.Global.HeckeDivisorEulerProduct
open Langlands.HarmonicAnalysis Langlands.LocalFactor.Archimedean
open Langlands.Global.HeckeFunctionalEquation

universe u

variable {K : Type u} [Field K] [NumberField K]

/-- The dilated Euler test is the function `x ↦ eulerTest_v (x π_v ^ d(v))`. -/
theorem coe_dilatedEulerTest (χ : HeckeCharacter K) (d : FinitePlaceDivisor K)
    (v : FinitePlace K) :
    (⇑(dilatedEulerTest χ d v) : FiniteCompletion K v → ℂ) = fun x =>
      eulerTest (topologicalData v) (χ.finiteComponent v)
        (x * ((uniformizerUnit (topologicalData v) ^ d v : (FiniteCompletion K v)ˣ) :
          FiniteCompletion K v)) :=
  rfl

/-- The local factor of the dual tensor: the actual local Fourier transform, for `ψf v` and
the self-dual measure `μ v`, of the dilated Euler test. -/
def fourierDilatedEulerTest (χ : HeckeCharacter K)
    (ψf : ∀ v : FinitePlace K,
      @UnitaryAdditiveCharacter (CompletionPadic.padicField v).Carrier _
        (topologicalData v).topology)
    (μ : ∀ v : FinitePlace K, SelfDualHaar (topologicalData v) (ψf v))
    (d : FinitePlaceDivisor K) (v : FinitePlace K) (y : FiniteCompletion K v) : ℂ :=
  Hecke.localFourier ψf μ v (dilatedEulerTest χ d v) y

theorem fourierDilatedEulerTest_eq (χ : HeckeCharacter K)
    (ψf : ∀ v : FinitePlace K,
      @UnitaryAdditiveCharacter (CompletionPadic.padicField v).Carrier _
        (topologicalData v).topology)
    (μ : ∀ v : FinitePlace K, SelfDualHaar (topologicalData v) (ψf v))
    (d : FinitePlaceDivisor K) :
    fourierDilatedEulerTest χ ψf μ d = fun v => Hecke.localFourier ψf μ v (dilatedEulerTest χ d v) :=
  rfl

/-- The theta coefficient is the adelic tensor coefficient of the dilated Euler tests, for
every finite set containing the support of the divisor and the ramified places. -/
theorem thetaCoeff_eq_tensorCoeff (χ : HeckeCharacter K) (d : FinitePlaceDivisor K)
    (S : Finset (FinitePlace K)) (hd : d.support ⊆ S)
    (hS : ∀ v ∉ S, (topologicalData v).multiplicativeConductor (χ.finiteComponent v) = 0)
    (γ : K) :
    thetaCoeff χ d γ = Hecke.tensorCoeff S (fun v y => dilatedEulerTest χ d v y) γ := by
  have hd0 : ∀ v ∉ S, d v = 0 := fun v hv =>
    Finsupp.notMem_support_iff.mp (fun h => hv (hd h))
  have hfac : ∀ v ∉ S, thetaFactor χ d γ v =
      eulerTest (topologicalData v) (χ.finiteComponent v)
        (algebraMap K (FiniteCompletion K v) γ) := fun v hv => by
    rw [thetaFactor, hd0 v hv, zpow_zero, Units.val_one, mul_one]
  rw [Hecke.tensorCoeff]
  split_ifs with hγ
  · rw [thetaCoeff_eq_prod χ d γ S (fun v hv => by
      rw [hfac v hv]
      exact eulerTest_eq_one_of_mem _ _ (hS v hv) (hγ v hv))]
    exact Finset.prod_congr rfl fun v _ => rfl
  · unfold Hecke.IntegralOutside at hγ
    push Not at hγ
    obtain ⟨v, hv, hvγ⟩ := hγ
    obtain ⟨T, hT⟩ := exists_finset_thetaFactor_eq_one χ d γ
    rw [thetaCoeff_eq_prod χ d γ (insert v T)
      (fun w hw => hT w (fun h => hw (Finset.mem_insert_of_mem h)))]
    refine Finset.prod_eq_zero (Finset.mem_insert_self v T) ?_
    rw [hfac v hv]
    by_contra h
    exact hvγ (mem_additiveLattice_zero_of_eulerTest_ne_zero _ _ h)

/-- The Fourier theta coefficient is the adelic tensor coefficient of the actual local Fourier
transforms of the dilated Euler tests, for every finite set containing the support of the
divisor, the ramified places and the places of nonzero additive conductor. -/
theorem fourierThetaCoeff_eq_tensorCoeff (χ : HeckeCharacter K)
    (ψf : ∀ v : FinitePlace K,
      @UnitaryAdditiveCharacter (CompletionPadic.padicField v).Carrier _
        (topologicalData v).topology)
    (μ : ∀ v : FinitePlace K, SelfDualHaar (topologicalData v) (ψf v))
    (d : FinitePlaceDivisor K) (S : Finset (FinitePlace K)) (hd : d.support ⊆ S)
    (hχS : ∀ v ∉ S, (topologicalData v).multiplicativeConductor (χ.finiteComponent v) = 0)
    (hψS : ∀ v ∉ S, (topologicalData v).additiveConductor (ψf v) = 0) (w : K) :
    fourierThetaCoeff χ ψf μ d w =
      Hecke.tensorCoeff S (fourierDilatedEulerTest χ ψf μ d) w := by
  have hd0 : ∀ v ∉ S, d v = 0 := fun v hv =>
    Finsupp.notMem_support_iff.mp (fun h => hv (hd h))
  have hfac : ∀ v ∉ S, fourierThetaFactor χ ψf μ d w v =
      eulerTest (topologicalData v) (χ.finiteComponent v)
        (algebraMap K (FiniteCompletion K v) w) := fun v hv => by
    rw [fourierThetaFactor, hd0 v hv, neg_zero, zpow_zero, zpow_zero, Units.val_one, mul_one,
      one_mul, fourierEulerTest_eq_eulerTest χ ψf μ v (hχS v hv) (hψS v hv)]
  rw [Hecke.tensorCoeff]
  split_ifs with hw
  · rw [fourierThetaCoeff_eq_prod χ ψf μ d w S (fun v hv => by
      rw [hfac v hv]
      exact eulerTest_eq_one_of_mem _ _ (hχS v hv) (hw v hv))]
    exact Finset.prod_congr rfl fun v _ => fourierThetaFactor_eq_fourierTransform χ ψf μ d w v
  · unfold Hecke.IntegralOutside at hw
    push Not at hw
    obtain ⟨v, hv, hvw⟩ := hw
    obtain ⟨T, hT⟩ := exists_finset_fourierThetaFactor_eq_one χ ψf μ S hψS d w
    rw [fourierThetaCoeff_eq_prod χ ψf μ d w (insert v T)
      (fun u hu => hT u (fun h => hu (Finset.mem_insert_of_mem h)))]
    refine Finset.prod_eq_zero (Finset.mem_insert_self v T) ?_
    rw [hfac v hv]
    by_contra h
    exact hvw (mem_additiveLattice_zero_of_eulerTest_ne_zero _ _ h)

private theorem differentiable_spectralVariable (v : FinitePlace K) :
    Differentiable ℂ (fun s => spectralVariable (topologicalData v) s) := by
  unfold spectralVariable
  fun_prop

/-- The class factor is entire in `s`. -/
theorem differentiable_classFactor (χ : HeckeCharacter K) (d : FinitePlaceDivisor K) :
    Differentiable ℂ (classFactor χ d) := by
  unfold classFactor
  refine Differentiable.fun_finsetProd fun v _ => ?_
  refine Differentiable.zpow ?_ (Or.inl fun s =>
    mul_ne_zero (Units.ne_zero _) (spectralVariable_ne_zero _ s))
  exact (differentiable_spectralVariable v).const_mul _

/-- The dual class factor is entire in `s`. -/
theorem differentiable_dualClassFactor (χ : HeckeCharacter K) (d : FinitePlaceDivisor K) :
    Differentiable ℂ (dualClassFactor χ d) := by
  have hq : ∀ v : FinitePlace K, ((topologicalData v).residueCardinality : ℂ) ≠ 0 := fun v =>
    Nat.cast_ne_zero.mpr (zero_lt_one.trans (topologicalData v).residueCardinality_gt_one).ne'
  unfold dualClassFactor
  refine Differentiable.fun_finsetProd fun v _ => ?_
  refine Differentiable.zpow ?_ (Or.inl fun s =>
    mul_ne_zero (mul_ne_zero (hq v) (inv_ne_zero (Units.ne_zero _)))
      (spectralVariable_ne_zero _ s))
  exact (differentiable_spectralVariable v).const_mul _

/-- The class factor never vanishes. -/
theorem classFactor_ne_zero (χ : HeckeCharacter K) (d : FinitePlaceDivisor K) (s : ℂ) :
    classFactor χ d s ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun _ _ =>
    zpow_ne_zero _ (mul_ne_zero (Units.ne_zero _) (spectralVariable_ne_zero _ s))

/-- The class factor at `1 - s` inverts the dual class factor at `s`. -/
theorem classFactor_one_sub_mul_dualClassFactor (χ : HeckeCharacter K)
    (d : FinitePlaceDivisor K) (s : ℂ) :
    classFactor χ d (1 - s) * dualClassFactor χ d s = 1 := by
  have h := dualClassFactor_one_sub_mul_classFactor χ d (1 - s)
  rw [sub_sub_cancel] at h
  rw [mul_comm]
  exact h

end Langlands.Global.HeckeTheta

namespace Langlands.Global.HeckeFunctionalEquation

open Langlands.LocalFactor Langlands.LocalFactor.Archimedean

universe u

variable {K : Type u} [Field K] [NumberField K]

private theorem realCharFun_neg_eq_inv (p : ℕ) (t : ℂ) {x : ℝ} (hx : x ≠ 0) :
    Hecke.realCharFun p (-t) x = (Hecke.realCharFun p t x)⁻¹ := by
  have habs : |x| ≠ 0 := abs_ne_zero.mpr hx
  have hσ : ((x / |x| : ℝ) : ℂ)⁻¹ = ((x / |x| : ℝ) : ℂ) := by
    rw [← Complex.ofReal_inv, inv_div]
    congr 1
    rw [div_eq_div_iff hx habs, abs_mul_abs_self]
  rw [Hecke.realCharFun, Hecke.realCharFun, mul_inv, ← inv_pow, hσ, Complex.cpow_neg]

private theorem complexCharFun_neg_eq_inv (N : ℤ) (u z : ℂ) :
    Hecke.complexCharFun (-N) (-u) z = (Hecke.complexCharFun N u z)⁻¹ := by
  rw [Hecke.complexCharFun, Hecke.complexCharFun, mul_inv, zpow_neg, mul_neg, Complex.cpow_neg]

section Dual

variable (χ : HeckeCharacter K)
    (dR dR' : {v : InfinitePlace K // v.IsReal} → RealCharacterData)
    (hR : ∀ v, IsRealCharacterPresentation v.2 (χ.infiniteComponent v.1) (dR v))
    (hR' : ∀ v, IsRealCharacterPresentation v.2 (χ⁻¹.infiniteComponent v.1) (dR' v))
    (dC dC' : {v : InfinitePlace K // v.IsComplex} → ComplexCharacterData)
    (hC : ∀ v, IsComplexCharacterPresentation v.2 (χ.infiniteComponent v.1) (dC v))
    (hC' : ∀ v, IsComplexCharacterPresentation v.2 (χ⁻¹.infiniteComponent v.1) (dC' v))

include hR hR' hC hC'

/-- The mixed character of the presentations of `χ⁻¹` is the mixed character of the
presentations of `χ` at the inverse point. -/
theorem mixedCharFun_dual_eq_inv_apply (y : mixedEmbedding.mixedSpace K) :
    Hecke.mixedCharFun (fun v => (dR' v).parity) (fun v => (dR' v).exponent)
        (fun v => (dC' v).weight) (fun v => (dC' v).exponent) y =
      Hecke.mixedCharFun (fun v => (dR v).parity) (fun v => (dR v).exponent)
        (fun v => (dC v).weight) (fun v => (dC v).exponent) y⁻¹ := by
  have hRel : ∀ v, (dR' v).parity = (dR v).parity ∧ (dR' v).exponent = -(dR v).exponent :=
    fun v => RealCharacterData.parity_eq_and_exponent_eq_neg_of_inv _ _
      (realCharacter_inv_of_presentation χ v.2 (hR v) (hR' v))
  have hCel : ∀ v, (dC' v).weight = -(dC v).weight ∧ (dC' v).exponent = -(dC v).exponent :=
    fun v => ComplexCharacterData.weight_eq_neg_and_exponent_eq_neg_of_inv _ _
      (complexCharacter_inv_of_presentation χ v.2 (hC v) (hC' v))
  rw [Hecke.mixedCharFun_inv]
  have h1 : (fun v => (dR' v).parity) = fun v => (dR v).parity := funext fun v => (hRel v).1
  have h2 : (fun v => (dR' v).exponent) = -(fun v => (dR v).exponent) :=
    funext fun v => by rw [Pi.neg_apply, (hRel v).2]
  have h3 : (fun v => (dC' v).weight) = -(fun v => (dC v).weight) :=
    funext fun v => by rw [Pi.neg_apply, (hCel v).1]
  have h4 : (fun v => (dC' v).exponent) = -(fun v => (dC v).exponent) :=
    funext fun v => by rw [Pi.neg_apply, (hCel v).2]
  rw [h1, h2, h3, h4]

/-- Off the zero set of the mixed norm, the mixed character of the presentations of `χ⁻¹` is
the inverse of the mixed character of the presentations of `χ`. -/
theorem mixedCharFun_dual_eq_inv (y : mixedEmbedding.mixedSpace K)
    (hy : mixedEmbedding.norm y ≠ 0) :
    Hecke.mixedCharFun (fun v => (dR' v).parity) (fun v => (dR' v).exponent)
        (fun v => (dC' v).weight) (fun v => (dC' v).exponent) y =
      (Hecke.mixedCharFun (fun v => (dR v).parity) (fun v => (dR v).exponent)
        (fun v => (dC v).weight) (fun v => (dC v).exponent) y)⁻¹ := by
  have hRel : ∀ v, (dR' v).parity = (dR v).parity ∧ (dR' v).exponent = -(dR v).exponent :=
    fun v => RealCharacterData.parity_eq_and_exponent_eq_neg_of_inv _ _
      (realCharacter_inv_of_presentation χ v.2 (hR v) (hR' v))
  have hCel : ∀ v, (dC' v).weight = -(dC v).weight ∧ (dC' v).exponent = -(dC v).exponent :=
    fun v => ComplexCharacterData.weight_eq_neg_and_exponent_eq_neg_of_inv _ _
      (complexCharacter_inv_of_presentation χ v.2 (hC v) (hC' v))
  rw [Hecke.norm_eq_prod_real_complex] at hy
  have hy1 : ∀ v, y.1 v ≠ 0 := fun v => abs_ne_zero.mp
    (Finset.prod_ne_zero_iff.mp (left_ne_zero_of_mul hy) v (Finset.mem_univ v))
  rw [Hecke.mixedCharFun, Hecke.mixedCharFun, mul_inv, ← Finset.prod_inv_distrib,
    ← Finset.prod_inv_distrib]
  congr 1
  · refine Finset.prod_congr rfl fun v _ => ?_
    rw [(hRel v).1, (hRel v).2, realCharFun_neg_eq_inv _ _ (hy1 v)]
  · refine Finset.prod_congr rfl fun v _ => ?_
    rw [(hCel v).1, (hCel v).2, complexCharFun_neg_eq_inv]

end Dual

end Langlands.Global.HeckeFunctionalEquation
