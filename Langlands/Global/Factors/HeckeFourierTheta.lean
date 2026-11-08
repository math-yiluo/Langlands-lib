import Langlands.Global.Factors.HeckeThetaCoefficients
import Langlands.LocalFactor.Abelian.TateGaussLattice

/-! # Fourier theta coefficients of actual Hecke characters -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open MeasureTheory Filter Topology NumberField NumberField.InfinitePlace
open scoped NumberField nonZeroDivisors

namespace Langlands.LocalFactor.PadicAbelian

universe u
variable {p : ℕ} [Fact p.Prime] {F : PadicField.{u} p} (T : F.TopologicalData)

local notation "Character" => @HarmonicAnalysis.Quasicharacter F.Carrier _ T.topology
local notation "AdditiveCharacter" =>
  @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology
local notation "LocalHaar" =>
  @HarmonicAnalysis.AdditiveHaarMeasure F.Carrier _ T.topology (@borel F.Carrier T.topology)
local notation "TestFunction" => @HarmonicAnalysis.SchwartzBruhat F.Carrier T.topology

/-- The dilation `x ↦ f (x * a)` of a test function by a unit. -/
def dilateTest (f : TestFunction) (a : F.Carrierˣ) : TestFunction := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  exact ⟨fun x => f (x * a),
    (HarmonicAnalysis.SchwartzBruhat.locallyConstant f).comp_continuous
      (continuous_mul_const _),
    (HarmonicAnalysis.SchwartzBruhat.hasCompactSupport f).comp_homeomorph
      (Homeomorph.mulRight₀ (a : F.Carrier) a.ne_zero)⟩

@[simp] theorem dilateTest_apply (f : TestFunction) (a : F.Carrierˣ) (x : F.Carrier) :
    dilateTest T f a x = f (x * a) :=
  rfl

/-- The Fourier integral of a dilation: `∫ ψ(xy) f(xa) dx = |a|⁻¹ ∫ ψ(x y a⁻¹) f(x) dx`. -/
theorem fourierIntegral_comp_mul_unit (ψ : AdditiveCharacter) (μ : LocalHaar)
    (f : F.Carrier → ℂ) (a : F.Carrierˣ) (y : F.Carrier) :
    let := T.topology
    let := T.valuativeRel
    let := T.localField
    let := borel F.Carrier
    let : BorelSpace F.Carrier := ⟨rfl⟩
    HarmonicAnalysis.fourierIntegral ψ μ (fun x => f (x * a)) y =
      ((T.normalizedAbs (a : F.Carrier))⁻¹ : ℂ) *
        HarmonicAnalysis.fourierIntegral ψ μ f (y * ((a⁻¹ : F.Carrierˣ) : F.Carrier)) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := borel F.Carrier
  let : BorelSpace F.Carrier := ⟨rfl⟩
  have h := integral_comp_mul_scalar T μ a
    (fun z => ψ.complex (z * (y * ((a⁻¹ : F.Carrierˣ) : F.Carrier))) * f z)
  have key : (∫ x, ψ.complex (x * y) * f (x * a) ∂μ.measure) =
      ∫ x, (fun z => ψ.complex (z * (y * ((a⁻¹ : F.Carrierˣ) : F.Carrier))) * f z)
        ((a : F.Carrier) * x) ∂μ.measure := by
    congr 1
    funext x
    dsimp only
    rw [mul_comm (a : F.Carrier) x, mul_mul_mul_comm, Units.mul_inv, mul_one]
  change (∫ x, ψ.complex (x * y) * f (x * a) ∂μ.measure) = _
  rw [key, h, Complex.real_smul, Complex.ofReal_inv]
  rfl

/-- The Fourier transform of a dilated test function. -/
theorem fourierTransform_dilateTest (ψ : AdditiveCharacter) (μ : LocalHaar)
    (f : TestFunction) (a : F.Carrierˣ) (y : F.Carrier) :
    let := T.topology
    let := T.valuativeRel
    let := T.localField
    let := borel F.Carrier
    let : BorelSpace F.Carrier := ⟨rfl⟩
    HarmonicAnalysis.fourierTransform ψ μ (dilateTest T f a) y =
      ((T.normalizedAbs (a : F.Carrier))⁻¹ : ℂ) *
        HarmonicAnalysis.fourierTransform ψ μ f (y * ((a⁻¹ : F.Carrierˣ) : F.Carrier)) :=
  fourierIntegral_comp_mul_unit T ψ μ f a y

/-- Dilation by a uniformizer power: `FT(f(· π^k))(y) = q^k FT(f)(y π^(-k))`. -/
theorem fourierTransform_dilateTest_uniformizer (ψ : AdditiveCharacter) (μ : LocalHaar)
    (f : TestFunction) (k : ℤ) (y : F.Carrier) :
    let := T.topology
    let := T.valuativeRel
    let := T.localField
    let := borel F.Carrier
    let : BorelSpace F.Carrier := ⟨rfl⟩
    HarmonicAnalysis.fourierTransform ψ μ (dilateTest T f (uniformizerUnit T ^ k)) y =
      (T.residueCardinality : ℂ) ^ k *
        HarmonicAnalysis.fourierTransform ψ μ f
          (y * ((uniformizerUnit T ^ (-k) : F.Carrierˣ) : F.Carrier)) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := borel F.Carrier
  let : BorelSpace F.Carrier := ⟨rfl⟩
  have h := fourierTransform_dilateTest T ψ μ f (uniformizerUnit T ^ k) y
  dsimp only at h
  show HarmonicAnalysis.fourierTransform ψ μ (dilateTest T f (uniformizerUnit T ^ k)) y = _
  rw [h, T.normalizedAbs_of_ne_zero (Units.ne_zero _), ord_uniformizerUnit_zpow, ← zpow_neg]
  congr 1
  push_cast
  rw [zpow_neg, inv_inv]

/-- The Fourier transform of a test function is bounded by the integral of its norm bound. -/
theorem norm_fourierTransform_eulerTest_le (χ : Character) (ψ : AdditiveCharacter)
    (μ : LocalHaar) (y : F.Carrier) :
    let := T.topology
    let := T.valuativeRel
    let := T.localField
    let := borel F.Carrier
    let : BorelSpace F.Carrier := ⟨rfl⟩
    ‖HarmonicAnalysis.fourierTransform ψ μ (eulerTest T χ) y‖ ≤
      (μ.measure (integerRing T)).toReal := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := borel F.Carrier
  let : BorelSpace F.Carrier := ⟨rfl⟩
  have hmeas : MeasurableSet (integerRing T) := by
    rw [integerRing_eq_lattice_zero]
    exact additiveLattice_measurableSet T 0
  have hfin : μ.measure (integerRing T) ≠ ⊤ := by
    rw [integerRing_eq_lattice_zero]
    exact ((T.isCompact_additiveLattice 0).measure_lt_top (μ := μ.measure)).ne
  have hint : Integrable ((integerRing T).indicator (1 : F.Carrier → ℝ)) μ.measure :=
    (integrable_indicator_iff hmeas).mpr (integrableOn_const hfin)
  change ‖∫ x, ψ.complex (x * y) * eulerTest T χ x ∂μ.measure‖ ≤ _
  refine (norm_integral_le_of_norm_le hint (Filter.Eventually.of_forall fun x => ?_)).trans
    (le_of_eq ?_)
  · rw [norm_mul, HarmonicAnalysis.UnitaryAdditiveCharacter.complex_apply, Circle.norm_coe,
      one_mul]
    by_cases hx : eulerTest T χ x = 0
    · rw [hx, norm_zero]
      exact Set.indicator_nonneg (fun _ _ => zero_le_one) x
    · have hmem : x ∈ integerRing T := by
        rw [integerRing_eq_lattice_zero]
        exact mem_additiveLattice_zero_of_eulerTest_ne_zero T χ hx
      rw [Set.indicator_of_mem hmem, Pi.one_apply]
      exact norm_eulerTest_le_one T χ x
  · rw [integral_indicator_one hmeas, measureReal_def]

/-- Nonzero values of the transformed Euler test lie in the lattice of level
`n + a`, the sum of the additive and multiplicative conductors. -/
theorem mem_additiveLattice_of_fourierTransform_eulerTest_ne_zero (χ : Character)
    (ψ : AdditiveCharacter) (μ : LocalHaar) {y : F.Carrier}
    (hy : letI := T.topology; letI := T.valuativeRel; letI := T.localField;
      letI := borel F.Carrier; letI : BorelSpace F.Carrier := ⟨rfl⟩;
      HarmonicAnalysis.fourierTransform ψ μ (eulerTest T χ) y ≠ 0) :
    y ∈ T.additiveLattice (T.additiveConductor ψ + T.multiplicativeConductor χ) := by
  classical
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := borel F.Carrier
  let : BorelSpace F.Carrier := ⟨rfl⟩
  by_cases hχ : T.multiplicativeConductor χ = 0
  · rw [fourier_eulerTest_unramified T χ hχ ψ μ y] at hy
    have h := Set.mem_of_indicator_ne_zero (right_ne_zero_of_mul hy)
    rw [hχ, Nat.cast_zero, add_zero]
    exact h
  · rw [fourier_eulerTest_ramified T χ hχ ψ μ y] at hy
    have h := Set.mem_of_indicator_ne_zero hy
    rw [T.mem_additiveLattice, gauss_valuation_le_exp_iff T h.1]
    have := h.2
    omega

end Langlands.LocalFactor.PadicAbelian

namespace Langlands.Global.HeckeTheta

open Langlands.LocalFactor.PadicAbelian Langlands.Global.CompletionPadic
open Langlands.ClassField.Global Langlands.Global.HeckeDivisor
open Langlands.Global.HeckeDivisorEulerProduct
open Langlands.HarmonicAnalysis Langlands.LocalFactor.Archimedean
open Langlands.Global.HeckeFunctionalEquation

universe u

variable {K : Type u} [Field K] [NumberField K]

local instance heckeFourierThetaDecidableEq : DecidableEq (FinitePlace K) := Classical.decEq _

/-- The actual local Euler test dilated by `π_v ^ d(v)`, as a test function. -/
def dilatedEulerTest (χ : HeckeCharacter K) (d : FinitePlaceDivisor K) (v : FinitePlace K) :
    @SchwartzBruhat (FiniteCompletion K v) (topologicalData v).topology :=
  dilateTest (topologicalData v) (eulerTest (topologicalData v) (χ.finiteComponent v))
    (uniformizerUnit (topologicalData v) ^ d v)

/-- The theta coefficient is the unordered product of the dilated Euler tests. -/
theorem thetaCoeff_eq_finprod_dilatedEulerTest (χ : HeckeCharacter K)
    (d : FinitePlaceDivisor K) (γ : K) :
    thetaCoeff χ d γ =
      ∏ᶠ v : FinitePlace K, dilatedEulerTest χ d v (algebraMap K (FiniteCompletion K v) γ) :=
  rfl

section Fourier

variable
    (χ : HeckeCharacter K)
    (ψf : ∀ v : FinitePlace K,
      @UnitaryAdditiveCharacter (CompletionPadic.padicField v).Carrier _
        (topologicalData v).topology)
    (μ : ∀ v : FinitePlace K, SelfDualHaar (topologicalData v) (ψf v))

/-- The actual Fourier transform of the local Euler test. -/
def fourierEulerTest (v : FinitePlace K) (y : FiniteCompletion K v) : ℂ :=
  let := (topologicalData v).topology
  let := (topologicalData v).valuativeRel
  let := (topologicalData v).localField
  let := borel (FiniteCompletion K v)
  let : BorelSpace (FiniteCompletion K v) := ⟨rfl⟩
  HarmonicAnalysis.fourierTransform (ψf v) (μ v).val
    (eulerTest (topologicalData v) (χ.finiteComponent v)) y

/-- The local factor of the Fourier theta coefficient. -/
def fourierThetaFactor (d : FinitePlaceDivisor K) (μ' : K) (v : FinitePlace K) : ℂ :=
  ((topologicalData v).residueCardinality : ℂ) ^ d v *
    fourierEulerTest χ ψf μ v (algebraMap K (FiniteCompletion K v) μ' *
      ((uniformizerUnit (topologicalData v) ^ (-d v) : (FiniteCompletion K v)ˣ) :
        FiniteCompletion K v))

/-- The Fourier theta coefficient: the unordered product of the local factors. -/
def fourierThetaCoeff (d : FinitePlaceDivisor K) (μ' : K) : ℂ :=
  ∏ᶠ v : FinitePlace K, fourierThetaFactor χ ψf μ d μ' v

/-- The dual ideal-class factor of a finite divisor. -/
def dualClassFactor (d : FinitePlaceDivisor K) (s : ℂ) : ℂ :=
  ∏ v ∈ d.support, (((topologicalData v).residueCardinality : ℂ) *
    ((χ.finiteComponent v (uniformizerUnit (topologicalData v)) : ℂ))⁻¹ *
      spectralVariable (topologicalData v) s) ^ d v

/-- Each local factor is the actual Fourier transform of the dilated Euler test. -/
theorem fourierThetaFactor_eq_fourierTransform (d : FinitePlaceDivisor K) (μ' : K)
    (v : FinitePlace K) :
    fourierThetaFactor χ ψf μ d μ' v =
      (let := (topologicalData v).topology
       let := (topologicalData v).valuativeRel
       let := (topologicalData v).localField
       let := borel (FiniteCompletion K v)
       let : BorelSpace (FiniteCompletion K v) := ⟨rfl⟩
       HarmonicAnalysis.fourierTransform (ψf v) (μ v).val (dilatedEulerTest χ d v)
         (algebraMap K (FiniteCompletion K v) μ')) := by
  rw [dilatedEulerTest, fourierTransform_dilateTest_uniformizer]
  rfl

/-- The Fourier theta coefficient is the unordered product of the actual Fourier
transforms of the dilated Euler tests. -/
theorem fourierThetaCoeff_eq_finprod_fourierTransform (d : FinitePlaceDivisor K) (μ' : K) :
    fourierThetaCoeff χ ψf μ d μ' =
      ∏ᶠ v : FinitePlace K,
        (let := (topologicalData v).topology
         let := (topologicalData v).valuativeRel
         let := (topologicalData v).localField
         let := borel (FiniteCompletion K v)
         let : BorelSpace (FiniteCompletion K v) := ⟨rfl⟩
         HarmonicAnalysis.fourierTransform (ψf v) (μ v).val (dilatedEulerTest χ d v)
           (algebraMap K (FiniteCompletion K v) μ')) :=
  finprod_congr fun v => fourierThetaFactor_eq_fourierTransform χ ψf μ d μ' v

/-- At an unramified place of additive conductor zero the transformed Euler test is the
Euler test itself. -/
theorem fourierEulerTest_eq_eulerTest (v : FinitePlace K)
    (hχ : (topologicalData v).multiplicativeConductor (χ.finiteComponent v) = 0)
    (hψ : (topologicalData v).additiveConductor (ψf v) = 0) (y : FiniteCompletion K v) :
    fourierEulerTest χ ψf μ v y = eulerTest (topologicalData v) (χ.finiteComponent v) y := by
  let := (topologicalData v).topology
  let := (topologicalData v).valuativeRel
  let := (topologicalData v).localField
  let := borel (FiniteCompletion K v)
  let : BorelSpace (FiniteCompletion K v) := ⟨rfl⟩
  have hμ : ((μ v).val.measure (integerRing (topologicalData v))).toReal = 1 := by
    rw [HeckeFunctionalEquation.selfDualHaar_integerRing_eq_one
      (topologicalData v) (ψf v) (μ v) hψ, ENNReal.toReal_one]
  exact congrFun (fourier_eulerTest_eq_self (topologicalData v) (χ.finiteComponent v) hχ
    (ψf v) hψ (μ v).val hμ) y

variable (Sψ : Finset (FinitePlace K))
    (hψ : ∀ v ∉ Sψ, (topologicalData v).additiveConductor (ψf v) = 0)

include hψ

/-- Away from the ramified places, the additive conductor places and the support of `d`,
the Fourier theta factor is the Euler test at `μ'`. -/
theorem exists_finset_fourierThetaFactor_eq_eulerTest (d : FinitePlaceDivisor K) :
    ∃ S : Finset (FinitePlace K), ∀ v ∉ S, ∀ μ' : K,
      fourierThetaFactor χ ψf μ d μ' v =
        eulerTest (topologicalData v) (χ.finiteComponent v)
          (algebraMap K (FiniteCompletion K v) μ') ∧
      (topologicalData v).multiplicativeConductor (χ.finiteComponent v) = 0 := by
  obtain ⟨R, hR⟩ := exists_finset_conductor_eq_zero χ
  refine ⟨R ∪ Sψ ∪ d.support, fun v hv μ' => ?_⟩
  simp only [Finset.mem_union, not_or, Finsupp.mem_support_iff, not_not] at hv
  obtain ⟨⟨hvR, hvψ⟩, hvd⟩ := hv
  refine ⟨?_, hR v hvR⟩
  rw [fourierThetaFactor, hvd, neg_zero, zpow_zero, zpow_zero, Units.val_one, mul_one, one_mul,
    fourierEulerTest_eq_eulerTest χ ψf μ v (hR v hvR) (hψ v hvψ)]

/-- The Fourier theta factors are one outside an explicit finite set. -/
theorem exists_finset_fourierThetaFactor_eq_one (d : FinitePlaceDivisor K) (μ' : K) :
    ∃ S : Finset (FinitePlace K), ∀ v ∉ S, fourierThetaFactor χ ψf μ d μ' v = 1 := by
  obtain ⟨S, hS⟩ := exists_finset_fourierThetaFactor_eq_eulerTest χ ψf μ Sψ hψ d
  let N := (Hecke.finite_setOf_not_mem_additiveLattice_zero μ').toFinset
  refine ⟨S ∪ N, fun v hv => ?_⟩
  simp only [N, Finset.mem_union, not_or, Set.Finite.mem_toFinset, Set.mem_ofPred_eq,
    not_not] at hv
  obtain ⟨hvS, hvN⟩ := hv
  obtain ⟨h1, h2⟩ := hS v hvS μ'
  rw [h1]
  exact eulerTest_eq_one_of_mem _ _ h2 hvN

theorem mulSupport_fourierThetaFactor_finite (d : FinitePlaceDivisor K) (μ' : K) :
    (Function.mulSupport (fourierThetaFactor χ ψf μ d μ')).Finite := by
  obtain ⟨S, hS⟩ := exists_finset_fourierThetaFactor_eq_one χ ψf μ Sψ hψ d μ'
  exact S.finite_toSet.subset fun v hv => by
    by_contra h
    exact hv (hS v h)

omit hψ in
/-- The Fourier theta coefficient is the finite product over any set outside which its
factors are one. -/
theorem fourierThetaCoeff_eq_prod (d : FinitePlaceDivisor K) (μ' : K)
    (S : Finset (FinitePlace K)) (hS : ∀ v ∉ S, fourierThetaFactor χ ψf μ d μ' v = 1) :
    fourierThetaCoeff χ ψf μ d μ' = ∏ v ∈ S, fourierThetaFactor χ ψf μ d μ' v :=
  finprod_eq_prod_of_mulSupport_subset _ fun v hv => by
    by_contra h
    exact hv (hS v h)

/-- Nonzero Fourier theta coefficients are supported on the lattice ideal of the divisor
`n + a - d`, where `n` and `a` are the additive and multiplicative conductors. -/
theorem exists_fourierThetaCoeff_support (d : FinitePlaceDivisor K) :
    ∃ e : FinitePlaceDivisor K,
      (∀ v, e v = (topologicalData v).additiveConductor (ψf v) +
        ((topologicalData v).multiplicativeConductor (χ.finiteComponent v) : ℤ) - d v) ∧
      ∀ μ' : K, fourierThetaCoeff χ ψf μ d μ' ≠ 0 →
        μ' ∈ (Hecke.latticeIdeal e : FractionalIdeal (𝓞 K)⁰ K) := by
  obtain ⟨R, hR⟩ := exists_finset_conductor_eq_zero χ
  let f : FinitePlace K → ℤ := fun v => (topologicalData v).additiveConductor (ψf v) +
    ((topologicalData v).multiplicativeConductor (χ.finiteComponent v) : ℤ) - d v
  have hf : (Function.support f).Finite := by
    refine ((R ∪ Sψ ∪ d.support : Finset (FinitePlace K)) : Set (FinitePlace K)).toFinite.subset
      fun v hv => ?_
    by_contra h
    simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe, Finsupp.mem_support_iff,
      not_or, not_not] at h
    obtain ⟨⟨hvR, hvψ⟩, hvd⟩ := h
    exact hv (by simp only [f, hR v hvR, hψ v hvψ, hvd, Nat.cast_zero, add_zero, sub_zero])
  refine ⟨Finsupp.ofSupportFinite f hf, fun v => rfl, fun μ' h => ?_⟩
  obtain ⟨S, hS⟩ := exists_finset_fourierThetaFactor_eq_one χ ψf μ Sψ hψ d μ'
  rw [fourierThetaCoeff_eq_prod χ ψf μ d μ' S hS] at h
  rw [Hecke.mem_latticeIdeal_iff_forall_mem]
  intro v
  have hv : fourierThetaFactor χ ψf μ d μ' v ≠ 0 := by
    by_cases hvS : v ∈ S
    · exact Finset.prod_ne_zero_iff.mp h v hvS
    · rw [hS v hvS]
      exact one_ne_zero
  have hmem := mem_additiveLattice_of_fourierTransform_eulerTest_ne_zero _ _ _ _
    (right_ne_zero_of_mul hv)
  have hπ : ((uniformizerUnit (topologicalData v) ^ d v : (FiniteCompletion K v)ˣ) :
      FiniteCompletion K v) ∈ (topologicalData v).additiveLattice (-d v) :=
    (uniformizer_pow_mem_additiveLattice _ (-d v) (d v)).mpr (by rw [neg_neg])
  have hprod := Hecke.mul_mem_additiveLattice v hmem hπ
  rw [mul_assoc, ← Units.val_mul, ← zpow_add, neg_add_cancel, zpow_zero,
    Units.val_one, mul_one, ← sub_eq_add_neg] at hprod
  exact hprod

/-- The Fourier theta coefficients are uniformly bounded. -/
theorem exists_norm_fourierThetaCoeff_le (d : FinitePlaceDivisor K) :
    ∃ C : ℝ, ∀ μ' : K, ‖fourierThetaCoeff χ ψf μ d μ'‖ ≤ C := by
  obtain ⟨S₀, hS₀⟩ := exists_finset_fourierThetaFactor_eq_eulerTest χ ψf μ Sψ hψ d
  let B : FinitePlace K → ℝ := fun v =>
    if v ∈ S₀ then max (((topologicalData v).residueCardinality : ℝ) ^ d v *
      (letI := (topologicalData v).topology; letI := borel (FiniteCompletion K v);
        ((μ v).val.measure (integerRing (topologicalData v))).toReal)) 1 else 1
  refine ⟨∏ v ∈ S₀, B v, fun μ' => ?_⟩
  obtain ⟨S₁, hS₁⟩ := exists_finset_fourierThetaFactor_eq_one χ ψf μ Sψ hψ d μ'
  have hsub : S₀ ⊆ S₀ ∪ S₁ := Finset.subset_union_left
  rw [fourierThetaCoeff_eq_prod χ ψf μ d μ' (S₀ ∪ S₁)
      (fun v hv => hS₁ v (fun h => hv (Finset.mem_union_right _ h))),
    norm_prod, Finset.prod_subset hsub (f := B) (fun v _ hv => by simp only [B, ite_eq_right hv])]
  refine Finset.prod_le_prod₀ (fun v _ => norm_nonneg _) (fun v _ => ?_)
  by_cases hv : v ∈ S₀
  · simp only [B, ite_eq_left hv]
    refine le_trans ?_ (le_max_left _ _)
    let := (topologicalData v).topology
    let := (topologicalData v).valuativeRel
    let := (topologicalData v).localField
    let := borel (FiniteCompletion K v)
    let : BorelSpace (FiniteCompletion K v) := ⟨rfl⟩
    rw [fourierThetaFactor, norm_mul, norm_zpow, Complex.norm_natCast]
    exact mul_le_mul_of_nonneg_left
      (norm_fourierTransform_eulerTest_le (topologicalData v) (χ.finiteComponent v) (ψf v)
        (μ v).val _)
      (zpow_nonneg (Nat.cast_nonneg _) _)
  · simp only [B, ite_eq_right hv]
    rw [(hS₀ v hv μ').1]
    exact norm_eulerTest_le_one _ _ _

omit hψ in
/-- A global integral unit multiplies each Fourier theta factor by its local character value. -/
theorem fourierThetaFactor_unit_mul (d : FinitePlaceDivisor K) (u : (𝓞 K)ˣ) (μ' : K)
    (v : FinitePlace K) :
    fourierThetaFactor χ ψf μ d ((u : 𝓞 K) * μ') v =
      (χ.finiteComponent v (localUnit v (Units.map (algebraMap (𝓞 K) K : 𝓞 K →* K) u)) :
        ℂ) * fourierThetaFactor χ ψf μ d μ' v := by
  have hw : (topologicalData v).ord ((localUnit v
      (Units.map (algebraMap (𝓞 K) K : 𝓞 K →* K) u) : (FiniteCompletion K v)ˣ) :
        FiniteCompletion K v) = 0 := by
    rw [ord_localUnit, principalDivisor_units_map, Finsupp.coe_zero, Pi.zero_apply]
  rw [fourierThetaFactor, fourierThetaFactor, show
      algebraMap K (FiniteCompletion K v) ((u : 𝓞 K) * μ') *
        ((uniformizerUnit (topologicalData v) ^ (-d v) : (FiniteCompletion K v)ˣ) :
          FiniteCompletion K v) =
      (algebraMap K (FiniteCompletion K v) μ' *
        ((uniformizerUnit (topologicalData v) ^ (-d v) : (FiniteCompletion K v)ˣ) :
          FiniteCompletion K v)) *
        ((localUnit v (Units.map (algebraMap (𝓞 K) K : 𝓞 K →* K) u) :
          (FiniteCompletion K v)ˣ) : FiniteCompletion K v) by
      rw [localUnit_val, map_mul]
      simp only [Units.coe_map, MonoidHom.coe_coe]
      ring]
  rw [fourierEulerTest, fourierEulerTest, fourier_eulerTest_mul_integralUnit _ _ _ _ _ hw]
  ring

omit hψ in
/-- The actual Fourier shell weight at the order of a unit is computed at that unit. -/
theorem fourierShellWeight_ord (v : FinitePlace K) (s : ℂ) (x : (FiniteCompletion K v)ˣ) :
    fourierShellWeight χ ψf μ v s ((topologicalData v).ord (x : FiniteCompletion K v)) =
      fourierEulerTest χ ψf μ v x * ((χ.finiteComponent v x : ℂ))⁻¹ *
        spectralVariable (topologicalData v) s ^
          (topologicalData v).ord (x : FiniteCompletion K v) := by
  let := (topologicalData v).topology
  let := (topologicalData v).valuativeRel
  let := (topologicalData v).localField
  let := borel (FiniteCompletion K v)
  let : BorelSpace (FiniteCompletion K v) := ⟨rfl⟩
  have h := shellMellinTerm_ord_of_covariant (topologicalData v) (fourierEulerTest χ ψf μ v)
    (χ.finiteComponent v)⁻¹ (fun y w hw => by
      show _ = (((χ.finiteComponent v w)⁻¹ : ℂˣ) : ℂ)⁻¹ * _
      rw [Units.val_inv_eq_inv_val, inv_inv]
      exact fourier_eulerTest_mul_integralUnit _ _ _ _ w hw y) s x
  change _ = _ * (((χ.finiteComponent v x)⁻¹ : ℂˣ) : ℂ) * _ at h
  rw [Units.val_inv_eq_inv_val] at h
  exact h

omit hψ in
private theorem fourier_coefficient_algebra (q G A P Q : ℂ) (hP : P ≠ 0) (hQ : Q ≠ 0)
    (m d : ℤ) :
    q ^ d * G * A⁻¹ * Q ^ m = G * (A * P ^ (-d))⁻¹ * Q ^ (m - d) * (q * P⁻¹ * Q) ^ d := by
  have hPd : P ^ d ≠ 0 := zpow_ne_zero d hP
  have hQd : Q ^ d ≠ 0 := zpow_ne_zero d hQ
  rw [zpow_neg, mul_inv, inv_inv, zpow_sub₀ hQ, mul_zpow, mul_zpow, inv_zpow, div_eq_mul_inv]
  calc q ^ d * G * A⁻¹ * Q ^ m =
        q ^ d * G * A⁻¹ * Q ^ m * (P ^ d * (P ^ d)⁻¹) * (Q ^ d * (Q ^ d)⁻¹) := by
          rw [mul_inv_cancel₀ hPd, mul_inv_cancel₀ hQd, mul_one, mul_one]
    _ = _ := by ring

omit hψ in
/-- The dual class factor at `1 - s` inverts the class factor at `s`. -/
theorem dualClassFactor_one_sub_mul_classFactor (d : FinitePlaceDivisor K) (s : ℂ) :
    dualClassFactor χ d (1 - s) * classFactor χ d s = 1 := by
  rw [dualClassFactor, classFactor, ← Finset.prod_mul_distrib]
  refine Finset.prod_eq_one fun v _ => ?_
  have hq : ((topologicalData v).residueCardinality : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (zero_lt_one.trans (topologicalData v).residueCardinality_gt_one).ne'
  have hP : (χ.finiteComponent v (uniformizerUnit (topologicalData v)) : ℂ) ≠ 0 :=
    Units.ne_zero _
  have hQ := spectralVariable_ne_zero (topologicalData v) s
  rw [← mul_zpow, spectralVariable_one_sub, Complex.ofReal_natCast]
  convert one_zpow (d v) using 2
  calc _ = (((topologicalData v).residueCardinality : ℂ) *
          ((topologicalData v).residueCardinality : ℂ)⁻¹) *
        (((χ.finiteComponent v (uniformizerUnit (topologicalData v)) : ℂ))⁻¹ *
          (χ.finiteComponent v (uniformizerUnit (topologicalData v)) : ℂ)) *
        ((spectralVariable (topologicalData v) s)⁻¹ * spectralVariable (topologicalData v) s) := by
          ring
    _ = 1 := by
      rw [mul_inv_cancel₀ hq, inv_mul_cancel₀ hP, inv_mul_cancel₀ hQ, mul_one, mul_one]

section Mixed

variable
    (dR : {v : InfinitePlace K // v.IsReal} → RealCharacterData)
    (hR : ∀ v, IsRealCharacterPresentation v.2 (χ.infiniteComponent v.1) (dR v))
    (dC : {v : InfinitePlace K // v.IsComplex} → ComplexCharacterData)
    (hC : ∀ v, IsComplexCharacterPresentation v.2 (χ.infiniteComponent v.1) (dC v))

include hR hC

/-- Unit equivariance of the Fourier theta coefficients. -/
theorem fourierThetaCoeff_unit_mul (d : FinitePlaceDivisor K) (u : (𝓞 K)ˣ) (μ' : K) :
    fourierThetaCoeff χ ψf μ d ((u : 𝓞 K) * μ') =
      (Hecke.mixedCharFun (fun v => (dR v).parity) (fun v => (dR v).exponent)
        (fun v => (dC v).weight) (fun v => (dC v).exponent)
        (mixedEmbedding K ((u : 𝓞 K) : K)))⁻¹ * fourierThetaCoeff χ ψf μ d μ' := by
  let a : Kˣ := Units.map (algebraMap (𝓞 K) K : 𝓞 K →* K) u
  obtain ⟨Sθ, hSθ⟩ := exists_finset_fourierThetaFactor_eq_one χ ψf μ Sψ hψ d μ'
  obtain ⟨Sχ, -, hSχ⟩ := exists_finset_finiteComponent_localUnit_eq_one χ a
  let S : Finset (FinitePlace K) := Sθ ∪ Sχ
  have hθ : ∀ v ∉ S, fourierThetaFactor χ ψf μ d μ' v = 1 := fun v hv =>
    hSθ v (fun h => hv (Finset.mem_union_left _ h))
  have hχ1 : ∀ v ∉ S, χ.finiteComponent v (localUnit v a) = 1 := fun v hv =>
    hSχ v (fun h => hv (Finset.mem_union_right _ h))
  have hθu : ∀ v ∉ S, fourierThetaFactor χ ψf μ d ((u : 𝓞 K) * μ') v = 1 := fun v hv => by
    rw [fourierThetaFactor_unit_mul, hθ v hv, hχ1 v hv, Units.val_one, mul_one]
  have hprod := finprod_finiteComponent_localUnit χ dR hR dC hC a
  rw [finprod_eq_prod_of_mulSupport_subset _ (s := S) (fun v hv => by
    by_contra hvS
    exact hv (by dsimp only; rw [hχ1 v hvS, Units.val_one]))] at hprod
  rw [fourierThetaCoeff_eq_prod χ ψf μ d _ S hθu, fourierThetaCoeff_eq_prod χ ψf μ d μ' S hθ]
  simp only [fourierThetaFactor_unit_mul]
  rw [Finset.prod_mul_distrib, hprod]
  rfl

/-- The Fourier theta coefficient, multiplied by the mixed character and the complex norm
power, is the actual Fourier divisor Euler coefficient at `principalDivisor μ' - d` times
the dual class factor. -/
theorem fourierThetaCoeff_mul_eq_coefficient (d : FinitePlaceDivisor K) (μ' : Kˣ) (s : ℂ)
    (S : Finset (FinitePlace K)) (hS : ∀ v ∉ S, fourierShellWeight χ ψf μ v s 0 = 1) :
    fourierThetaCoeff χ ψf μ d μ' *
        Hecke.mixedCharFun (fun v => (dR v).parity) (fun v => (dR v).exponent)
          (fun v => (dC v).weight) (fun v => (dC v).exponent) (mixedEmbedding K (μ' : K)) *
        ((mixedEmbedding.norm (mixedEmbedding K (μ' : K)) : ℝ) : ℂ) ^ (-s) =
      DivisorEulerProduct.coefficient S (fun v => fourierShellWeight χ ψf μ v s)
          (principalDivisor μ' - d) * dualClassFactor χ d s := by
  obtain ⟨Sθ, hSθ⟩ := exists_finset_fourierThetaFactor_eq_one χ ψf μ Sψ hψ d μ'
  obtain ⟨Sχ, hpd, hSχ⟩ := exists_finset_finiteComponent_localUnit_eq_one χ μ'
  let S' : Finset (FinitePlace K) := Sθ ∪ Sχ ∪ d.support ∪ S
  have hθS : Sθ ⊆ S' :=
    Finset.subset_union_left.trans (Finset.subset_union_left.trans Finset.subset_union_left)
  have hχS : Sχ ⊆ S' :=
    Finset.subset_union_right.trans (Finset.subset_union_left.trans Finset.subset_union_left)
  have hdS : d.support ⊆ S' := Finset.subset_union_right.trans Finset.subset_union_left
  have hSS : S ⊆ S' := Finset.subset_union_right
  have hθ : ∀ v ∉ S', fourierThetaFactor χ ψf μ d μ' v = 1 := fun v hv =>
    hSθ v (fun h => hv (hθS h))
  have hprod := finprod_finiteComponent_localUnit χ dR hR dC hC μ'
  rw [finprod_eq_prod_of_mulSupport_subset _ (s := S') (fun v hv => by
    by_contra hvS
    exact hv (by dsimp only; rw [hSχ v (fun h => hvS (hχS h)), Units.val_one]))] at hprod
  have hmix : Hecke.mixedCharFun (fun v => (dR v).parity) (fun v => (dR v).exponent)
      (fun v => (dC v).weight) (fun v => (dC v).exponent) (mixedEmbedding K (μ' : K)) =
      ∏ v ∈ S', ((χ.finiteComponent v (localUnit v μ') : ℂ))⁻¹ := by
    rw [Finset.prod_inv_distrib, hprod, inv_inv]
  have he : (principalDivisor μ' - d).support ⊆ S' := Finsupp.support_sub.trans
    (Finset.union_subset (hpd.trans hχS) hdS)
  rw [fourierThetaCoeff_eq_prod χ ψf μ d μ' S' hθ, hmix,
    mixedNorm_cpow_eq_prod μ' s S' (hpd.trans hχS), dualClassFactor,
    Finset.prod_subset hdS (fun v _ hv => by rw [Finsupp.notMem_support_iff.mp hv, zpow_zero]),
    DivisorEulerProduct.coefficient,
    Finset.prod_subset (Finset.union_subset hSS he) (fun v _ hv => by
      rw [Finset.mem_union, not_or, Finsupp.mem_support_iff, not_not] at hv
      rw [hv.2]
      exact hS v hv.1),
    ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun v _ => ?_
  have hx : (topologicalData v).ord ((localUnit v μ' *
      uniformizerUnit (topologicalData v) ^ (-d v) : (FiniteCompletion K v)ˣ) :
        FiniteCompletion K v) = (principalDivisor μ' - d) v := by
    rw [Units.val_mul, (topologicalData v).ord_mul (Units.ne_zero _) (Units.ne_zero _),
      ord_localUnit, ord_uniformizerUnit_zpow, Finsupp.sub_apply, sub_eq_add_neg]
  have hloc := fourierShellWeight_ord χ ψf μ v s
    (localUnit v μ' * uniformizerUnit (topologicalData v) ^ (-d v))
  rw [hx] at hloc
  rw [hloc, fourierThetaFactor, map_mul, map_zpow, Units.val_mul, Units.val_mul, localUnit_val,
    Finsupp.sub_apply]
  simp only [Units.val_zpow_eq_zpow_val]
  exact fourier_coefficient_algebra _ _ _ _ _ (Units.ne_zero _)
    (spectralVariable_ne_zero (topologicalData v) s) _ _

end Mixed

end Fourier

end Langlands.Global.HeckeTheta
