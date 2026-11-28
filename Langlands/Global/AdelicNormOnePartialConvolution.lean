import Langlands.Automorphic.GroupSchemeCuspidalConvolutionCompact
import Langlands.GroupScheme.Absolute.ParabolicDynamicProof

/-! # Norm-one partial convolutions of functions on the positive rational quotient -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory Filter
open scoped CategoryTheory.MonObj CompactlySupported

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints
  PositiveRealTorus RepresentationGrowth

variable {F : Type u} [Field F] [NumberField F] {H : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine H.X.left] [LocallyOfFiniteType H.X.hom]
  (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ H)

local notation "A" => AdelicGroupPoints F H
local notation "A₁" => normOneSubgroup F H
local notation "Q" => PositiveRationalQuotient F H T i
local notation "q" => LeftCosetSpace.mk (positiveRationalSubgroup F H T i)

/-- The convolution `y ↦ ∫_{H(𝔸)¹} conj K(n⁻¹ y) h(n) dn` over the norm-one subgroup of a
function `h` on the positive rational quotient, read at norm-one representatives. -/
def normOnePartialConvolution (K : A → ℂ) (h : Q → ℂ) (y : A) : ℂ :=
  ∫ n : A₁, starRingEnd ℂ (K ((n : A)⁻¹ * y)) * h (q n.val) ∂Measure.haar

/-- Partial convolutions are left invariant under rational points. -/
theorem normOnePartialConvolution_rational_mul (K : A → ℂ) (h : Q → ℂ)
    (r : RationalGroupPoints F H) (y : A) :
    normOnePartialConvolution T i K h (rational F H r * y) =
      normOnePartialConvolution T i K h y := by
  unfold normOnePartialConvolution
  let ρ : A₁ := rationalNormOne F H r
  rw [← integral_mul_left_eq_self _ ρ]
  congr 1
  funext n
  have hmk : q ((ρ * n : A₁) : A) = q (n : A) := by
    have hρ : (ρ : A) ∈ positiveRationalSubgroup F H T i :=
      rationalSubgroup_le_positiveRationalSubgroup F H T i ⟨r, rfl⟩
    exact LeftCosetSpace.mk_subgroup_mul _ ⟨_, hρ⟩ _
  rw [hmk]
  have harg : ((ρ * n : A₁) : A)⁻¹ * (rational F H r * y) = (n : A)⁻¹ * y := by
    change ((ρ : A) * (n : A))⁻¹ * (rational F H r * y) = (n : A)⁻¹ * y
    rw [mul_inv_rev, mul_assoc, ← mul_assoc ((ρ : A)⁻¹)]
    simp [ρ]
  rw [harg]

/-- Right translation of the argument is right translation of the kernel. -/
theorem normOnePartialConvolution_mul_right (K : A → ℂ) (h : Q → ℂ) (y x : A) :
    normOnePartialConvolution T i K h (y * x) =
      normOnePartialConvolution T i (fun z => K (z * x)) h y := by
  unfold normOnePartialConvolution
  simp only [mul_assoc]

section Smoothing

variable (hi : Function.Injective (characterRestrict i)) [(characterRestrict i).range.FiniteIndex]
  (I : Type u) [Fintype I] (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of F)) I)
  (hc : IsCentral i)

local notation "Γ" => positiveRationalSubgroup F H T i
local notation "dq" => positiveRationalQuotientHaarMeasure F H T i
local notation "dg" => (Measure.haar : Measure A)
local notation "dΓ" => positiveRationalSubgroupHaarMeasure F H T i hi I e hc
local notation "V" => Lp ℂ 2 dq

variable [(Measure.haar : Measure (normOneSubgroup F H)).IsMulRightInvariant]

include hi e hc in
/-- Smoothing a quotient `L²` class by a compactly supported continuous kernel gives a
continuous function on the adelic group. -/
theorem continuous_positiveQuotientLpSmoothing (κ : C_c(A, ℂ)) (v : V) :
    Continuous (positiveQuotientLpSmoothing T i κ v) := by
  let := positiveRationalQuotient_borelSpace F H T i hi I e hc
  let := positiveRationalQuotientHaarMeasure_isLocallyFiniteMeasure F H T i hi I e hc
  let := positiveRationalSubgroupHaarMeasure_isHaarMeasure F H T i hi I e hc
  let := positiveRationalSubgroupHaarMeasure_sigmaFinite F H T i hi I e hc
  let := positiveRationalSubgroupHaarMeasure_isMulRightInvariant F H T i hi I e hc
  obtain ⟨w, hw, hk, -⟩ := Langlands.QuotientIntegration.quotientConvolutionKernel Γ
    (isClosed_positiveRationalSubgroup F H T i hi I e hc) dΓ dg dq
    (positiveRationalQuotientHaarMeasure_isCompatible F H T i hi I e hc) κ
  have hEq : positiveQuotientLpSmoothing T i κ v = fun x => inner ℂ (w x) v :=
    funext fun x => ((hk x v).2).symm
  rw [hEq]
  exact hw.inner continuous_const

variable (hG : IsConnectedReductive H)

include hi e hc in
/-- Smoothings of full almost-everywhere cuspidal classes by compactly supported continuous
kernels have vanishing constant terms along all proper parabolics at every point. -/
theorem hasZeroProperParabolicConstantTerms_positiveQuotientLpSmoothing (κ : C_c(A, ℂ))
    (v : V) (hv : v ∈ fullAEL2CuspidalSubmodule F H parabolicDynamic hG T i hi I e hc) :
    HasZeroProperParabolicConstantTerms (positiveQuotientLpSmoothing T i κ v) := by
  let := positiveRationalQuotient_borelSpace F H T i hi I e hc
  let := hG.isAffineHom
  have hκI : Integrable (κ : A → ℂ) dg := κ.continuous.integrable_of_hasCompactSupport
    κ.hasCompactSupport
  let f := positiveQuotientLpSmoothing T i κ v
  have hInv' := positiveQuotientLpSmoothing_invariant T i (κ : A → ℂ) v
  let φ : C(Q, ℂ) := ⟨LeftCosetSpace.lift Γ f hInv',
    LeftCosetSpace.continuous_lift Γ _ _ (continuous_positiveQuotientLpSmoothing T i hi I e hc κ v)⟩
  have hφAE : (haarQuotientL2IntegratedAction F H T i hi I e hc dg κ hκI v : Q → ℂ) =ᵐ[dq] φ :=
    positiveQuotientLpSmoothing_ae_eq T i hi I e hc κ hκI v
  have hmem := haarQuotientL2IntegratedAction_mem_fullAEL2CuspidalSubmodule F H parabolicDynamic
    hG T i hi I e hc dg κ hκI v hv
  have hφCus := (groupSchemeFullAEL2ContinuousCuspidality F H parabolicDynamic hG T i hi I e hc
    φ _ hφAE).mp hmem
  exact hasZeroProperParabolicConstantTerms_of_normalized parabolicDynamic hG _ hφCus

local notation "Pos" => intrinsicSubgroup F T
local notation "νP" => normalizedPositiveHaarMeasure F H T i hi I e hc
local notation "πP" => positiveFactor F H T i hi I e
local notation "π₁" => normOneFactor F H T i hi I e
local notation "ι₀" => positivePointMap F H T i

/-- The kernel `a ↦ ρ(a_+) conj K(a₁⁻¹)` on `H(𝔸) = H(𝔸)^+ × H(𝔸)¹`, whose smoothing
reproduces norm-one partial convolutions at norm-one points. -/
def normOneSmoothingKernel (K : C_c(A, ℂ)) (ρ : C_c(Pos, ℂ)) : C_c(A, ℂ) where
  toFun a := ρ (πP a) * starRingEnd ℂ (K ((π₁ a : A)⁻¹))
  continuous_toFun := (ρ.continuous.comp (positiveFactor F H T i hi I e).continuous).mul
    (continuous_star.comp (K.continuous.comp
      (continuous_subtype_val.comp (continuous_normOneFactor F H T i hi I e)).inv))
  hasCompactSupport' := by
    let C : Set A₁ := {n | (n : A)⁻¹ ∈ tsupport K}
    have hC : IsCompact C := by
      have hemb : Topology.IsClosedEmbedding (fun n : A₁ => (n : A)⁻¹) :=
        (Homeomorph.inv A).isClosedEmbedding.comp
          (isClosed_normOneSubgroup F H).isClosedEmbedding_subtypeVal
      exact hemb.isCompact_preimage K.hasCompactSupport
    have hS : IsCompact (normOneDecomposition F H T i hi I e '' (tsupport ρ ×ˢ C)) :=
      (ρ.hasCompactSupport.prod hC).image (normOneDecomposition F H T i hi I e).continuous
    refine HasCompactSupport.intro hS fun a ha => ?_
    have hdec := positivePointMap_mul_normOneFactor F H T i hi I e a
    by_cases hρ : πP a ∈ tsupport ρ
    · by_cases hK : (π₁ a : A)⁻¹ ∈ tsupport K
      · exact absurd ⟨(πP a, π₁ a), ⟨hρ, hK⟩, hdec⟩ ha
      · change ρ (πP a) * starRingEnd ℂ (K ((π₁ a : A)⁻¹)) = 0
        rw [image_eq_zero_of_notMem_tsupport hK, map_zero, mul_zero]
    · change ρ (πP a) * starRingEnd ℂ (K ((π₁ a : A)⁻¹)) = 0
      rw [image_eq_zero_of_notMem_tsupport hρ, zero_mul]

omit [(Measure.haar : Measure (normOneSubgroup F H)).IsMulRightInvariant] in
include hi e hc in
/-- On norm-one points, smoothing by `normOneSmoothingKernel K ρ` is the norm-one partial
convolution with `K`, multiplied by the integral of `ρ`. -/
theorem positiveQuotientLpSmoothing_normOneSmoothingKernel (K : C_c(A, ℂ)) (ρ : C_c(Pos, ℂ))
    (h : V) (x : A₁) :
    positiveQuotientLpSmoothing T i (normOneSmoothingKernel T i hi I e K ρ) h x =
      (∫ b, ρ b ∂νP) * normOnePartialConvolution T i K h x := by
  let := positiveIsTopologicalGroup F T I e
  let := positiveLocallyCompactSpace F T I e
  let := positiveSecondCountableTopology F T I e
  unfold positiveQuotientLpSmoothing rightConvolution
  have hmp := measurePreserving_normOneDecomposition F H T i hi I e hc
  rw [← hmp.integral_comp (normOneDecomposition F H T i hi I e).measurableEmbedding]
  have hpt : ∀ p : Pos × A₁,
      normOneSmoothingKernel T i hi I e K ρ (normOneDecomposition F H T i hi I e p) *
          (h : Q → ℂ) (q ((x : A) * normOneDecomposition F H T i hi I e p)) =
        ρ p.1 * (starRingEnd ℂ (K ((p.2 : A)⁻¹)) * (h : Q → ℂ) (q ((x : A) * p.2))) := by
    rintro ⟨b, n⟩
    simp only [normOneDecomposition_apply]
    have h1 : πP (ι₀ b * n) = b := positiveFactor_mul_normOne F H T i hi I e b n
    have h2 : (π₁ (ι₀ b * n) : A) = n := by
      rw [normOneFactor_val, h1, inv_mul_cancel_left]
    have h3 : q ((x : A) * (ι₀ b * n)) = q ((x : A) * n) := by
      rw [← mul_assoc, ← (positivePointMap_commute F H T i hc b (x : A)).eq, mul_assoc]
      exact LeftCosetSpace.mk_subgroup_mul _
        ⟨_, imageSubgroup_le_positiveRationalSubgroup F H T i ⟨b.val, b.property, rfl⟩⟩ _
    change ρ (πP (ι₀ b * n)) * starRingEnd ℂ (K ((π₁ (ι₀ b * n) : A)⁻¹)) * _ = _
    rw [h1, h2, h3, mul_assoc]
  simp only [Function.comp_apply]
  simp_rw [hpt]
  let := normalizedPositiveHaarMeasure_sigmaFinite F H T i hi I e hc
  rw [integral_prod_mul (fun b => ρ b)
    (fun n : A₁ => starRingEnd ℂ (K ((n : A)⁻¹)) * (h : Q → ℂ) (q ((x : A) * n)))]
  congr 1
  unfold normOnePartialConvolution
  conv_rhs => rw [← integral_mul_left_eq_self _ x]
  congr 1
  funext n
  simp only [Subgroup.coe_mul, mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one]

include hi e hc in
/-- Norm-one partial convolutions of full almost-everywhere cuspidal classes have vanishing
constant terms along all proper parabolics at every point. -/
theorem hasZeroProperParabolicConstantTerms_normOnePartialConvolution (K : C_c(A, ℂ)) (h : V)
    (hv : h ∈ fullAEL2CuspidalSubmodule F H parabolicDynamic hG T i hi I e hc) :
    HasZeroProperParabolicConstantTerms (normOnePartialConvolution T i K h) := by
  let := positiveIsTopologicalGroup F T I e
  let := positiveLocallyCompactSpace F T I e
  let := positiveSecondCountableTopology F T I e
  let := normalizedPositiveHaarMeasure_isHaarMeasure F H T i hi I e hc
  obtain ⟨f₀, hf₀c, hf₀n, hf₀1⟩ := exists_continuous_nonneg_pos (1 : Pos)
  let ρ : C_c(Pos, ℂ) := ⟨⟨fun b => (f₀ b : ℂ), Complex.continuous_ofReal.comp f₀.continuous⟩,
    hf₀c.comp_left Complex.ofReal_zero⟩
  have hρ : (∫ b, ρ b ∂νP) ≠ 0 := by
    have hpos : 0 < ∫ b, f₀ b ∂νP :=
      f₀.continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero hf₀c hf₀n hf₀1
    change (∫ b, ((f₀ b : ℝ) : ℂ) ∂νP) ≠ 0
    rw [integral_complex_ofReal]
    exact_mod_cast hpos.ne'
  intro P U p r _ _ hp hr hprop
  funext y
  set c : A := ι₀ (πP y) with hcdef
  set y₁ : A₁ := π₁ y with hy₁def
  have hy : y = (y₁ : A) * c := by
    rw [hcdef, ← (positivePointMap_commute F H T i hc (πP y) (y₁ : A)).eq]
    exact (positivePointMap_mul_normOneFactor F H T i hi I e y).symm
  let Kc : C_c(A, ℂ) := ⟨⟨fun z => K (z * c), K.continuous.comp (continuous_id.mul continuous_const)⟩,
    K.hasCompactSupport.comp_homeomorph (Homeomorph.mulRight c)⟩
  have hsm := hasZeroProperParabolicConstantTerms_positiveQuotientLpSmoothing T i hi I e hc hG
    (normOneSmoothingKernel T i hi I e Kc ρ) h hv P U p r hp hr hprop
  have : CompactSpace (AdelicSubgroupPoints.RationalQuotient F H
      (SubgroupFunctor.range (r ≫ p))) :=
    AdelicSubgroupPoints.compactSpace_rationalQuotient_range_unipotent F (r ≫ p)
      hr.1.smooth hr.1.connectedSpace hr.1.isUnipotent
  have key : ∀ u ∈ AdelicSubgroupPoints.adelicPoints F H (SubgroupFunctor.range (r ≫ p)),
      normOnePartialConvolution T i K h (u * y) = (∫ b, ρ b ∂νP)⁻¹ *
        positiveQuotientLpSmoothing T i (normOneSmoothingKernel T i hi I e Kc ρ) h
          (u * (y₁ : A)) := by
    intro u hu
    have hu1 : u ∈ normOneSubgroup F H :=
      AdelicSubgroupPoints.adelicPoints_le_normOneSubgroup F H _ hu
    have hcmp := positiveQuotientLpSmoothing_normOneSmoothingKernel T i hi I e hc Kc ρ h
      ⟨u * (y₁ : A), (normOneSubgroup F H).mul_mem hu1 y₁.2⟩
    change _ = _ * positiveQuotientLpSmoothing T i (normOneSmoothingKernel T i hi I e Kc ρ) h
      ((⟨u * (y₁ : A), (normOneSubgroup F H).mul_mem hu1 y₁.2⟩ : A₁) : A)
    rw [hcmp, inv_mul_cancel_left₀ hρ, hy, ← mul_assoc, normOnePartialConvolution_mul_right]
    rfl
  have h0 := congrFun hsm (y₁ : A)
  unfold subgroupConstantTerm at h0 ⊢
  rw [Pi.zero_apply] at h0 ⊢
  rw [integral_congr_ae (Eventually.of_forall fun x => key _ (Quotient.out x).2),
    integral_const_mul, h0, mul_zero]

end Smoothing

end Langlands.Global
