import Langlands.Global.AdelicWeightedConvolutionEstimate
import Langlands.Global.AdelicWeightedSiegelSpace

/-! # Weighted pointwise adelic convolution -/

noncomputable section

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory MeasureTheory NumberField Set
open scoped CategoryTheory.MonObj ENNReal

namespace Langlands.Global

open AdelicGroupPoints

namespace WeightedSiegel

variable (F : Type u) [Field F] [NumberField F]
  {G P : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine G.X.left] [IsAffine P.X.left]
  (p : P ⟶ G) [IsClosedImmersion p.hom.hom.left]
  {K : Subgroup (AdelicGroupPoints F G)} (hK : AdelicGroupPoints.IsIwasawaCompact p K)

/-- The exponential weight on the ambient group, restricted to the preimage of a height set. -/
def chamberDensity (ell : RealCharacterDual F P → ℝ) (S : Set (RealCharacterDual F P)) :
    AdelicGroupPoints F G → ℝ≥0∞ :=
  (hK.height ⁻¹' S).indicator (fun g => ENNReal.ofReal (Real.exp (-2 * ell (hK.height g))))

variable [LocallyOfFiniteType G.X.hom]

/-- Integrate over the chosen fundamental domain using the ambient chamber density. -/
theorem lintegral_domainMeasure_eq_chamberDensity
    (ell : RealCharacterDual F P → ℝ) (hell : Continuous ell)
    (S : Set (RealCharacterDual F P)) (hS : @MeasurableSet _ (borel _) S)
    {φ : DomainQuotient F p → ℝ≥0∞} (hφ : Measurable φ) :
    ∫⁻ z, φ z ∂domainMeasure F p hK ell (domainHeight F p hK ⁻¹' S) =
      ∫⁻ g in LeftCosetSpace.fundamentalDomain (parabolicPrincipalSubgroup F p)
        (isDiscrete_parabolicPrincipalSubgroup F p),
          φ (LeftCosetSpace.mk (parabolicPrincipalSubgroup F p) g) *
            chamberDensity F p hK ell S g ∂Measure.haar := by
  let q := LeftCosetSpace.mk (parabolicPrincipalSubgroup F p)
  let T := domainHeight F p hK ⁻¹' S
  let δ := domainDensity F p hK ell
  let : MeasurableSpace (RealCharacterDual F P) := borel _
  let : BorelSpace (RealCharacterDual F P) := ⟨rfl⟩
  have hT : MeasurableSet T := (continuous_domainHeight F p hK).measurable hS
  have hδ : Measurable δ := measurable_domainDensity F p hK hell
  change ∫⁻ z, φ z ∂((domainHaarMeasure F p).restrict T).withDensity δ = _
  rw [lintegral_withDensity_eq_lintegral_mul _ hδ hφ, ← lintegral_indicator hT]
  unfold domainHaarMeasure LeftCosetSpace.haarQuotientMeasure
    LeftCosetSpace.discreteQuotientMeasure LeftCosetSpace.quotientMeasure
  rw [lintegral_map ((hδ.mul hφ).indicator hT) (LeftCosetSpace.measurable_mk _)]
  apply lintegral_congr
  intro g
  change T.indicator (δ * φ) (q g) = φ (q g) * chamberDensity F p hK ell S g
  by_cases hg : hK.height g ∈ S
  · rw [indicator_of_mem (show q g ∈ T from hg), chamberDensity,
      indicator_of_mem (show g ∈ hK.height ⁻¹' S from hg)]
    exact mul_comm _ _
  · rw [indicator_of_notMem (show q g ∉ T from hg), chamberDensity,
      indicator_of_notMem (show g ∉ hK.height ⁻¹' S from hg), mul_zero]

end WeightedSiegel

open RepresentationGrowth WeightedSiegel

/-- A fixed weighted height admits a single growth exponent for pointwise right convolution,
uniform over compact kernel supports and compact sets of finite components. -/
def AdelicWeightedPointwiseConvolutionStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (G P : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffine G.X.left] [IsAffine P.X.left] [LocallyOfFiniteType G.X.hom]
    (p : P ⟶ G) [IsClosedImmersion p.hom.hom.left]
    (K : Subgroup (AdelicGroupPoints F G)) (hK : IsIwasawaCompact p K)
    (n : ℕ) (rho : GroupScheme.MatrixRepresentation G (Fin n)),
    0 < n → GroupScheme.IsClosedSubgroup rho →
    ∀ (ell : RealCharacterDual F P → ℝ), Continuous ell →
    ∀ (A r : ℝ), 0 < A → 0 ≤ r →
    (∀ g, Real.exp (ell (hK.height g)) ≤ A * adelicHeight F G rho g ^ r) →
    let Γ := parabolicPrincipalSubgroup F p
    let D := LeftCosetSpace.fundamentalDomain Γ (isDiscrete_parabolicPrincipalSubgroup F p)
    let μG : Measure (AdelicGroupPoints F G) := Measure.haar
    ∃ R : ℝ, 0 ≤ R ∧ ∀ (Kf : Set (FiniteAdelicGroupPoints F G)), IsCompact Kf →
      ∀ (C : Set (AdelicGroupPoints F G)), IsCompact C →
      ∃ B : ℝ, 0 ≤ B ∧ ∀ (S : Set (RealCharacterDual F P)), @MeasurableSet _ (borel _) S →
        ∀ x : AdelicGroupPoints F G, finite F G x ∈ Kf →
        (∀ a ∈ C, hK.height (x * a) ∈ S) →
        ∀ (f : AdelicGroupPoints F G → ℂ), Measurable f →
        (∀ (dlt : Γ) g, f ((dlt : AdelicGroupPoints F G) * g) = f g) →
        let I := ∫⁻ g in D, ‖f g‖ₑ ^ (2 : ℕ) * chamberDensity F p hK ell S g ∂μG
        I < ∞ → ∀ (h : AdelicGroupPoints F G → ℂ) (hh : MemLp h 2 (μG.restrict C)),
        Function.support h ⊆ C →
          Integrable (fun a => h a * f (x * a)) μG ∧
          ‖∫ a, h a * f (x * a) ∂μG‖ ≤
            B * adelicHeight F G rho x ^ R * ‖hh.toLp h‖ * Real.sqrt I.toReal

/-- Weighted support domination and Cauchy–Schwarz give the pointwise growth estimate. -/
theorem adelicWeightedPointwiseConvolution : AdelicWeightedPointwiseConvolutionStatement.{u} := by
  classical
  intro F _ _ G P _ _ _ p _ K hK n rho hn hrho ell hell A r hA hr hweight Γ D μG
  let H := adelicHeight F G rho
  have hH (g : AdelicGroupPoints F G) : 0 < H g :=
    zero_lt_one.trans_le (one_le_adelicHeight F G rho hn g)
  obtain ⟨d, hdom⟩ := adelicWeightedSupportMeasure F G n rho hn hrho Γ
    (parabolicPrincipalSubgroup_le F p)
  refine ⟨(d : ℝ) / 2 + r, by positivity, fun Kf hKf C hC => ?_⟩
  obtain ⟨B, hB, hdomC⟩ := hdom Kf hKf C hC
  obtain ⟨L₀, hL₀⟩ := (hC.image (continuous_adelicHeight F G rho hn)).bddAbove
  let L := max L₀ 1
  have hL : 0 < L := zero_lt_one.trans_le (le_max_right _ _)
  let M := A * L ^ r
  have hM : 0 < M := mul_pos hA (Real.rpow_pos_of_pos hL _)
  refine ⟨Real.sqrt B * M, mul_nonneg (Real.sqrt_nonneg _) hM.le, ?_⟩
  intro S hS x hx hxs f hf hfΓ I hI h hh hsub
  let T := domainHeight F p hK ⁻¹' S
  let ν := domainMeasure F p hK ell T
  let q := LeftCosetSpace.mk Γ
  let fQ : DomainQuotient F p → ℂ := LeftCosetSpace.lift Γ f hfΓ
  have hfQ : Measurable fQ := measurable_from_quotient.mpr hf
  have hIeq : (∫⁻ z, ‖fQ z‖ₑ ^ (2 : ℕ) ∂ν) = I :=
    lintegral_domainMeasure_eq_chamberDensity F p hK ell hell S hS (hfQ.enorm.pow_const _)
  have hnorm : eLpNorm fQ 2 ν = I ^ (1 / 2 : ℝ) := by
    rw [← hIeq]
    simpa only [ENNReal.toReal_ofNat, ENNReal.rpow_two] using
      eLpNorm_eq_lintegral_rpow_enorm_toReal (p := 2) (by norm_num) (by norm_num)
        hfQ.aestronglyMeasurable
  have hmem : MemLp fQ 2 ν := by
    rw [memLp_iff, hnorm]
    exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) hI.ne
  have hLp : ‖hmem.toLp fQ‖ = Real.sqrt I.toReal := by
    rw [Lp.norm_toLp, hnorm, ← ENNReal.toReal_rpow, Real.sqrt_eq_rpow]
  let m := M * H x ^ r
  have hm : 0 < m := mul_pos hM (Real.rpow_pos_of_pos (hH x) _)
  let b := m⁻¹ ^ 2
  have hb : 0 < b := pow_pos (inv_pos.mpr hm) _
  have hδ (a : AdelicGroupPoints F G) (ha : a ∈ C) :
      ENNReal.ofReal b ≤ domainDensity F p hK ell (q (x * a)) := by
    have haL : H a ≤ L := (hL₀ ⟨a, ha, rfl⟩).trans (le_max_left _ _)
    have hxa : H (x * a) ≤ H x * L :=
      (adelicHeight_mul_le F G rho hn x a).trans (mul_le_mul_of_nonneg_left haL (hH x).le)
    have hma : Real.exp (ell (hK.height (x * a))) ≤ m := calc
      _ ≤ A * H (x * a) ^ r := hweight _
      _ ≤ A * (H x * L) ^ r :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (hH _).le hxa hr) hA.le
      _ = m := by rw [Real.mul_rpow (hH x).le hL.le]; unfold m M; ring
    have he (t : ℝ) : Real.exp (-2 * t) = (Real.exp t)⁻¹ ^ (2 : ℕ) := by
      rw [← Real.exp_neg, ← Real.exp_nat_mul]
      congr 1
      push_cast
      ring
    unfold domainDensity
    change ENNReal.ofReal b ≤ ENNReal.ofReal (Real.exp (-2 * ell (hK.height (x * a))))
    rw [he]
    exact ENNReal.ofReal_le_ofReal
      (pow_le_pow_left₀ (inv_pos.mpr hm).le (inv_le_inv₀ hm (Real.exp_pos _) |>.mpr hma) _)
  have hdomx := hdomC T (domainDensity F p hK ell) x b hb hx
    (fun a ha => ⟨show q (x * a) ∈ T from hxs a ha, hδ a ha⟩)
  have hcoeff : 0 ≤ B * H x ^ d / b :=
    div_nonneg (mul_nonneg hB (pow_nonneg (hH x).le _)) hb.le
  obtain ⟨hi, hbound⟩ := norm_integral_mul_comp_le_of_map_restrict_le μG ν
    ((LeftCosetSpace.measurable_mk Γ).comp (measurable_const.mul measurable_id))
    hcoeff hdomx hh hsub hmem
  refine ⟨hi, hbound.trans_eq ?_⟩
  have hsqrt : Real.sqrt (B * H x ^ d / b) = Real.sqrt B * M * H x ^ ((d : ℝ) / 2 + r) := by
    rw [Real.sqrt_div (mul_nonneg hB (pow_nonneg (hH x).le _)), Real.sqrt_mul hB,
      show Real.sqrt b = m⁻¹ from Real.sqrt_sq (inv_pos.mpr hm).le,
      div_inv_eq_mul, Real.sqrt_eq_rpow (x := H x ^ d), ← Real.rpow_natCast (H x) d,
      ← Real.rpow_mul (hH x).le, Real.rpow_add (hH x)]
    rw [show (d : ℝ) * (1 / 2) = (d : ℝ) / 2 by ring]
    unfold m
    ring
  rw [hsqrt, hLp]
  ring

end Langlands.Global
