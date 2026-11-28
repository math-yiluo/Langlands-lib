import Langlands.Global.AdelicNormOneRepresentativeDecay
import Langlands.Global.AdelicLeviCuspFormMajorantProof
import Langlands.Global.AdelicCuspidalProjectionExistenceReduction
import Langlands.Global.AdelicLeviFibreSmoothing
import Langlands.Global.AdelicNormOnePartialConvolutionGrowth

/-! # Integrable majorants for the finite Levi fibre pairing -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory Set
open scoped CategoryTheory.MonObj CompactlySupported Pointwise NNReal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000

namespace Langlands.Global.StandardParabolicFamily

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints
  PositiveRealTorus RepresentationGrowth

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (fam : StandardParabolicFamily F G) (J : StandardIndex F G fam.i fam.ν)

local notation "A" => AdelicGroupPoints F G
local notation "M" => fam.M J
local notation "AM" => AdelicGroupPoints F M
local notation "A₁" => normOneSubgroup F M
local notation "X₁" => NormOneRationalQuotient F M
local notation "dq₁" => normOneRationalQuotientHaarMeasure F M
local notation "jM" => fam.l J ≫ fam.p J
local notation "ι" => map F M G jM
local notation "Γ" => parabolicQuotientSubgroup F (fam.p J) (fam.iU J) (fam.l J)
local notation "hM" => IsRationalLeviSubgroup.isConnectedReductive
  (ParabolicRootPresentationData.IsCompatible.levi (fam.isCompatible J))

variable {N : ℕ} (rho : MatrixRepresentation G (Fin N)) (hN : 0 < N)

include hN

/-- The product of an ambient function of height growth with a rapidly decreasing Levi test
is uniformly bounded on norm-one points and compact families of right translates. -/
theorem exists_leviPairing_norm_bound {f : A → ℂ} {t : AM → ℂ}
    (hf : HasHeightGrowth rho f) (hfi : IsLeftInvariantUnder F G Γ f)
    (hti : IsLeftInvariantUnder F M (rationalSubgroup F M) t)
    (htd : HasRapidDecayOnNormOneRepresentatives (jM ≫ rho) t) {D : Set A} (hD : IsCompact D) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (x : A₁) (g : A), g ∈ D →
      ‖f (ι (x : AM) * g)‖ * ‖t (x : AM)‖ ≤ C := by
  obtain ⟨C, R, hC, _, hf⟩ := hf
  let r := ⌈R⌉₊
  let H := adelicHeight F G rho
  have hH (z : A) : 0 ≤ H z := zero_le_one.trans (one_le_adelicHeight F G rho hN z)
  have hbound (z : A) : ‖f z‖ ≤ C * H z ^ r := by
    rw [← Real.rpow_natCast]
    exact (hf z).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le (one_le_adelicHeight F G rho hN z) (Nat.le_ceil R)) hC)
  obtain ⟨B, hB⟩ := (hD.image (continuous_adelicHeight F G rho hN)).bddAbove
  let D₀ := max B 1
  have hD₀ : 0 ≤ D₀ := zero_le_one.trans (le_max_right _ _)
  obtain ⟨L, hL, htest⟩ := htd r
  refine ⟨C * D₀ ^ r * L, by positivity, fun x g hg => ?_⟩
  obtain ⟨a, ha⟩ := htest x
  let y := rational F M a * (x : AM)
  have ha' : ‖t y‖ * adelicHeight F M (jM ≫ rho) y ^ r ≤ L := ha
  have hyf : f (ι y * g) = f (ι (x : AM) * g) := by
    dsimp only [y]
    rw [map_mul, mul_assoc]
    exact fam.leviRational_mul_of_parabolicInvariant J hfi a _
  have hyt : t y = t x := hti _ ⟨a, rfl⟩ _
  rw [← hyf, ← hyt]
  have hg' : H g ≤ D₀ := (hB (mem_image_of_mem H hg)).trans (le_max_left _ _)
  have hhat : H (ι y * g) ≤ H (ι y) * D₀ :=
    (adelicHeight_mul_le F G rho hN _ _).trans (mul_le_mul_of_nonneg_left hg' (hH _))
  calc
    _ ≤ C * H (ι y * g) ^ r * ‖t y‖ :=
      mul_le_mul_of_nonneg_right (hbound _) (norm_nonneg _)
    _ ≤ C * (H (ι y) * D₀) ^ r * ‖t y‖ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (hH _) hhat _) hC) (norm_nonneg _)
    _ = C * D₀ ^ r * (‖t y‖ * adelicHeight F M (jM ≫ rho) y ^ r) := by
      change C * (adelicHeight F G rho (ι y) * D₀) ^ r * ‖t y‖ = _
      rw [adelicHeight_map_eq_adelicHeight_comp, mul_pow]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left ha' (mul_nonneg hC (pow_nonneg hD₀ _))

/-- Absolute convergence of a Levi pairing for a continuous function of moderate growth
and a continuous test with weighted norm-one representatives. -/
theorem integrable_leviPairingIntegrand_of_heightGrowth {f : A → ℂ} {t : AM → ℂ}
    (hf : HasHeightGrowth rho f) (hfc : Continuous f) (hfi : IsLeftInvariantUnder F G Γ f)
    (htc : Continuous t) (hti : IsLeftInvariantUnder F M (rationalSubgroup F M) t)
    (htd : HasRapidDecayOnNormOneRepresentatives (jM ≫ rho) t) (g : A) :
    Integrable (fam.leviPairingIntegrand J f g t) dq₁ := by
  let := AdelicSiegelFactors.isFiniteMeasure_normOneRationalQuotientHaarMeasure_of_connectedReductive F M hM
  obtain ⟨C, _, hb⟩ := fam.exists_leviPairing_norm_bound J rho hN hf hfi hti htd
    (isCompact_singleton (x := g))
  apply (integrable_const C).mono'
    (fam.continuous_leviPairingIntegrand J hfc (fam.leviRational_mul_of_parabolicInvariant J hfi)
      htc hti g).aestronglyMeasurable
  refine Filter.Eventually.of_forall fun q => ?_
  rw [leviPairingIntegrand, norm_mul, Complex.norm_conj]
  exact hb (Quotient.out q) g rfl

/-- The compact product bound supplies the domination premise in the finite Iwasawa
unfolding. -/
theorem exists_leviPairing_iwasawa_majorant {f : A → ℂ} {t : AM → ℂ}
    (hf : HasHeightGrowth rho f) (hfi : IsLeftInvariantUnder F G Γ f)
    (hti : IsLeftInvariantUnder F M (rationalSubgroup F M) t)
    (htd : HasRapidDecayOnNormOneRepresentatives (jM ≫ rho) t)
    (K : Subgroup A) (hK : IsCompact (K : Set A)) (C : Set AM) (hC : IsCompact C) :
    ∃ W : X₁ → ℝ, Integrable W dq₁ ∧ ∀ᵐ q ∂dq₁, ∀ (k : K) (z : AM), z ∈ C →
      ‖f (ι (((Quotient.out q : A₁) : AM) * z) * k)‖ *
        ‖t ((Quotient.out q : A₁) : AM)‖ ≤ W q := by
  let := AdelicSiegelFactors.isFiniteMeasure_normOneRationalQuotientHaarMeasure_of_connectedReductive F M hM
  obtain ⟨B, _, hb⟩ := fam.exists_leviPairing_norm_bound J rho hN hf hfi hti htd
    ((hC.image (ι).continuous).mul hK)
  refine ⟨fun _ => B, integrable_const _, Filter.Eventually.of_forall fun q k z hz => ?_⟩
  rw [map_mul, mul_assoc]
  exact hb (Quotient.out q) (ι z * k) (Set.mul_mem_mul (mem_image_of_mem _ hz) k.property)

omit hN

variable (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ fam.M J)
  (hi : Function.Injective (characterRestrict i)) [(characterRestrict i).range.FiniteIndex]
  (I : Type u) [Fintype I] (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of F)) I) (hc : IsCentral i)
  [(Measure.haar : Measure (normOneSubgroup F (fam.M J))).IsMulRightInvariant]

local notation "Pos" => intrinsicSubgroup F T
local notation "pp" => positivePointMap F M T i
local notation "νP" => normalizedPositiveHaarMeasure F M T i hi I e hc
local notation "Q₊" => PositiveRationalQuotient F M T i
local notation "V" => Lp ℂ 2 (positiveRationalQuotientHaarMeasure F M T i)
local notation "δ" => fam.leviModulus J
local notation "Γ₁" => rationalNormOneSubgroup F M

/-- In the pairing of a smoothed continuous family with a test of rapid decay, the integral
over the norm-one quotient can be exchanged with the positive integral. -/
theorem leviPairing_leviFibreSmoothing_eq_integral {n : ℕ}
    (rhoM : MatrixRepresentation M (Fin n)) (hn : 0 < n) (hrhoM : IsClosedSubgroup rhoM)
    (β : C_c(A, ℂ)) (w : Pos → V) (hw : Continuous w)
    (t : AM → ℂ) (htc : Continuous t) (hti : IsLeftInvariantUnder F M (rationalSubgroup F M) t)
    (htd : HasRapidDecayOnNormOneRepresentatives rhoM t) (g : A) :
    fam.leviPairing J (fam.leviFibreSmoothing J T i hi I e hc β w) g t =
      ∫ b, ∫ q : X₁, fam.leviFibreSmoothingIntegrand J T i β g b (Quotient.out q) (w b) *
        starRingEnd ℂ (t ((Quotient.out q : A₁) : AM)) ∂dq₁ ∂νP := by
  let := normalizedPositiveHaarMeasure_isHaarMeasure F M T i hi I e hc
  let := normalizedPositiveHaarMeasure_sigmaFinite F M T i hi I e hc
  let : T2Space Pos := (positiveLogCoordinateEquiv F T I e).toHomeomorph.symm.t2Space
  let := AdelicSiegelFactors.isFiniteMeasure_normOneRationalQuotientHaarMeasure_of_connectedReductive F M hM
  let E (p : A₁ × Pos) :=
    fam.leviFibreSmoothingIntegrand J T i β g p.2 p.1 (w p.2) * starRingEnd ℂ (t p.1)
  let f (q : X₁) (b : Pos) := E (Quotient.out q, b)
  have hE : Continuous E := by
    apply Continuous.mul
    · exact Continuous.comp'
        (g := fun p : A × Pos × A₁ => fam.leviFibreSmoothingIntegrand J T i β p.1 p.2.1 p.2.2 (w p.2.1))
        (f := fun p : A₁ × Pos => ((g, p.2, p.1) : A × Pos × A₁))
        (fam.continuous_leviFibreSmoothingIntegrand J T i hi I e hc β w hw)
        (continuous_const.prodMk (continuous_snd.prodMk continuous_fst))
    · exact Complex.continuous_conj.comp (htc.comp (continuous_subtype_val.comp continuous_fst))
  have hInv (r : RationalGroupPoints F M) (x : A₁) (b : Pos) :
      E (rationalNormOne F M r * x, b) = E (x, b) := by
    dsimp only [E, leviFibreSmoothingIntegrand]
    rw [Subgroup.coe_mul, rationalNormOne_val, normOnePartialConvolution_rational_mul, hti _ ⟨r, rfl⟩]
  have hf : Continuous (Function.uncurry f) := by
    apply LeftCosetSpace.continuous_out_prod' Γ₁ E hE
    rintro ⟨_, r, rfl⟩ x b
    exact hInv r x b
  obtain ⟨D, hD, hSupp⟩ := fam.exists_compact_support_leviFibreSmoothingIntegrand J T i hi I e β
    (isCompact_singleton (x := g))
  let L := fam.radicalKernelCc J β g 1
  let B : Set AM := (tsupport L)⁻¹ * (pp '' D)
  have hB : IsCompact B := L.hasCompactSupport.inv.mul (hD.image (pp).continuous)
  let K (b : Pos) := fam.leviFibreSmoothingKernel J T i β g b
  have hKB (b : Pos) (hb : b ∈ D) : tsupport (K b) ⊆ B := by
    apply closure_minimal _ hB.isClosed
    intro z hz
    let y := pp b * z⁻¹
    have hy : L y ≠ 0 := by
      intro h
      apply hz
      change starRingEnd ℂ (L y) = 0
      rw [h, map_zero]
    refine ⟨y⁻¹, Set.inv_mem_inv.mpr (subset_tsupport _ hy), pp b, ⟨b, hb, rfl⟩, ?_⟩
    dsimp only [y]
    group
  obtain ⟨R, hR⟩ := L.continuous.bounded_above_of_compact_support L.hasCompactSupport
  have hKR (b : Pos) (z : AM) : ‖K b z‖ ≤ max R 0 := by
    change ‖starRingEnd ℂ (L (pp b * z⁻¹))‖ ≤ _
    rw [Complex.norm_conj]
    exact (hR _).trans (le_max_left _ _)
  obtain ⟨C, hC, m, hconv⟩ := exists_normOnePartialConvolution_bound T i hi I e hc rhoM hn hrhoM
    B hB (max R 0) (le_max_right _ _)
  let a (b : Pos) := (δ (pp b) : ℝ)⁻¹
  have ha0 (b : Pos) : 0 ≤ a b := inv_nonneg.mpr (NNReal.coe_nonneg _)
  have ha : Continuous a :=
    (NNReal.continuous_coe.comp ((fam.continuous_leviModulus J).comp (pp).continuous)).inv₀
      fun b => (NNReal.coe_pos.mpr (fam.leviModulus_pos J (pp b))).ne'
  let W (b : Pos) := a b * ‖w b‖
  obtain ⟨B₀, hB₀⟩ := (hD.image (ha.mul hw.norm : Continuous W)).bddAbove
  obtain ⟨L₀, hL₀, htest⟩ := htd m
  let M₀ := C * max B₀ 0 * L₀
  have hbound (q : X₁) (b : Pos) (hb : b ∈ D) : ‖f q b‖ ≤ M₀ := by
    obtain ⟨r, hr⟩ := htest (Quotient.out q)
    let x : A₁ := rationalNormOne F M r * Quotient.out q
    let H := adelicHeight F M rhoM
    have ht : ‖t (x : AM)‖ * H x ^ m ≤ L₀ := hr
    have hfE : f q b = E (x, b) := (hInv r (Quotient.out q) b).symm
    rw [hfE]
    change ‖a b • normOnePartialConvolution T i (K b) (w b : Q₊ → ℂ) (x : AM) *
      starRingEnd ℂ (t (x : AM))‖ ≤ M₀
    rw [norm_mul, norm_smul, Complex.norm_conj, Real.norm_of_nonneg (ha0 b)]
    calc
      _ ≤ a b * (C * H x ^ m * ‖w b‖) * ‖t (x : AM)‖ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
          (hconv (K b) (hKB b hb) (hKR b) x (w b)) (ha0 b)) (norm_nonneg _)
      _ = C * W b * (‖t (x : AM)‖ * H x ^ m) := by dsimp only [W]; ring
      _ ≤ C * max B₀ 0 * L₀ := mul_le_mul
        (mul_le_mul_of_nonneg_left ((hB₀ (mem_image_of_mem W hb)).trans (le_max_left _ _)) hC) ht
        (mul_nonneg (norm_nonneg _) (pow_nonneg (zero_le_one.trans (one_le_adelicHeight F M rhoM hn _)) _))
        (mul_nonneg hC (le_max_right _ _))
  have hz (q : X₁) (b : Pos) (hb : b ∉ D) : f q b = 0 := by
    dsimp only [f, E]
    rw [hSupp g rfl b hb, zero_mul]
  have hmass : (Measure.prod dq₁ νP) (univ ×ˢ D : Set (X₁ × Pos)) < ⊤ := by
    rw [Measure.prod_prod]
    exact ENNReal.mul_lt_top (measure_lt_top dq₁ univ) hD.measure_lt_top
  have hint : Integrable (Function.uncurry f) (Measure.prod dq₁ νP) := by
    have hmajor : Integrable ((univ ×ˢ D : Set (X₁ × Pos)).indicator (fun _ => M₀))
        (Measure.prod dq₁ νP) :=
      (integrableOn_const hmass.ne).integrable_indicator (MeasurableSet.univ.prod hD.measurableSet)
    apply hmajor.mono' hf.aestronglyMeasurable
    refine Filter.Eventually.of_forall fun p => ?_
    by_cases h : p.2 ∈ D
    · rw [indicator_of_mem (show p ∈ (univ ×ˢ D : Set (X₁ × Pos)) from ⟨mem_univ _, h⟩)]
      exact hbound p.1 p.2 h
    · rw [indicator_of_notMem (fun hp => h hp.2), Function.uncurry, hz _ _ h, norm_zero]
  have hterm (q : X₁) :
      fam.leviPairingIntegrand J (fam.leviFibreSmoothing J T i hi I e hc β w) g t q =
        ∫ b, f q b ∂νP := by
    unfold leviPairingIntegrand leviFibreSmoothing
    rw [← integral_mul_const]
    exact integral_congr_ae (Filter.Eventually.of_forall fun b =>
      congrArg (· * starRingEnd ℂ (t ((Quotient.out q : A₁) : AM)))
        (fam.leviFibreSmoothingIntegrand_mul_normOne J T i hc β g b (Quotient.out q) (w b)))
  unfold leviPairing
  rw [integral_congr_ae (Filter.Eventually.of_forall hterm), integral_integral_swap hint]

end Langlands.Global.StandardParabolicFamily
