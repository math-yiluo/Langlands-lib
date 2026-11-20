import Langlands.Global.RankinSelberg.EisensteinBoundary
import Langlands.Global.RankinSelberg.EqualAnalyticDualTransport

/-! # Poisson decomposition of the unfolded Eisenstein series -/

noncomputable section
universe u
open NumberField MeasureTheory Set Langlands.Global
open scoped CategoryTheory.MonObj
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.Eisenstein

open EqualAnalytic

local instance poissonSchemeAffine (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.IsAffine (Scheme F n).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance poissonSchemeSmooth (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.Smooth (Scheme F n).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement _ _

variable (F : Type u) [Field F] [NumberField F] (r : ℕ)

local notation "n" => (r + 1)
local notation "e" => GeneralLinearGroupPoints.adelicEquiv F n

/-- Pointwise Poisson summation for two theta kernels, including their zero-vector terms. -/
def IsThetaPoissonPair (Φ Ψ : RowVector F n → ℂ) : Prop :=
  ∀ x : Points F n, thetaSum F n Φ (e x) + Φ 0 =
    Complex.exp (-(Real.log (detNorm F n x) : ℂ)) *
      (thetaSum F n Ψ (e (iota F n x)) + Ψ 0)

theorem isThetaPoissonPair_fourier [CompactSpace (AdeleQuotient F)]
    (ψ : AddChar (Adeles F) ℂ) (hψ : IsStandardAdditiveCharacter F ψ)
    {Φ : RowVector F n → ℂ} (hΦ : Φ ∈ schwartzBruhat F n) :
    IsThetaPoissonPair F r Φ (fourierTransform F n ψ Φ) :=
  thetaSum_poisson_points n ψ hψ hΦ

theorem IsThetaPoissonPair.symm {Φ Ψ : RowVector F n → ℂ}
    (hP : IsThetaPoissonPair F r Φ Ψ) : IsThetaPoissonPair F r Ψ Φ := by
  intro g
  have h := hP (iota F n g)
  rw [UnequalAnalytic.iota_iota, log_detNorm_iota, Complex.ofReal_neg, neg_neg] at h
  rw [h, ← mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, one_mul]

private theorem mellinHeight_iota_inv (g : Points F n) (a : Points F 1) :
    mellinHeight F r (iota F n g) a⁻¹ = -mellinHeight F r g a := by
  rw [mellinHeight, mellinHeight, ← iota_zeta, ← UnequalAnalytic.iota_mul, log_detNorm_iota]

private theorem mellinHeight_principal_mul (g : Points F n) (c : ideleRational F)
    (a : Points F 1) :
    mellinHeight F r g ((c : Points F 1) * a) = mellinHeight F r g a := by
  rw [mellinHeight_eq, mellinHeight_eq, logNorm_ideleRational_mul]

private theorem ae_mellinHeight_ne_zero (g : Points F n) :
    ∀ᵐ a ∂ideleQuotientMeasure F, mellinHeight F r g a ≠ 0 := by
  let b := -Real.log (detNorm F n g) / ((n : ℕ) : ℝ)
  have hb : {a | mellinHeight F r g a = 0} = logNorm F ⁻¹' {b} := by
    ext a
    simp only [mem_ofPred_eq, mem_preimage, mem_singleton_iff, mellinHeight_eq, b]
    rw [eq_div_iff (by positivity : ((n : ℕ) : ℝ) ≠ 0), mul_comm (logNorm F a)]
    constructor <;> intro h <;> linarith
  rw [ae_iff]
  simp only [not_ne_iff, hb]
  rw [ideleQuotientMeasure, Measure.restrict_apply ((measurable_logNorm F) (measurableSet_singleton _)),
    inter_comm, ideleMeasure_logNorm_preimage F (measurableSet_singleton _), measure_singleton]

private theorem integral_ideleQuotient_inv (f : Points F 1 → ℂ)
    (hf : ∀ (c : ideleRational F) (a : Points F 1), f ((c : Points F 1) * a) = f a) :
    ∫ a, f a⁻¹ ∂ideleQuotientMeasure F = ∫ a, f a ∂ideleQuotientMeasure F := by
  have hInv : MeasurePreserving (Inv.inv : Points F 1 → Points F 1)
      (ideleMeasure F) (ideleMeasure F) := by
    refine ⟨measurable_inv, ?_⟩
    rw [ideleMeasure, Measure.map_smul _ measurable_inv.aemeasurable, Measure.map_inv_eq_self]
  have hD := isFundamentalDomain_ideleDomain F (ideleMeasure F)
  have hDinv := (isFundamentalDomain_preimage_inv F
    (isFundamentalDomain_ideleDomain F Measure.haar)).mono
      (show ideleMeasure F ≪ Measure.haar from Measure.smul_absolutelyContinuous)
  calc
    _ = ∫ a in Inv.inv ⁻¹' ideleDomain F, f a⁻¹ ∂ideleMeasure F :=
      hD.setIntegral_eq hDinv fun c a => by
        change f (((c : Points F 1) * a)⁻¹) = f a⁻¹
        rw [mul_inv_rev, points_one_mul_comm F a⁻¹]
        exact hf c⁻¹ a⁻¹
    _ = _ := hInv.setIntegral_preimage_emb measurableEmbedding_inv f _

variable (χ : IdeleClassGroup (𝓞 F) F →ₜ* ℂˣ) {Φ Ψ : RowVector F (r + 1) → ℂ}

private theorem ideleChar_inv_inv (a : Points F 1) : ideleChar F χ⁻¹ a⁻¹ = ideleChar F χ a := by
  have h := (ideleChar_mul F χ a⁻¹ a).symm
  rw [inv_mul_cancel, ideleChar_one] at h
  rw [ideleChar_inv, eq_inv_of_mul_eq_one_left h, inv_inv]

private theorem mellinIntegrand_principal_mul
    (g : Points F n) (s : ℂ) (c : ideleRational F) (a : Points F 1) :
    mellinIntegrand F r χ Φ g s ((c : Points F 1) * a) = mellinIntegrand F r χ Φ g s a := by
  obtain ⟨f, hf⟩ := (ratUnitEquiv F).surjective c
  have h := congrArg Subtype.val hf
  rw [ratUnitEquiv_apply] at h
  rw [mellinIntegrand_eq, mellinIntegrand_eq, ideleChar_ideleRational_mul,
    mellinHeight_principal_mul, ← h, scalarTheta_ratUnit_mul]

private theorem mellinIntegrand_poisson (hP : IsThetaPoissonPair F r Φ Ψ)
    (g : Points F n) (s : ℂ) (a : Points F 1) :
    mellinIntegrand F r χ Φ g s a + Φ 0 * boundaryWeight F r χ g s a -
        Ψ 0 * boundaryWeight F r χ g (s - 1) a =
      mellinIntegrand F r χ⁻¹ Ψ (iota F n g) (1 - s) a⁻¹ := by
  have h := hP (zeta F n a * g)
  rw [UnequalAnalytic.iota_mul, iota_zeta] at h
  change scalarTheta F n Φ g a + Φ 0 = Complex.exp (-(mellinHeight F r g a : ℂ)) *
    (scalarTheta F n Ψ (iota F n g) a⁻¹ + Ψ 0) at h
  let L : ℂ := mellinHeight F r g a
  have hs : Complex.exp ((s - 1) * L) = Complex.exp (-L) * Complex.exp (s * L) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  have hdual : Complex.exp ((1 - s) * (-L)) = Complex.exp ((s - 1) * L) := by
    congr 1
    ring
  rw [mellinIntegrand_eq, mellinIntegrand_eq, boundaryWeight, boundaryWeight,
    mellinHeight_iota_inv, Complex.ofReal_neg, ideleChar_inv_inv, hdual, hs]
  linear_combination (ideleChar F χ a * Complex.exp (s * L)) * h

/-- Unfolded Mellin integral as the sum of two positive tails and two boundary terms. -/
theorem integral_mellin_eq (hP : IsThetaPoissonPair F r Φ Ψ) (g : Points F n) (s : ℂ)
    (hM : Integrable (mellinIntegrand F r χ Φ g s) (ideleQuotientMeasure F))
    (hB : IntegrableOn (boundaryWeight F r χ g s) (positiveLog F r g)ᶜ (ideleQuotientMeasure F))
    (hB' : IntegrableOn (boundaryWeight F r χ g (s - 1)) (positiveLog F r g)ᶜ
      (ideleQuotientMeasure F)) :
    ∫ a, mellinIntegrand F r χ Φ g s a ∂ideleQuotientMeasure F =
      positiveTail F r χ Φ g s + positiveTail F r χ⁻¹ Ψ (iota F n g) (1 - s) +
        Ψ 0 * negativeBoundary F r χ g (s - 1) - Φ 0 * negativeBoundary F r χ g s := by
  let upper : Set (Points F 1) := {a | 0 < mellinHeight F r (iota F n g) a}
  let dual := mellinIntegrand F r χ⁻¹ Ψ (iota F n g) (1 - s)
  let f := upper.indicator dual
  have hf : ∀ (c : ideleRational F) (a : Points F 1), f ((c : Points F 1) * a) = f a := by
    intro c a
    have hcut : (c : Points F 1) * a ∈ upper ↔ a ∈ upper := by
      simp only [upper, mem_ofPred_eq, mellinHeight_principal_mul]
    by_cases ha : a ∈ upper
    · simp only [f, indicator_of_mem (hcut.2 ha), indicator_of_mem ha, dual,
        mellinIntegrand_principal_mul]
    · simp only [f, indicator_of_notMem (mt hcut.1 ha), indicator_of_notMem ha]
  have hcut (a : Points F 1) : a⁻¹ ∈ upper ↔ a ∈ (positiveLog F r g)ᶜ := by
    simp only [upper, mem_ofPred_eq, mellinHeight_iota_inv, positiveLog, mem_compl_iff, not_le,
      neg_pos]
  let k : Points F 1 → ℂ := fun a =>
    mellinIntegrand F r χ Φ g s a + Φ 0 * boundaryWeight F r χ g s a -
      Ψ 0 * boundaryWeight F r χ g (s - 1) a
  have hinv : ∫ a in (positiveLog F r g)ᶜ, k a ∂ideleQuotientMeasure F =
      ∫ a, f a ∂ideleQuotientMeasure F := by
    rw [← integral_ideleQuotient_inv F f hf,
      ← integral_indicator (measurableSet_positiveLog F r g).compl]
    apply integral_congr_ae
    filter_upwards [] with a
    by_cases ha : a ∈ (positiveLog F r g)ᶜ
    · simpa only [indicator_of_mem ha, f, indicator_of_mem ((hcut a).2 ha), k, dual]
        using mellinIntegrand_poisson F r χ hP g s a
    · simp only [f, indicator_of_notMem (mt (hcut a).1 ha), indicator_of_notMem ha]
  have htail : ∫ a, f a ∂ideleQuotientMeasure F =
      positiveTail F r χ⁻¹ Ψ (iota F n g) (1 - s) := by
    rw [positiveTail, ← integral_indicator (measurableSet_positiveLog F r (iota F n g))]
    apply integral_congr_ae
    filter_upwards [ae_mellinHeight_ne_zero F r (iota F n g)] with a ha
    have hmem : a ∈ upper ↔ a ∈ positiveLog F r (iota F n g) := by
      change (0 < mellinHeight F r (iota F n g) a) ↔ (0 ≤ mellinHeight F r (iota F n g) a)
      exact ⟨le_of_lt, fun h => lt_of_le_of_ne h ha.symm⟩
    by_cases hu : a ∈ upper
    · simp only [f, indicator_of_mem hu, indicator_of_mem (hmem.1 hu), dual]
    · simp only [f, indicator_of_notMem hu, indicator_of_notMem (mt hmem.2 hu)]
  rw [htail, show k = mellinIntegrand F r χ Φ g s +
      (fun a => Φ 0 * boundaryWeight F r χ g s a) -
      (fun a => Ψ 0 * boundaryWeight F r χ g (s - 1) a) from rfl,
      integral_sub' (hM.integrableOn.add (hB.const_mul (Φ 0))) (hB'.const_mul (Ψ 0)),
      integral_add' hM.integrableOn (hB.const_mul (Φ 0)), integral_const_mul, integral_const_mul] at hinv
  rw [← integral_add_compl (measurableSet_positiveLog F r g) hM]
  unfold positiveTail at hinv
  unfold positiveTail negativeBoundary
  linear_combination hinv

end Langlands.Global.RankinSelbergGlobal.Eisenstein
