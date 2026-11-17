import Langlands.Global.RankinSelberg.AdelicSimpleRootGaugeHaarModulus
import Langlands.Global.RankinSelberg.AdelicSchwartzMellinProduct

/-! # Full-rank simple-root and last-coordinate Mellin convergence -/

noncomputable section
universe u
open NumberField MeasureTheory
open scoped Classical CategoryTheory.MonObj ENNReal NNReal
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal

variable (F : Type u) [Field F] [NumberField F]

local instance fullMellinSchemeAffine (n : ℕ) :
    AlgebraicGeometry.IsAffine (Scheme F n).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance fullMellinSchemeSmooth (n : ℕ) :
    AlgebraicGeometry.Smooth (Scheme F n).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement _ _
local instance fullMellinIdeleMeasurableSpace : MeasurableSpace (Ideles F) := borel _
local instance fullMellinIdeleBorelSpace : BorelSpace (Ideles F) := ⟨rfl⟩
local instance fullMellinIdeleLocallyCompact : LocallyCompactSpace (Ideles F) :=
  (AdelicSchwartzMellin.ideleContinuousEquiv F).symm.toHomeomorph.isClosedEmbedding.locallyCompactSpace
local instance fullMellinIdeleSecondCountable : SecondCountableTopology (Ideles F) :=
  (AdelicSchwartzMellin.ideleContinuousEquiv F).symm.toHomeomorph.secondCountableTopology

namespace AdelicSchwartzMellin

private theorem exists_product_majorant_with_scalar {n : ℕ}
    {Φ : RowVector F n → ℂ} (hΦ : EqualAnalytic.IsRowDominated F n Φ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∃ Ψ : RowVector F 1 → ℂ, Ψ ∈ schwartzBruhat F 1 ∧
      ∀ x, ‖Φ x‖ ≤ A * ∏ j : Fin n, ‖Ψ (fun _ _ => x 0 j)‖ := by
  by_cases hn : 0 < n
  · obtain ⟨Ψ, hΨ, hb⟩ := exists_product_schwartzBruhat_majorant F hn hΦ
    exact ⟨1, zero_le_one, Ψ, hΨ, fun x => by simpa only [one_mul] using hb x⟩
  · have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
    subst n
    refine ⟨‖Φ 0‖, norm_nonneg _, 0, (schwartzBruhat F 1).zero_mem, fun x => ?_⟩
    have hx : x = 0 := Subsingleton.elim _ _
    simp [hx]

/-- A Schwartz function in the first coordinates and a rank-one Schwartz
function in the last coordinate have a finite weighted torus integral,
including when there are no first coordinates. -/
theorem lintegral_split_schwartz_mellin_lt_top
    [CompactSpace (AdeleQuotient F)] {r : ℕ}
    (mu : Measure (Fin (r + 1) → Ideles F)) [mu.IsHaarMeasure]
    {φ : RowVector F r → ℂ} (hφ : φ ∈ schwartzBruhat F r)
    {ψ : RowVector F 1 → ℂ} (hψ : ψ ∈ schwartzBruhat F 1)
    (exponents : Fin (r + 1) → ℝ) (hExponents : ∀ j, 3 < exponents j) :
    ∫⁻ a : Fin (r + 1) → Ideles F,
      ‖φ (fun _ j => (a j.castSucc : Adeles F))‖ₑ *
        ‖ψ (fun _ _ => (a (Fin.last r) : Adeles F))‖ₑ *
        ∏ j, ENNReal.ofReal
          (((IdeleAbsoluteValue.full F (a j) : ℝ≥0) : ℝ) ^ exponents j)
      ∂mu < ⊤ := by
  obtain ⟨A, hA, rho, hRho, hb⟩ := exists_product_majorant_with_scalar F
    (EqualAnalytic.schwartzBruhat_properties F r hφ).2.2
  let family : Fin (r + 1) → (RowVector F 1 → ℂ) :=
    Fin.lastCases ψ (fun _ => rho)
  have hFamily : ∀ j, family j ∈ schwartzBruhat F 1 := by
    intro j
    refine Fin.lastCases ?_ (fun _ => ?_) j
    · simpa only [family, Fin.lastCases_last] using hψ
    · simpa only [family, Fin.lastCases_castSucc] using hRho
  let k : Fin (r + 1) → Ideles F → ℝ≥0∞ := fun j a =>
    ‖family j (fun _ _ => (a : Adeles F))‖ₑ *
      ENNReal.ofReal (((IdeleAbsoluteValue.full F a : ℝ≥0) : ℝ) ^ exponents j)
  have hk : ∀ j, Measurable (k j) := fun j =>
    measurable_idele_mellinKernel F
      (EqualAnalytic.schwartzBruhat_properties F 1 (hFamily j)).1 (exponents j)
  have hmajor : ∀ a : Fin (r + 1) → Ideles F,
      ‖φ (fun _ j => (a j.castSucc : Adeles F))‖ₑ *
          ‖ψ (fun _ _ => (a (Fin.last r) : Adeles F))‖ₑ *
          ∏ j, ENNReal.ofReal
            (((IdeleAbsoluteValue.full F (a j) : ℝ≥0) : ℝ) ^ exponents j) ≤
        ENNReal.ofReal A * ∏ j, k j (a j) := by
    intro a
    have hnorm :
        ‖φ (fun _ j => (a j.castSucc : Adeles F))‖ₑ ≤
          ENNReal.ofReal A *
            ∏ i : Fin r, ‖rho (fun _ _ => (a i.castSucc : Adeles F))‖ₑ := by
      simp_rw [← ofReal_norm]
      rw [← ENNReal.ofReal_prod_of_nonneg (fun _ _ => norm_nonneg _),
        ← ENNReal.ofReal_mul hA]
      exact ENNReal.ofReal_le_ofReal (hb (fun _ j => (a j.castSucc : Adeles F)))
    calc
      _ ≤ (ENNReal.ofReal A *
            ∏ i : Fin r, ‖rho (fun _ _ => (a i.castSucc : Adeles F))‖ₑ) *
          ‖ψ (fun _ _ => (a (Fin.last r) : Adeles F))‖ₑ *
          ∏ j, ENNReal.ofReal
            (((IdeleAbsoluteValue.full F (a j) : ℝ≥0) : ℝ) ^ exponents j) :=
        mul_le_mul (mul_le_mul hnorm le_rfl bot_le bot_le) le_rfl bot_le bot_le
      _ = _ := by
        simp only [k, Finset.prod_mul_distrib]
        rw [Fin.prod_univ_castSucc
          (fun j => ‖family j (fun _ _ => (a j : Adeles F))‖ₑ)]
        simp only [family, Fin.lastCases_castSucc, Fin.lastCases_last]
        ac_rfl
  let nu : Measure (Fin (r + 1) → Ideles F) :=
    Measure.pi (fun _ => (Measure.haar : Measure (Ideles F)))
  have hpi : (∫⁻ a : Fin (r + 1) → Ideles F,
      ‖φ (fun _ j => (a j.castSucc : Adeles F))‖ₑ *
        ‖ψ (fun _ _ => (a (Fin.last r) : Adeles F))‖ₑ *
        ∏ j, ENNReal.ofReal
          (((IdeleAbsoluteValue.full F (a j) : ℝ≥0) : ℝ) ^ exponents j) ∂nu) < ⊤ := by
    refine (lintegral_mono hmajor).trans_lt ?_
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    change ENNReal.ofReal A *
      (∫⁻ a, ∏ j, k j (a j) ∂Measure.pi (fun _ => Measure.haar)) < ⊤
    rw [lintegral_fin_prod_eq_prod k hk]
    apply ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    exact ENNReal.prod_lt_top fun j _ =>
      lintegral_idele_schwartzBruhat_rpow_lt_top F Measure.haar (hFamily j) (hExponents j)
  exact (lintegral_continuousMulEquiv_lt_top_iff
    (ContinuousMulEquiv.refl (Fin (r + 1) → Ideles F)) mu nu _).mpr hpi

end AdelicSchwartzMellin

/-- The Mellin exponent on each simple root and on the last diagonal
coordinate after including the inverse unipotent Haar modulus. -/
def gaugeFullRankMellinExponent (r : ℕ) (τ σ : ℝ) (j : Fin (r + 1)) : ℝ :=
  (((j : ℕ) + 1 : ℕ) : ℝ) * σ +
    Fin.lastCases 0 (fun _ : Fin r => -τ) j +
    gaugeInverseModulusRootExponent r j

/-- The gauge, determinant and inverse Haar weights combine into their
coordinate Mellin exponents. -/
theorem gaugeFullRank_scalarWeight (r : ℕ) (τ σ : ℝ)
    (d : Fin (r + 1) → Ideles F) :
    ENNReal.ofReal (gaugeSimpleRootNormProduct F r d ^ (-τ)) *
        ENNReal.ofReal (detNorm F (r + 1) (gaugeDiagonalPoint F (r + 1) d) ^ σ) *
        gaugeDiagonalInverseHaarWeight F r d =
      ∏ j, ENNReal.ofReal
        (((IdeleAbsoluteValue.full F (gaugeBlockRootIdeles F r d j) : ℝ≥0) : ℝ) ^
          gaugeFullRankMellinExponent r τ σ j) := by
  let a : Fin (r + 1) → ℝ := fun j =>
    ((IdeleAbsoluteValue.full F (gaugeBlockRootIdeles F r d j) : ℝ≥0) : ℝ)
  have ha : ∀ j, 0 < a j := fun j => IdeleAbsoluteValue.full_pos F _
  have hsimple : gaugeSimpleRootNormProduct F r d ^ (-τ) =
      ∏ j, a j ^ (Fin.lastCases (0 : ℝ) (fun _ : Fin r => -τ) j : ℝ) := by
    rw [Fin.prod_univ_castSucc]
    simp only [Fin.lastCases_castSucc, Fin.lastCases_last, Real.rpow_zero, mul_one]
    have hprod : gaugeSimpleRootNormProduct F r d = ∏ i : Fin r, a i.castSucc := by
      simp only [gaugeSimpleRootNormProduct, a, gaugeBlockRootIdeles,
        GaugeTorusCoordinates.blockRoots_castSucc, gaugeSimpleRootIdeles]
    rw [hprod, ← Real.finsetProd_rpow _ _ (fun (j : Fin r) _ => (ha j.castSucc).le)]
  have hdet : detNorm F (r + 1) (gaugeDiagonalPoint F (r + 1) d) ^ σ =
      ∏ j, a j ^ ((((j : ℕ) + 1 : ℕ) : ℝ) * σ) := by
    rw [detNorm_gaugeDiagonalPoint_blockRoots,
      ← Real.finsetProd_rpow _ _ (fun j _ => pow_nonneg (ha j).le _)]
    apply Finset.prod_congr rfl
    intro j _
    exact (Real.rpow_natCast_mul (ha j).le _ σ).symm
  rw [hsimple, hdet, gaugeDiagonalInverseHaarWeight_eq_rootWeights]
  rw [ENNReal.ofReal_prod_of_nonneg
    (fun j _ => Real.rpow_nonneg (ha j).le _)]
  rw [ENNReal.ofReal_prod_of_nonneg
    (fun j _ => Real.rpow_nonneg (ha j).le _)]
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j _
  change ENNReal.ofReal (a j ^ _) * ENNReal.ofReal (a j ^ _) *
    ENNReal.ofReal (a j ^ _) = ENNReal.ofReal (a j ^ _)
  rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (ha j).le _),
    ← Real.rpow_add (ha j),
    ← ENNReal.ofReal_mul (Real.rpow_nonneg (ha j).le _),
    ← Real.rpow_add (ha j)]
  congr 2
  simp only [gaugeFullRankMellinExponent]
  ring

/-- One threshold makes all full-rank coordinate exponents exceed three. -/
theorem gaugeFullRankMellinExponent_gt_three (r : ℕ) {τ σ : ℝ}
    (hτ : 0 ≤ τ)
    (hσ : τ + 3 + ∑ j : Fin (r + 1),
      ((((j : ℕ) + 1) * (r - (j : ℕ)) : ℕ) : ℝ) < σ)
    (j : Fin (r + 1)) : 3 < gaugeFullRankMellinExponent r τ σ j := by
  have hsum : 0 ≤ ∑ j : Fin (r + 1),
      ((((j : ℕ) + 1) * (r - (j : ℕ)) : ℕ) : ℝ) :=
    Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
  have hσpos : 0 ≤ σ := by linarith
  have hj : (1 : ℝ) ≤ (((j : ℕ) + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le (j : ℕ))
  have hweight := mul_le_mul_of_nonneg_right hj hσpos
  have hmult :
      ((((j : ℕ) + 1) * (r - (j : ℕ)) : ℕ) : ℝ) ≤
        ∑ i : Fin (r + 1), ((((i : ℕ) + 1) * (r - (i : ℕ)) : ℕ) : ℝ) :=
    Finset.single_le_sum
      (f := fun i : Fin (r + 1) => ((((i : ℕ) + 1) * (r - (i : ℕ)) : ℕ) : ℝ))
      (fun _ _ => Nat.cast_nonneg _) (Finset.mem_univ j)
  have hsplit : -τ ≤ Fin.lastCases 0 (fun _ : Fin r => -τ) j := by
    refine Fin.lastCases ?_ (fun _ => ?_) j
    · simpa only [Fin.lastCases_last] using neg_nonpos.mpr hτ
    · simp only [Fin.lastCases_castSucc, le_refl]
  dsimp only [gaugeFullRankMellinExponent, gaugeInverseModulusRootExponent]
  linarith

/-- The full-rank diagonal majorant is integrable in one half-plane uniform
in both Schwartz functions and in the Haar normalization. -/
theorem lintegral_gaugeSchwartzTorusMajorant_lt_top_of_large
    [CompactSpace (AdeleQuotient F)] (r : ℕ)
    (mu : Measure (Fin (r + 1) → Ideles F)) [mu.IsHaarMeasure]
    {φ : RowVector F r → ℂ} (hφ : φ ∈ schwartzBruhat F r)
    {ψ : RowVector F 1 → ℂ} (hψ : ψ ∈ schwartzBruhat F 1)
    {τ σ : ℝ} (hτ : 0 ≤ τ)
    (hσ : τ + 3 + ∑ j : Fin (r + 1),
      ((((j : ℕ) + 1) * (r - (j : ℕ)) : ℕ) : ℝ) < σ) :
    ∫⁻ d : Fin (r + 1) → Ideles F,
      gaugeDiagonalInverseHaarWeight F r d *
        ENNReal.ofReal (gaugeSimpleRootNormProduct F r d ^ (-τ)) *
        ‖φ (gaugeSimpleRootRow F r d)‖ₑ *
        ‖ψ (fun _ _ => (d (Fin.last r) : Adeles F))‖ₑ *
        ENNReal.ofReal (detNorm F (r + 1) (gaugeDiagonalPoint F (r + 1) d) ^ σ)
      ∂mu < ⊤ := by
  let f : (Fin (r + 1) → Ideles F) → ℝ≥0∞ := fun a =>
    ‖φ (fun _ j => (a j.castSucc : Adeles F))‖ₑ *
      ‖ψ (fun _ _ => (a (Fin.last r) : Adeles F))‖ₑ *
      ∏ j, ENNReal.ofReal
        (((IdeleAbsoluteValue.full F (a j) : ℝ≥0) : ℝ) ^
          gaugeFullRankMellinExponent r τ σ j)
  have hint : ∫⁻ a, f a ∂mu < ⊤ :=
    AdelicSchwartzMellin.lintegral_split_schwartz_mellin_lt_top F mu hφ hψ
      (gaugeFullRankMellinExponent r τ σ)
      (gaugeFullRankMellinExponent_gt_three r hτ hσ)
  have hroot := (GaugeTorusCoordinates.lintegral_blockRoots_lt_top_iff r mu f).mpr hint
  convert hroot using 1
  apply lintegral_congr
  intro d
  have hrow : (fun (_ : Fin 1) (j : Fin r) =>
      ((GaugeTorusCoordinates.blockRoots (G := Ideles F) r d j.castSucc :
        Ideles F) : Adeles F)) =
        gaugeSimpleRootRow F r d := by
    ext i j
    simp only [GaugeTorusCoordinates.blockRoots_castSucc, gaugeSimpleRootRow,
      gaugeSimpleRootIdeles]
  dsimp only [f]
  rw [hrow, GaugeTorusCoordinates.blockRoots_last]
  change _ = ‖φ (gaugeSimpleRootRow F r d)‖ₑ *
    ‖ψ (fun _ _ => (d (Fin.last r) : Adeles F))‖ₑ *
    ∏ j, ENNReal.ofReal
      (((IdeleAbsoluteValue.full F (gaugeBlockRootIdeles F r d j) : ℝ≥0) : ℝ) ^
        gaugeFullRankMellinExponent r τ σ j)
  rw [← gaugeFullRank_scalarWeight F r τ σ d]
  ac_rfl

end Langlands.Global.RankinSelbergGlobal
