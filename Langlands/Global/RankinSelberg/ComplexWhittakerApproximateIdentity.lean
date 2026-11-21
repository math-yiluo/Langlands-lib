import Langlands.Global.RankinSelberg.ComplexCompactAverageGrowth
import Langlands.Global.RankinSelberg.ComplexCompactProbeBounds
import Langlands.Global.RankinSelberg.ComplexOppositeNonzero

/-! # Quantitative compact approximate identities for exact complex Whittaker intertwiners -/

noncomputable section

open MeasureTheory
open scoped Classical Matrix.Norms.Operator Langlands.Archimedean.ComplexDuality

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexWhittakerApproximateIdentity

open Langlands.Archimedean (unitaryCompact complexStandardRep principalSeriesRep_apply_coe)
open Langlands.Archimedean.ComplexDuality (unitaryHaar)
open Langlands.LocalFactor.Archimedean (ComplexCharacterData)
open GeneralLinear (upperEntryCoordinates upperEntryCoordinates_apply)
open ComplexCompactAverageGrowth (complexCompactAverageGrowth)
open ComplexCompactDualProbe (dualSection)
open ComplexCompactProbeBounds (CompactBound CompactRightDifferenceBound complexCompactProbeBounds)
open ComplexModulusOpenCell (complexEntryLebesgue groupTranspose)
open ComplexNormalizedCompactAverage (oppositeMass averageScale contractedPair inverseWeight complexNormalizedCompactAverage)
open ComplexOppositeCompactChart (Coordinates oppositePoint_upperEntries)
open ComplexOppositeDilation (contractionDiagonal contraction contraction_entry)
open ComplexOppositeMoment (norm_upperEntries)
open ComplexOppositeNonzero (complexOppositeNonzero)

local notation "G" => fun n => Langlands.GeneralLinear n ℂ
local notation "U" => fun n => unitaryCompact ℂ n
local notation "N" => fun n => GeneralLinear.upperUnipotent n ℂ
local notation "UC" => fun n => Matrix.unitaryGroup (Fin n) ℂ
local notation "Std" => Automorphic.complexStandardKFinite

local instance approximateIdentityNMeasurable (n : ℕ) : MeasurableSpace (N n) := borel _
local instance approximateIdentityNBorel (n : ℕ) : BorelSpace (N n) := ⟨rfl⟩

private theorem norm_contractedCoordinates {n : ℕ} {ε : ℝ} (hε : 0 < ε) (hle : ε ≤ 1) (u : N n) :
    ‖upperEntryCoordinates n (contraction n hε u)‖ ≤ ε * ‖upperEntryCoordinates n u‖ := by
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg hε.le (norm_nonneg _))).mpr
  intro ij
  rw [upperEntryCoordinates_apply, contraction_entry hε u ij.2, norm_smul,
    Real.norm_of_nonneg (pow_nonneg hε.le _)]
  have hgap : ij.val.2.val - ij.val.1.val ≠ 0 := by
    have h : ij.val.1.val < ij.val.2.val := ij.2
    omega
  apply mul_le_mul (pow_le_of_le_one hε.le hle hgap) _ (norm_nonneg _) hε.le
  simpa only [upperEntryCoordinates_apply] using norm_le_pi_norm (upperEntryCoordinates n u) ij

private theorem compactRep_apply {n : ℕ} {ds : List ComplexCharacterData} (k : UC n)
    (f : Std n ds) (g : G n) : (complexStandardRep n ds k f).val g = f.val (g * Unitary.toUnits k) := by
  exact congrFun (principalSeriesRep_apply_coe ℂ n (Langlands.Archimedean.complexPositionCharacter ds) k f) g

private theorem average_commutes_compact {n : ℕ} {ds : List ComplexCharacterData}
    (A : Std n ds →ₗ[ℂ] Std n ds) (f₀ : Std n ds) (g : G n) (c : ℂ)
    (h : ∀ (f : Std n ds) (y : G n), (A f).val y =
      c * ∫ k : U n, inverseWeight f k * f₀.val (y * k.val * g) ∂unitaryHaar n)
    (k : UC n) (f : Std n ds) : A (complexStandardRep n ds k f) = complexStandardRep n ds k (A f) := by
  apply Subtype.ext
  funext y
  change (A (complexStandardRep n ds k f)).val y = (complexStandardRep n ds k (A f)).val y
  rw [compactRep_apply, h, h]
  congr 1
  let t : U n := ⟨Unitary.toUnits k, k.2⟩
  conv_lhs => rw [← integral_mul_left_eq_self _ t]
  apply integral_congr_ae (ae_of_all _ fun u => ?_)
  change (complexStandardRep n ds k f).val ((t * u : U n).val⁻¹) *
      f₀.val (y * (t * u : U n).val * g) = f.val u.val⁻¹ * f₀.val (y * t.val * u.val * g)
  rw [compactRep_apply, Subgroup.coe_mul, mul_inv_rev]
  change f.val (u.val⁻¹ * t.val⁻¹ * t.val) * _ = _
  rw [mul_assoc u.val⁻¹, inv_mul_cancel, mul_one, ← mul_assoc y]

/-- Every exact complex Whittaker intertwiner admits compact-equivariant approximate identity
operators with uniform compact norm bounds, first-order error, and polynomial sampling at one. -/
def ComplexWhittakerApproximateIdentityStatement : Prop :=
  ∀ (r : ℕ) (ds : List ComplexCharacterData) (a : ℂˣ)
    (B : Std (r + 1) ds →ₗ[ℂ] (G (r + 1) → ℂ)), IsComplexWhittakerIntertwiner r ds a B →
  ∃ (C : ℝ) (P : ℕ), 1 ≤ C ∧
    ∀ (ε : ℝ), 0 < ε → ε ≤ 1 → ∃ A : Std (r + 1) ds →ₗ[ℂ] Std (r + 1) ds,
      (∀ (k : UC (r + 1)) (f : Std (r + 1) ds),
        A (complexStandardRep (r + 1) ds k f) = complexStandardRep (r + 1) ds k (A f)) ∧
      (∀ f R, CompactBound f R → CompactBound (A f) (C * R)) ∧
      (∀ f R D, 0 ≤ D → CompactBound f R → CompactRightDifferenceBound f D →
        CompactBound (f - A f) (C * ε * (R + D))) ∧
      ∀ f R, CompactBound f R → ‖B (A f) 1‖ ≤ C * R * (ε ^ P)⁻¹

set_option maxHeartbeats 1200000 in
theorem complexWhittakerApproximateIdentity : ComplexWhittakerApproximateIdentityStatement := by
  intro r ds a B hB
  let n := r + 1
  let ν := complexEntryLebesgue n
  let e := upperEntryCoordinates (K := ℂ) n
  obtain ⟨M, H, E, hH, hE, hProbe⟩ := complexCompactProbeBounds r ds
  obtain ⟨f₀, hMoment, hMass⟩ := complexOppositeNonzero n ds (M + 1)
  have hm : oppositeMass f₀ ≠ 0 := fun h => hMass.ne' (by
    change (oppositeMass f₀).re = 0
    rw [h, Complex.zero_re])
  let F : N n → ℂ := fun u => f₀.val (groupTranspose u.val)
  let W (u : N n) := (1 + ‖e u‖) ^ (M + 1)
  let A₀ (u : N n) := W u * ‖F u‖
  have hW (u : N n) : 1 ≤ W u := one_le_pow₀ (le_add_of_nonneg_right (norm_nonneg _))
  have hiW : Integrable (fun u => W u • F u) ν := by
    simpa only [W, F, e, norm_upperEntries] using hMoment
  have hA₀ : Integrable A₀ ν := by
    apply hiW.norm.congr
    exact ae_of_all _ fun u => by
      change ‖W u • F u‖ = W u * ‖F u‖
      rw [norm_smul, Real.norm_of_nonneg (zero_le_one.trans (hW u))]
  have hFc : Continuous F := f₀.2.1.1.continuous.comp
    (((GeneralLinear.continuous_inverseTranspose n ℂ).comp continuous_inv).comp continuous_subtype_val)
  have hF : Integrable F ν := hA₀.mono' hFc.aestronglyMeasurable
    (ae_of_all _ fun u => le_mul_of_one_le_left (norm_nonneg _) (hW u))
  let J := ∫ u : N n, A₀ u ∂ν
  let D₀ := ‖(oppositeMass f₀)⁻¹‖
  obtain ⟨c, hc, hAverage⟩ := complexNormalizedCompactAverage r
  obtain ⟨Cw, P, _, hSample⟩ := complexCompactAverageGrowth r c ds a B hc hB f₀
  let C₀ := D₀ * H * J
  let C₁ := D₀ * E * J
  let C := max 1 (max Cw (max C₀ C₁))
  have hCw : Cw ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have hC₀ : C₀ ≤ C := (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hC₁ : C₁ ≤ C := (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  refine ⟨C, P, le_max_left _ _, fun ε hε hle => ?_⟩
  obtain ⟨A, hOpp, hStd, hWh⟩ := hAverage ds a B hB f₀ hm ε hε
  refine ⟨A, average_commutes_compact A f₀ _ _ hStd, ?_, ?_, ?_⟩
  · intro f R hR x
    have hR₀ := (norm_nonneg _).trans (hR x)
    have hNorm : ‖∫ u : N n, contractedPair f f₀ x hε u ∂ν‖ ≤ H * R * J := by
      have hi := norm_integral_le_of_norm_le (f := contractedPair f f₀ x hε)
        (hA₀.const_mul (H * R)) (ae_of_all _ fun u => ?_)
      · simpa only [integral_const_mul, J] using hi
      · let z : Coordinates n := e (contraction n hε u)
        have hz : ‖z‖ ≤ ‖e u‖ := (norm_contractedCoordinates hε hle u).trans
          (mul_le_of_le_one_left (norm_nonneg _) hle)
        have hp : (1 + ‖z‖) ^ M ≤ W u :=
          (pow_le_pow_left₀ (by positivity) (add_le_add le_rfl hz) _).trans
            (pow_le_pow_right₀ (le_add_of_nonneg_right (norm_nonneg _)) (Nat.le_succ M))
        have hk := (hProbe f x z R 0 le_rfl hR).1
        rw [show ComplexOppositeCompactChart.oppositePoint z = groupTranspose (contraction n hε u).val from
          oppositePoint_upperEntries _] at hk
        change ‖contractedPair f f₀ x hε u‖ ≤ H * R * A₀ u
        rw [contractedPair, norm_mul]
        calc
          _ ≤ ‖F u‖ * (H * R * (1 + ‖z‖) ^ M) := mul_le_mul_of_nonneg_left hk (norm_nonneg _)
          _ ≤ ‖F u‖ * (H * R * W u) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hp (mul_nonneg hH hR₀)) (norm_nonneg _)
          _ = _ := by dsimp only [A₀]; ring
    rw [(hOpp f x).2, norm_mul]
    calc
      _ ≤ D₀ * (H * R * J) := mul_le_mul_of_nonneg_left hNorm (norm_nonneg _)
      _ = C₀ * R := by dsimp only [C₀]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hC₀ hR₀
  · intro f R D hD hR hd x
    let y := f.val (Unitary.toUnits x)
    let T (u : N n) := dualSection f x (groupTranspose (contraction n hε u).val)
    have hR₀ := (norm_nonneg _).trans (hR x)
    have hRD := add_nonneg hR₀ hD
    have hInt : (∫ u : N n, F u * (T u - y) ∂ν) =
        (∫ u : N n, contractedPair f f₀ x hε u ∂ν) - oppositeMass f₀ * y := by
      have hFT : Integrable (fun u : N n => F u * T u) ν := (hOpp f x).1
      simp_rw [mul_sub]
      rw [integral_sub hFT (hF.mul_const y), integral_mul_const]
      rfl
    have hEq : (A f).val (Unitary.toUnits x) - y =
        (oppositeMass f₀)⁻¹ * ∫ u : N n, F u * (T u - y) ∂ν := by
      rw [(hOpp f x).2, hInt, mul_sub, inv_mul_cancel_left₀ hm]
    have hNorm : ‖∫ u : N n, F u * (T u - y) ∂ν‖ ≤ E * (R + D) * ε * J := by
      have hi := norm_integral_le_of_norm_le (f := fun u => F u * (T u - y))
        (hA₀.const_mul (E * (R + D) * ε)) (ae_of_all _ fun u => ?_)
      · simpa only [integral_const_mul, J] using hi
      · let z : Coordinates n := e (contraction n hε u)
        have hz : ‖z‖ ≤ ε * ‖e u‖ := norm_contractedCoordinates hε hle u
        have hz₁ := hz.trans (mul_le_of_le_one_left (norm_nonneg _) hle)
        have hp : (1 + ‖z‖) ^ M ≤ (1 + ‖e u‖) ^ M := pow_le_pow_left₀ (by positivity)
          (add_le_add le_rfl hz₁) _
        have hk := (hProbe f x z R D hD hR).2 hd
        rw [show ComplexOppositeCompactChart.oppositePoint z = groupTranspose (contraction n hε u).val from
          oppositePoint_upperEntries _] at hk
        have hb : ‖T u - y‖ ≤ E * (R + D) * ε * W u := by
          calc
            _ ≤ E * (R + D) * ‖z‖ * (1 + ‖z‖) ^ M := hk
            _ ≤ E * (R + D) * (ε * (1 + ‖e u‖)) * (1 + ‖e u‖) ^ M :=
              mul_le_mul (mul_le_mul_of_nonneg_left (hz.trans (mul_le_mul_of_nonneg_left
                (le_add_of_nonneg_left zero_le_one) hε.le)) (mul_nonneg hE hRD)) hp (by positivity) (by positivity)
            _ = _ := by dsimp only [W]; rw [pow_succ]; ring
        change ‖F u * (T u - y)‖ ≤ E * (R + D) * ε * A₀ u
        rw [norm_mul]
        exact (mul_le_mul_of_nonneg_left hb (norm_nonneg _)).trans_eq (by dsimp only [A₀]; ring)
    change ‖y - (A f).val (Unitary.toUnits x)‖ ≤ _
    rw [norm_sub_rev, hEq, norm_mul]
    calc
      _ ≤ D₀ * (E * (R + D) * ε * J) := mul_le_mul_of_nonneg_left hNorm (norm_nonneg _)
      _ = C₁ * ε * (R + D) := by dsimp only [C₁]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC₁ hε.le) hRD
  · intro f R hR
    have hR₀ := (norm_nonneg _).trans (hR 1)
    rw [hWh]
    simp only [one_mul]
    refine (hSample ε hε hle f R (fun k => ?_)).trans ?_
    · let x : UC n := ⟨k.val.val, k.2⟩
      exact (show Unitary.toUnits x = k.val from Units.ext rfl) ▸ hR x
    · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCw hR₀) (by positivity)

end Langlands.Global.RankinSelbergGlobal.ComplexWhittakerApproximateIdentity
