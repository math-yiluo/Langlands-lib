import Langlands.Correspondence.HenniartWeilArtinConductorExistenceProof
import Langlands.LocalFactor.Ramification.InertiaConductorRefinementProof
import Langlands.Weil.Representation.IsomorphismInvarianceProof

/-! # The Swan label of an irreducible Weil class -/

noncomputable section

namespace Langlands.Henniart.Numerical

open Correspondence FiniteRepresentation Weil.Local Module MeasureTheory
open Ramification.Padic Ramification.Padic.InertiaConductorRefinement Ramification.HerbrandBridge
open VirtualRepresentation.LocalWeil.Ramification

universe uK uW

variable {p : ℕ} [Fact p.Prime] (K : PadicField.{uK} p)

private theorem artin_eq_codimension_add_rank_mul_break
    (A : FiniteRepresentation.{0, uK, uW} ℂ (localWeilGroup K))
    (hA : A.IsContinuous) (hi : A.IsIrreducible)
    (P : FiniteInertiaPresentation K A)
    (hP : Function.Surjective (weilInertiaRestriction K P.extension)) :
    (P.artinConductor hP : ℝ) =
      ((A.rank : ℝ) - finrank ℂ (upperFixedSpace K A 0)) + (A.rank : ℝ) * lastBreak K A := by
  let T := (absoluteFiniteExtension K P.extension).canonicalTopologicalData
  let ρ := P.representation hP
  let b := lastBreak K A
  let B := max (herbrandPhi T K.Carrier (ramificationCutoff T K.Carrier)) b
  have hb : 0 ≤ b := lastBreak_nonneg K A
  have hbB : b ≤ B := le_max_right _ _
  have hB : herbrandPhi T K.Carrier (ramificationCutoff T K.Carrier) ≤ B := le_max_left _ _
  obtain ⟨hlo, hhi⟩ := weilIrreduciblePositiveThresholds K A hA hi
  have hcod (r : ℝ) (hr : 0 ≤ r) : upperCodimension T K.Carrier ρ r =
      ((A.rank : ℝ) - finrank ℂ (upperFixedSpace K A r)) := by
    unfold upperCodimension
    rw [presentationUpperFixedComparison K A P hP r hr]
    rfl
  calc
    (P.artinConductor hP : ℝ) = upperCodimension T K.Carrier ρ 0 +
        ∫ r in (0 : ℝ)..B, upperCodimension T K.Carrier ρ r :=
      inertiaArtinConductor_eq_integral T K.Carrier ρ hB
    _ = ((A.rank : ℝ) - finrank ℂ (upperFixedSpace K A 0)) + (A.rank : ℝ) * b := by
      rw [hcod 0 le_rfl]
      congr 1
      rw [← intervalIntegral.integral_add_adjacent_intervals
        (upperCodimension_intervalIntegrable T K.Carrier ρ 0 b)
        (upperCodimension_intervalIntegrable T K.Carrier ρ b B)]
      have hfirst : (∫ r in (0 : ℝ)..b, upperCodimension T K.Carrier ρ r) = (A.rank : ℝ) * b := by
        rw [intervalIntegral.integral_congr_Ioo_of_le hb (g := fun _ => (A.rank : ℝ)),
          intervalIntegral.integral_const, smul_eq_mul, sub_zero, mul_comm]
        intro r hr
        rw [hcod r hr.1.le, (hlo r hr.1).mp hr.2.le, finrank_bot, Nat.cast_zero, sub_zero]
      have hlast : (∫ r in b..B, upperCodimension T K.Carrier ρ r) = 0 := by
        rw [intervalIntegral.integral_congr_Ioo_of_le hbB (g := fun _ => (0 : ℝ)),
          intervalIntegral.integral_zero]
        intro r hr
        rw [hcod r (hb.trans hr.1.le), (hhi r (hb.trans_lt hr.1)).mp hr.1, finrank_top]
        exact sub_self (A.rank : ℝ)
      rw [hfirst, hlast, add_zero]

private theorem cast_sub_rank_eq_rank_mul_break
    (A : FiniteRepresentation.{0, uK, uW} ℂ (localWeilGroup K))
    (hA : A.IsContinuous) (hi : A.IsIrreducible)
    (P : FiniteInertiaPresentation K A)
    (hP : Function.Surjective (weilInertiaRestriction K P.extension)) (a : ℕ)
    (ha : P.artinConductor hP = (a : ℚ)) :
    ((a - A.rank : ℕ) : ℝ) = (A.rank : ℝ) * lastBreak K A := by
  have h := artin_eq_codimension_add_rank_mul_break K A hA hi P hP
  rw [ha, Rat.cast_natCast] at h
  rcases (lastBreak_nonneg K A).eq_or_lt with h0 | hpos
  · rw [← h0, mul_zero, add_zero] at h
    have hle : a ≤ A.rank := by exact_mod_cast (show (a : ℝ) ≤ A.rank by linarith)
    simp [Nat.sub_eq_zero_of_le hle, ← h0]
  · have hle : upperFixedSpace K A 0 ≤ upperFixedSpace K A (lastBreak K A) := by
      intro v hv
      apply (mem_upperFixedSpace K A _ v).mpr
      intro w hw
      exact (mem_upperFixedSpace K A 0 v).mp hv w (upperGroup_antitone K hpos.le hw)
    have hbot : upperFixedSpace K A 0 = ⊥ := by
      rw [((weilIrreduciblePositiveThresholds K A hA hi).1 _ hpos).mp le_rfl] at hle
      exact le_bot_iff.mp hle
    rw [hbot, finrank_bot, Nat.cast_zero, sub_zero] at h
    have hr : A.rank ≤ a := by
      exact_mod_cast (show (A.rank : ℝ) ≤ a by
        rw [h]; exact le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _) hpos.le))
    rw [Nat.cast_sub hr, h, add_sub_cancel_left]

/-- The numerical Swan label is the rank times the last break of a genuine representative.
At break zero, the Artin conductor need only be at most the rank. -/
theorem hasWeilSwan_iff_rank_mul_lastBreak {k : ℕ}
    (σ : IrreducibleWeilClass.{uK, uW} K k.succPNat)
    (A : FiniteRepresentation.{0, uK, uW} ℂ (localWeilGroup K))
    (hA : classOf A = weilClassForget K σ) (s : ℕ) :
    HasWeilSwan K σ s ↔ (s : ℝ) = (k + 1 : ℕ) * lastBreak K A := by
  have aux (a : ℕ) (ha : HasArtinConductor K σ a) :
      ((a - (k + 1) : ℕ) : ℝ) = (k + 1 : ℕ) * lastBreak K A := by
    obtain ⟨C, P, hP, hC, hArtin⟩ := ha
    obtain ⟨R, hR⟩ := Quotient.exists_rep σ.val
    have hRclass : classOf R.val = weilClassForget K σ := congrArg (forgetPropertyClass _) hR
    obtain ⟨e⟩ := (classOf_eq_iff _ _).mp (hC.trans hRclass.symm)
    obtain ⟨e'⟩ := (classOf_eq_iff _ _).mp (hC.trans hA.symm)
    have hc : C.IsContinuous := (isContinuous_iff_of_equiv e).mpr R.property.1
    have hi : C.IsIrreducible := (Weil.IsomorphismInvariance.irreducible_iff e).mpr R.property.2
    have hr : C.rank = k + 1 := (congrArg classRank hC).trans σ.property
    have h := cast_sub_rank_eq_rank_mul_break K C hc hi P hP a hArtin
    rw [hr, lastBreak_equiv K e'] at h
    exact h
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact aux a ha
  · intro hs
    obtain ⟨a, ha⟩ := weilArtinConductorExistence p K k σ
    exact ⟨a, ha, Nat.cast_injective (R := ℝ) ((aux a ha).trans hs.symm)⟩

/-- The natural-valued Swan label, normalized by the actual representative's last break. -/
noncomputable def weilSwanLabel {k : ℕ}
    (σ : IrreducibleWeilClass.{uK, uW} K k.succPNat) : ℕ :=
  (Classical.choose (weilArtinConductorExistence p K k σ)) - (k + 1)

/-- Any given occurrence of the label agrees with the chosen one. -/
theorem hasWeilSwan_iff_eq_label {k : ℕ}
    (σ : IrreducibleWeilClass.{uK, uW} K k.succPNat) (s : ℕ) :
    HasWeilSwan K σ s ↔ s = weilSwanLabel K σ := by
  obtain ⟨A, hA⟩ := Quotient.exists_rep σ.val
  have h := hasWeilSwan_iff_rank_mul_lastBreak K σ A.val (congrArg (forgetPropertyClass _) hA)
  have hl : HasWeilSwan K σ (weilSwanLabel K σ) :=
    ⟨_, Classical.choose_spec (weilArtinConductorExistence p K k σ), rfl⟩
  exact ⟨fun hs => Nat.cast_injective (R := ℝ) ((h s).mp hs |>.trans ((h _).mp hl).symm),
    fun hs => hs.symm ▸ hl⟩

end Langlands.Henniart.Numerical
