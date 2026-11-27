import Langlands.Correspondence.HenniartLocalNumerical
import Langlands.LocalFactor.Ramification.LocalWeilBreakProof

/-!
# Swan conductors of local Weil classes from their last breaks

Over a nonarchimedean local field, the rank times the last break computes the
Swan conductor of an irreducible Weil class. This value tests the natural Swan
exponent used in the refined orbit counts.
-/

noncomputable section

set_option autoImplicit false

namespace Langlands.Henniart.LocalNumerical

open FiniteRepresentation Ramification Ramification.Local Ramification.Local.SepClosed
open VirtualRepresentation.LocalWeil.SepClosed.Ramification

universe uK uΩ uW

variable (K : Type uK) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  (Ω : Type uΩ) [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]

local notation "W" =>
  (@Weil.Local.SepClosed.localWeilGroup K _ _ _ _ Ω _ _ _ (IsSepClosure.sep_closed K))

/-- The Swan conductor of a continuous irreducible Weil class, expressed as
rank times its last upper break. -/
def weilSwanConductor {n : ℕ+} (σ : IrreducibleWeilClass.{uK, uΩ, uW} K Ω n) : ℝ :=
  ((n : ℕ) : ℝ) * classLastBreak K Ω (weilClassForget K Ω σ)

/-- A representative computes the class Swan conductor using its own last break. -/
theorem weilSwanConductor_eq_rank_mul_lastBreak {n : ℕ+}
    {σ : IrreducibleWeilClass.{uK, uΩ, uW} K Ω n}
    {A : FiniteRepresentation.{0, uΩ, uW} ℂ W}
    (hA : classOf A = weilClassForget K Ω σ) :
    weilSwanConductor K Ω σ = ((n : ℕ) : ℝ) * lastBreak K Ω A := by
  rw [weilSwanConductor, ← hA, classLastBreak_classOf]

private theorem representative_continuous_irreducible {n : ℕ+}
    {σ : IrreducibleWeilClass.{uK, uΩ, uW} K Ω n}
    {A : FiniteRepresentation.{0, uΩ, uW} ℂ W}
    (hA : classOf A = weilClassForget K Ω σ) : A.IsContinuous ∧ A.IsIrreducible := by
  obtain ⟨B, hB⟩ := Quotient.exists_rep σ.val
  have hclass : classOf B.val = weilClassForget K Ω σ :=
    congrArg (forgetPropertyClass _) hB
  obtain ⟨e⟩ := (classOf_eq_iff A B.val).mp (hA.trans hclass.symm)
  exact ⟨(isContinuous_iff_of_equiv e).mpr B.property.1,
    (Weil.IsomorphismInvariance.irreducible_iff e).mpr B.property.2⟩

private theorem representative_rank {n : ℕ+}
    {σ : IrreducibleWeilClass.{uK, uΩ, uW} K Ω n}
    {A : FiniteRepresentation.{0, uΩ, uW} ℂ W}
    (hA : classOf A = weilClassForget K Ω σ) : A.rank = (n : ℕ) := by
  rw [← classRank_classOf, hA]
  exact σ.property

/-- Each finite inertia presentation gives the same Swan conductor on the
class. -/
theorem weilSwanConductor_eq_presentation {n : ℕ+}
    {σ : IrreducibleWeilClass.{uK, uΩ, uW} K Ω n}
    {A : FiniteRepresentation.{0, uΩ, uW} ℂ W}
    (hA : classOf A = weilClassForget K Ω σ)
    (P : FiniteInertiaPresentation K Ω A)
    (hP : Function.Surjective (weilInertiaRestriction K Ω P.extension)) :
    weilSwanConductor K Ω σ = (P.swanConductor hP : ℝ) := by
  obtain ⟨hc, hi⟩ := representative_continuous_irreducible K Ω hA
  rw [weilSwanConductor_eq_rank_mul_lastBreak K Ω hA, ← representative_rank K Ω hA]
  exact (weilIrreducibleSwanBreak K Ω A hc hi P hP).symm

set_option maxHeartbeats 600000 in
private theorem fixedCodimension_eq_rank_of_pos_lastBreak
    (A : FiniteRepresentation.{0, uΩ, uW} ℂ W) (hc : A.IsContinuous)
    (hi : A.IsIrreducible) (P : FiniteInertiaPresentation K Ω A)
    (hP : Function.Surjective (weilInertiaRestriction K Ω P.extension))
    (hb : 0 < lastBreak K Ω A) :
    fixedCodimension _ (P.representation hP) ⊤ = A.rank := by
  let T := finiteTopologicalData K Ω P.extension
  let ρ := P.representation hP
  have hbot := ((weilIrreduciblePositiveThresholds K Ω A hc hi).1 _ hb).mp le_rfl
  have hzero : upperFixedSpace K Ω A 0 = ⊥ := by
    apply le_bot_iff.mp
    rw [← hbot]
    intro v hv
    apply (mem_upperFixedSpace K Ω A _ v).mpr
    intro w hw
    exact (mem_upperFixedSpace K Ω A 0 v).mp hv w (upperGroup_antitone K Ω hb.le hw)
  have htop : (Local.upperRamificationGroup T K 0).subgroupOf (Local.inertia T K) = ⊤ :=
    (congrArg (fun H => H.subgroupOf (Local.inertia T K))
      (Local.upperRamificationGroup_zero T K)).trans (Subgroup.subgroupOf_self (Local.inertia T K))
  have hinertia : Local.inertiaUpperFixedVectors T K ρ 0 = fixedVectors ρ ⊤ :=
    congrArg (fixedVectors ρ) htop
  have hfix : fixedVectors ρ ⊤ = ⊥ :=
    hinertia.symm.trans ((presentationUpperFixedComparison K Ω A P hP 0 le_rfl).symm.trans hzero)
  change A.rank - Module.finrank ℂ (fixedVectors ρ ⊤) = A.rank
  rw [hfix, finrank_bot, Nat.sub_zero]

private theorem exists_artin_sub_rank_iff
    (A : FiniteRepresentation.{0, uΩ, uW} ℂ W) (hc : A.IsContinuous)
    (hi : A.IsIrreducible) (P : FiniteInertiaPresentation K Ω A)
    (hP : Function.Surjective (weilInertiaRestriction K Ω P.extension)) (s : ℕ) :
    (∃ a : ℕ, P.artinConductor hP = (a : ℚ) ∧ a - A.rank = s) ↔
      (s : ℝ) = (A.rank : ℝ) * lastBreak K Ω A := by
  let d := fixedCodimension _ (P.representation hP) ⊤
  have hd : d ≤ A.rank := Nat.sub_le ..
  have hartin : P.artinConductor hP = P.swanConductor hP + (d : ℚ) :=
    finiteUpperBreakArtinIdentity K Ω P.extension A (P.representation hP)
  have hsum : (P.artinConductor hP : ℝ) = (A.rank : ℝ) * lastBreak K Ω A + (d : ℝ) := by
    rw [hartin, Rat.cast_add, Rat.cast_natCast, weilIrreducibleSwanBreak K Ω A hc hi P hP]
  rcases (lastBreak_nonneg K Ω A).eq_or_lt with hb | hb
  · rw [← hb, mul_zero, zero_add] at hsum
    have ha : P.artinConductor hP = (d : ℚ) :=
      Rat.cast_injective (α := ℝ) (by simpa only [Rat.cast_natCast] using hsum)
    rw [← hb, mul_zero, ha]
    constructor
    · rintro ⟨a, he, rfl⟩
      have he' : d = a := by exact_mod_cast he
      rw [← he', Nat.sub_eq_zero_of_le hd, Nat.cast_zero]
    · intro hs
      have hs' : s = 0 := by exact_mod_cast hs
      exact ⟨d, rfl, (Nat.sub_eq_zero_of_le hd).trans hs'.symm⟩
  · rw [show d = A.rank from fixedCodimension_eq_rank_of_pos_lastBreak K Ω A hc hi P hP hb]
      at hsum
    constructor
    · rintro ⟨a, ha, rfl⟩
      rw [ha, Rat.cast_natCast] at hsum
      have hnonneg := mul_nonneg (Nat.cast_nonneg (α := ℝ) A.rank) hb.le
      have hle : (A.rank : ℝ) ≤ a := by linarith
      rw [Nat.cast_sub (by exact_mod_cast hle : A.rank ≤ a)]
      linarith
    · intro hs
      refine ⟨s + A.rank, Rat.cast_injective (α := ℝ) ?_, Nat.add_sub_cancel_right _ _⟩
      rw [hsum, ← hs, Rat.cast_natCast, Nat.cast_add]

/-- A natural Swan exponent in the refined orbit counts is exactly the
intrinsic Swan conductor of the class, including at exponent zero. -/
theorem hasWeilSwan_iff_eq_weilSwanConductor {k s : ℕ}
    (σ : IrreducibleWeilClass.{uK, uΩ, uW} K Ω k.succPNat) :
    HasWeilSwan K Ω σ s ↔ (s : ℝ) = weilSwanConductor K Ω σ := by
  constructor
  · rintro ⟨a, ⟨A, P, hP, hA, ha⟩, hs⟩
    obtain ⟨hc, hi⟩ := representative_continuous_irreducible K Ω hA
    have hrank := representative_rank K Ω hA
    rw [weilSwanConductor_eq_rank_mul_lastBreak K Ω hA, ← hrank]
    exact (exists_artin_sub_rank_iff K Ω A hc hi P hP s).mp ⟨a, ha, by rw [hrank]; exact hs⟩
  · intro hs
    obtain ⟨A, hA⟩ := Quotient.exists_rep (weilClassForget K Ω σ)
    obtain ⟨hc, hi⟩ := representative_continuous_irreducible K Ω hA
    obtain ⟨P⟩ := continuousWeilFiniteInertiaPresentation K Ω A hc
    let hP := weilInertiaRestrictionSurjectivity K Ω P.extension
    have hrank := representative_rank K Ω hA
    rw [weilSwanConductor_eq_rank_mul_lastBreak K Ω hA, ← hrank] at hs
    obtain ⟨a, ha, he⟩ := (exists_artin_sub_rank_iff K Ω A hc hi P hP s).mpr hs
    rw [hrank] at he
    exact ⟨a, ⟨A, P, hP, hA, ha⟩, he⟩

/-- At a positive cutoff, an irreducible class with natural Swan exponent
`s` is trivial on the upper group precisely when `s < rank * cutoff`. -/
theorem isTrivialAt_iff_of_hasWeilSwan {k s : ℕ}
    {σ : IrreducibleWeilClass.{uK, uΩ, uW} K Ω k.succPNat}
    {A : FiniteRepresentation.{0, uΩ, uW} ℂ W}
    (hA : classOf A = weilClassForget K Ω σ) (hs : HasWeilSwan K Ω σ s)
    {b : ℝ} (hb : 0 < b) :
    IsTrivialAt K Ω A b ↔ (s : ℝ) < ((k + 1 : ℕ) : ℝ) * b := by
  obtain ⟨hc, hi⟩ := representative_continuous_irreducible K Ω hA
  have hfull := (weilIrreduciblePositiveThresholds K Ω A hc hi).2 b hb
  have hs' := (hasWeilSwan_iff_eq_weilSwanConductor K Ω σ).mp hs
  rw [weilSwanConductor_eq_rank_mul_lastBreak K Ω hA] at hs'
  change (s : ℝ) = ((k + 1 : ℕ) : ℝ) * lastBreak K Ω A at hs'
  have hpos : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos k
  rw [hs', mul_lt_mul_iff_of_pos_left hpos, hfull]
  constructor
  · intro h
    apply eq_top_iff.mpr
    intro v _
    exact (mem_upperFixedSpace K Ω A b v).mpr fun w hw => by rw [h w hw]; rfl
  · intro h w hw
    apply LinearMap.ext
    intro v
    exact (mem_upperFixedSpace K Ω A b v).mp (h ▸ Submodule.mem_top) w hw

end Langlands.Henniart.LocalNumerical
