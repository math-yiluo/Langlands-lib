import Langlands.Correspondence.HenniartWeilArtinConductorExistenceProof
import Langlands.LocalFactor.Ramification.Herbrand.WeilBreakProof
import Langlands.LocalFactor.Ramification.InertiaConductorRefinementProof

/-! # Swan exponents and upper breaks of irreducible Weil classes -/

noncomputable section

namespace Langlands.Henniart.Numerical

open Correspondence VirtualRepresentation
open VirtualRepresentation.LocalWeil.Ramification
open Ramification Ramification.Padic Ramification.HerbrandBridge
open Ramification.Padic.InertiaConductorRefinement Weil.Local

universe uK uW
variable {p : ℕ} [Fact p.Prime] (K : PadicField.{uK} p)

/-- A single irreducible Weil break gives a rectangular upper-codimension
profile, whose integral is rank times last break. -/
theorem irreducible_presentation_swan_eq_rank_mul_lastBreak
    (A : FiniteRepresentation.{0, uK, uW} ℂ (localWeilGroup K))
    (hc : A.IsContinuous) (hi : A.IsIrreducible) (P : FiniteInertiaPresentation K A)
    (hP : Function.Surjective (weilInertiaRestriction K P.extension)) :
    (P.swanConductor hP : ℝ) = (A.rank : ℝ) * lastBreak K A := by
  let T := (absoluteFiniteExtension K P.extension).canonicalTopologicalData
  let ρ := P.representation hP
  let t := lastBreak K A
  let B := max t (Padic.herbrandPhi T K.Carrier (ramificationCutoff T K.Carrier))
  have ht : 0 ≤ t := lastBreak_nonneg K A
  have hB : t ≤ B := le_max_left _ _
  have hBefore : ∀ a ∈ Set.Ioo (0 : ℝ) t,
      upperCodimension T K.Carrier ρ a = (A.rank : ℝ) := by
    intro a ha
    have h0 := ((weilIrreduciblePositiveThresholds K A hc hi).1 a ha.1).mp ha.2.le
    rw [upperCodimension, ← presentationUpperFixedComparison K A P hP a ha.1.le, h0]
    simp [FiniteRepresentation.rank]
  have hAfter : ∀ a ∈ Set.Ioo t B, upperCodimension T K.Carrier ρ a = 0 := by
    intro a ha
    have htop := ((weilIrreduciblePositiveThresholds K A hc hi).2 a (ht.trans_lt ha.1)).mp ha.1
    rw [upperCodimension, ← presentationUpperFixedComparison K A P hP a (ht.trans ha.1.le),
      htop, finrank_top, sub_self]
  change (inertiaSwanConductor T K.Carrier ρ : ℝ) = (A.rank : ℝ) * t
  rw [InertiaConductorRefinement.inertiaSwanConductor_eq_integral T K.Carrier ρ
      (B := B) (le_max_right t _),
    ← intervalIntegral.integral_add_adjacent_intervals
      (upperCodimension_intervalIntegrable T K.Carrier ρ 0 t)
      (upperCodimension_intervalIntegrable T K.Carrier ρ t B),
    intervalIntegral.integral_congr_Ioo_of_le ht hBefore,
    intervalIntegral.integral_congr_Ioo_of_le hB hAfter]
  simp [mul_comm]

/-- Truncating the natural Artin conductor minus the rank gives the Swan
exponent even for last break zero: then the Swan term is zero and the tame
codimension is at most the rank. -/
theorem irreducible_artin_sub_rank_eq_rank_mul_lastBreak
    (A : FiniteRepresentation.{0, uK, uW} ℂ (localWeilGroup K))
    (hc : A.IsContinuous) (hi : A.IsIrreducible) (P : FiniteInertiaPresentation K A)
    (hP : Function.Surjective (weilInertiaRestriction K P.extension))
    {a : ℕ} (ha : P.artinConductor hP = a) :
    ((a - A.rank : ℕ) : ℝ) = (A.rank : ℝ) * lastBreak K A := by
  let T := (absoluteFiniteExtension K P.extension).canonicalTopologicalData
  let ρ := P.representation hP
  let t := lastBreak K A
  let d := fixedCodimension _ ρ ⊤
  have ht : 0 ≤ t := lastBreak_nonneg K A
  have hd : d ≤ A.rank := Nat.sub_le ..
  have hs := irreducible_presentation_swan_eq_rank_mul_lastBreak K A hc hi P hP
  have hadd : (a : ℝ) = (d : ℝ) + (A.rank : ℝ) * t := by
    change inertiaArtinConductor T K.Carrier ρ = (a : ℚ) at ha
    change (inertiaSwanConductor T K.Carrier ρ : ℝ) = (A.rank : ℝ) * t at hs
    rw [← Rat.cast_natCast (α := ℝ), ← ha, inertiaArtinConductor_eq_tame_add_swan,
      Rat.cast_add, Rat.cast_natCast, hs]
  by_cases ht' : 0 < t
  · have hbot := ((weilIrreduciblePositiveThresholds K A hc hi).1 t ht').mp (le_refl t)
    rw [presentationUpperFixedComparison K A P hP t ht] at hbot
    have hle := InertiaConductorRefinement.inertiaUpperFixedVectors_monotone T K.Carrier ρ ht
    rw [inertiaUpperFixedVectors_zero, hbot] at hle
    have hf : fixedVectors ρ ⊤ = ⊥ := le_bot_iff.mp hle
    have hd' : d = A.rank := by
      unfold d fixedCodimension
      rw [hf, finrank_bot, Nat.sub_zero]
      rfl
    rw [hd'] at hadd
    have hprod : 0 ≤ (A.rank : ℝ) * t := mul_nonneg (Nat.cast_nonneg _) ht
    have hle' : (A.rank : ℝ) ≤ a := by linarith
    rw [Nat.cast_sub (by exact_mod_cast hle' : A.rank ≤ a)]
    linarith
  · have h0 : t = 0 := le_antisymm (le_of_not_gt ht') ht
    rw [h0, mul_zero, add_zero] at hadd
    have heq : a = d := by exact_mod_cast hadd
    rw [heq, Nat.sub_eq_zero_of_le hd, Nat.cast_zero]
    exact (mul_eq_zero_of_right _ h0).symm

/-- The last break and rank of an actual representative of an irreducible
Weil class depend only on that class. -/
theorem weilRepresentative_break_rank {k : ℕ}
    {σ : IrreducibleWeilClass.{uK, uW} K k.succPNat}
    {A : FiniteRepresentation.{0, uK, uW} ℂ (localWeilGroup K)}
    (hA : FiniteRepresentation.classOf A = weilClassForget K σ) :
    lastBreak K A = breakLabel K ⟨k.succPNat, σ⟩ ∧ A.rank = k + 1 :=
  ⟨(classBreak_basic K ⟨k.succPNat, σ⟩ A hA).2.1,
    (classBreak_basic K ⟨k.succPNat, σ⟩ A hA).2.2.1⟩

/-- A representative of a continuous irreducible class is continuous and
irreducible. -/
theorem weilRepresentative_continuous_irreducible {k : ℕ}
    {σ : IrreducibleWeilClass.{uK, uW} K k.succPNat}
    {A : FiniteRepresentation.{0, uK, uW} ℂ (localWeilGroup K)}
    (hA : FiniteRepresentation.classOf A = weilClassForget K σ) :
    A.IsContinuous ∧ A.IsIrreducible := by
  obtain ⟨R, hR⟩ := Quotient.exists_rep σ.val
  have h' := congrArg (FiniteRepresentation.forgetPropertyClass _) hR
  obtain ⟨e⟩ := (FiniteRepresentation.classOf_eq_iff A R.val).mp (hA.trans h'.symm)
  exact ⟨(FiniteRepresentation.isContinuous_iff_of_equiv e).mpr R.property.1,
    isIrreducible_of_equiv K e.symm R.property.2⟩

/-- An integral Swan exponent agrees with the rank times the intrinsic last break. -/
theorem hasWeilSwan_eq_rank_mul_breakLabel {k s : ℕ}
    {σ : IrreducibleWeilClass.{uK, uW} K k.succPNat} (hs : HasWeilSwan K σ s) :
    (s : ℝ) = ((k + 1 : ℕ) : ℝ) * breakLabel K ⟨k.succPNat, σ⟩ := by
  obtain ⟨a, ha, rfl⟩ := hs
  obtain ⟨A, P, hP, hA, ha⟩ :=
    (Numerical.hasArtinConductor_iff_exists_padicPresentation K σ a).mp ha
  obtain ⟨hc, hi⟩ := weilRepresentative_continuous_irreducible K hA
  obtain ⟨ht, hn⟩ := weilRepresentative_break_rank K hA
  rw [← hn, ← ht]
  exact irreducible_artin_sub_rank_eq_rank_mul_lastBreak K A hc hi P hP ha

/-- The unique natural Swan exponent of a continuous irreducible class. -/
def weilSwanExponent {k : ℕ} (σ : IrreducibleWeilClass.{uK, uW} K k.succPNat) : ℕ :=
  Classical.choose (weilArtinConductorExistence p K k σ) - (k + 1)

theorem hasWeilSwan_weilSwanExponent {k : ℕ}
    (σ : IrreducibleWeilClass.{uK, uW} K k.succPNat) :
    HasWeilSwan K σ (weilSwanExponent K σ) :=
  ⟨_, Classical.choose_spec (weilArtinConductorExistence p K k σ), rfl⟩

theorem hasWeilSwan_iff_eq_rank_mul_lastBreak {k s : ℕ}
    {σ : IrreducibleWeilClass.{uK, uW} K k.succPNat}
    {A : FiniteRepresentation.{0, uK, uW} ℂ (localWeilGroup K)}
    (hA : FiniteRepresentation.classOf A = weilClassForget K σ) :
    HasWeilSwan K σ s ↔ (s : ℝ) = ((k + 1 : ℕ) : ℝ) * lastBreak K A := by
  rw [(weilRepresentative_break_rank K hA).1]
  refine ⟨hasWeilSwan_eq_rank_mul_breakLabel K, fun hs => ?_⟩
  have h := hasWeilSwan_eq_rank_mul_breakLabel K (hasWeilSwan_weilSwanExponent K σ)
  have he : weilSwanExponent K σ = s := by exact_mod_cast h.trans hs.symm
  rw [← he]
  exact hasWeilSwan_weilSwanExponent K σ

/-- A weak bound is equivalent to triviality at every upper index strictly larger
than the bound (not only at the next integer). -/
theorem lastBreak_le_iff_isTrivialAbove
    {A : FiniteRepresentation.{0, uK, uW} ℂ (localWeilGroup K)} (hc : A.IsContinuous)
    {b : ℝ} (hb : 0 ≤ b) :
    lastBreak K A ≤ b ↔ ∀ a : ℝ, b < a → IsTrivialAt K A a := by
  constructor
  · intro h a ha
    exact (lastBreak_lt_iff_isTrivialAt K A hc (hb.trans_lt ha)).mp (h.trans_lt ha)
  · intro h
    apply le_of_forall_pos_lt_add
    intro ε hε
    have h' : b < b + ε := lt_add_of_pos_right _ hε
    exact (lastBreak_lt_iff_isTrivialAt K A hc (hb.trans_lt h')).mpr (h _ h')

end Langlands.Henniart.Numerical
