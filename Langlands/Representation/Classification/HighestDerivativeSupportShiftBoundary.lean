import Langlands.Representation.Classification.SupercuspidalSupport
import Langlands.Representation.Derivative.MirabolicDerivativeVanishing

/-!
# Boundary cases for highest-derivative support shift

Rank-zero supports are empty. At positive rank, vanishing of every positive
general-linear derivative forces the representation to vanish.
-/

noncomputable section

open CategoryTheory

namespace Langlands

universe uF uV

namespace Derivative

open GeneralLinear HarmonicAnalysis

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
variable (T : F.TopologicalData)
variable (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology)

/-- Every positive bounded general-linear derivative has a subsingleton carrier. -/
def PositiveGeneralLinearDerivativesVanish {N : ℕ} :
    letI := T.topology
    SmoothRep.{0, uF, uV} ℂ (GeneralLinear N F.Carrier) → Prop :=
  letI := T.topology
  fun A => ∀ (j : ℕ) (hj : j ≤ N), 0 < j →
    Subsingleton ((generalLinearDerivative T ψ N j hj).obj A)

/-- The positive derivatives jointly detect a representation of positive rank. -/
theorem subsingleton_of_forall_generalLinearDerivative {N : ℕ} (hN : 0 < N) :
    letI := T.topology
    ∀ A : SmoothRep.{0, uF, uV} ℂ (GeneralLinear N F.Carrier),
      PositiveGeneralLinearDerivativesVanish T ψ A →
      Subsingleton A := by
  let := T.topology
  obtain ⟨M, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hN)
  intro A hA
  apply Mirabolic.subsingleton_of_forall_mirabolicDerivative T ψ M
    ((generalLinearRestriction T M).obj A)
  intro n j h
  subst M
  have hvan := hA (j + 1) (by omega) (by omega)
  have key : ∀ (m : ℕ) (hm : n + j + 1 = m + j + 1),
      Subsingleton
        ((generalLinearRankCast T hm ⋙ generalLinearDerivativePositive T ψ m j).obj A) →
      Subsingleton
        ((mirabolicDerivative T ψ n j).obj ((generalLinearRestriction T (n + j)).obj A)) := by
    intro m hm hv
    have hmn : m = n := by omega
    subst m
    exact hv
  exact key _ (rank_eq_of_succ_le (by omega)) hvan

/-- Any highest nonzero derivative order is positive when the source rank is positive. -/
theorem highestGeneralLinearDerivativeOrder_pos {N k : ℕ} (hN : 0 < N)
    (hk : k ≤ N) :
    letI := T.topology
    ∀ A : SmoothRep.{0, uF, uV} ℂ (GeneralLinear N F.Carrier),
      Nontrivial ((generalLinearDerivative T ψ N k hk).obj A) →
      (∀ (j : ℕ) (hj : j ≤ N), k < j →
        Subsingleton ((generalLinearDerivative T ψ N j hj).obj A)) →
      0 < k := by
  let := T.topology
  intro A hnonzero hvan
  by_contra hpos
  have hk0 : k = 0 := by omega
  subst k
  let : Nontrivial A := hnonzero
  let : Subsingleton A :=
    subsingleton_of_forall_generalLinearDerivative T ψ hN A hvan
  exact false_of_nontrivial_of_subsingleton A

end Derivative

namespace PadicField.TopologicalData

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
variable {T : F.TopologicalData}

/-- A support at rank zero is empty, since every cuspidal datum has positive rank. -/
theorem IsSupercuspidalSupport.eq_zero_of_rank_zero {n : ℕ}
    {π : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)}
    {s : Multiset (CuspidalDatum.{uV, uF} T)}
    (hs : T.IsSupercuspidalSupport π s) (hn : n = 0) : s = 0 := by
  have hsum : (s.map CuspidalDatum.rank).sum = 0 := hs.sum_rank.trans hn
  induction s using Multiset.induction_on with
  | empty => rfl
  | @cons ρ s _ =>
    simp only [Multiset.map_cons, Multiset.sum_cons] at hsum
    have hρ := ρ.rank_pos
    omega

/-- The support-shift inequality holds whenever the derivative has rank zero. -/
theorem IsSupercuspidalSupport.twist_le_of_rank_zero {n : ℕ}
    {π : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)}
    {s' : Multiset (CuspidalDatum.{uV, uF} T)}
    (hs' : T.IsSupercuspidalSupport π s') (hn : n = 0)
    (s : Multiset (CuspidalDatum.{uV, uF} T)) :
    s'.map (CuspidalDatum.twist 1) ≤ s := by
  rw [hs'.eq_zero_of_rank_zero hn, Multiset.map_zero]
  exact zero_le

end PadicField.TopologicalData

end Langlands
