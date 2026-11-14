import Langlands.AllFieldBZ.Representation.Derivative.OrderedCuspidalProductNondegeneracyProof

/-!
# All-field version of `Langlands.Representation.Whittaker.PadicMirabolicNondegeneracyOrder`

Port to an arbitrary nonarchimedean local field (`Langlands.AllFieldBZ.LocalFieldPackage`)
of the p-adic draft module `Langlands.Representation.Whittaker.PadicMirabolicNondegeneracyOrder`, which is not published.
See the paired Markdown.
-/
noncomputable section
namespace Langlands.AllFieldBZ.Whittaker.PadicMirabolicNondegeneracy
open CategoryTheory
open Langlands.GeneralLinear
open Langlands.AllFieldBZ.GeneralLinear
universe uF uV

variable {F : LocalFieldPackage.{uF}} (T : F.TopologicalData)

/-- `ν^s ρ = ρ` only for `s = 0`. -/
theorem eq_zero_of_twist_eq_self (ρ : T.CuspidalDatum.{uV, uF}) (s : ℝ)
    (h : ρ.twist s = ρ) : s = 0 := by
  let := T.topology
  rcases ρ with ⟨r, hr, c⟩
  have hc : T.supercuspidalClassRealPowerTwist r s c = c := by
    simpa only [LocalFieldPackage.TopologicalData.CuspidalDatum.twist,
      LocalFieldPackage.TopologicalData.CuspidalDatum.mk.injEq, heq_eq_eq, true_and] using h
  induction c using Quotient.inductionOn with
  | h A =>
    let At := SupercuspidalRep.twist (T.determinantPowerCharacter r s)
      (T.isOpen_ker_determinantPowerCharacter r s)
      (T.ker_determinant_le_ker_determinantPowerCharacter r s) A
    change At.isoClass = A.isoClass at hc
    obtain ⟨e⟩ := (SupercuspidalRep.isoClass_eq_iff At A).mp hc
    let e' := SmoothRep.equivOfIso ((supercuspidalProperty (F := F.Carrier)
      (n := r)).ι.mapIso e.symm)
    exact Derivative.OrderedCuspidalProductTwistOne.exponent_eq_zero T r hr A.obj
      A.property.2.1 A.property.1 s e'

/-- The indices `l` with `ρ_l = ν^m ρ_i` for some `m ≥ 1`. -/
def above {k : ℕ} (ρ : Fin k → T.CuspidalDatum.{uV, uF}) (i : Fin k) : Finset (Fin k) := by
  classical
  exact Finset.univ.filter fun l => ∃ m : ℕ, 0 < m ∧ ρ l = (ρ i).twist m

theorem mem_above {k : ℕ} (ρ : Fin k → T.CuspidalDatum.{uV, uF}) (i l : Fin k) :
    l ∈ above T ρ i ↔ ∃ m : ℕ, 0 < m ∧ ρ l = (ρ i).twist m := by
  classical
  unfold above
  simp

/-- If `ρ_j = ν ρ_i`, then strictly fewer indices lie above `j` than above `i`. -/
theorem card_above_lt {k : ℕ} (ρ : Fin k → T.CuspidalDatum.{uV, uF}) {i j : Fin k}
    (h : ρ j = (ρ i).twist 1) : (above T ρ j).card < (above T ρ i).card := by
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · refine ⟨j, (mem_above T ρ i j).2 ⟨1, Nat.one_pos, by simpa using h⟩, fun hj => ?_⟩
    obtain ⟨m, hm, hjm⟩ := (mem_above T ρ j j).1 hj
    have h0 := eq_zero_of_twist_eq_self T (ρ j) m hjm.symm
    have : m = 0 := by exact_mod_cast h0
    omega
  · intro l hl
    obtain ⟨m, hm, hl⟩ := (mem_above T ρ j l).1 hl
    refine (mem_above T ρ i l).2 ⟨m + 1, Nat.succ_pos m, ?_⟩
    rw [hl, h, LocalFieldPackage.TopologicalData.CuspidalDatum.twist_twist]
    push_cast
    rfl

/-- Every finite family of cuspidal data has a reordering with `ρ_j ≠ ν ρ_i`
for all `i < j`. -/
theorem exists_ordered_perm {k : ℕ} (ρ : Fin k → T.CuspidalDatum.{uV, uF}) :
    ∃ e : Equiv.Perm (Fin k), ∀ i j : Fin k, i < j → ρ (e j) ≠ (ρ (e i)).twist 1 := by
  refine ⟨Tuple.sort (fun i => (above T ρ i).card), fun i j hij h => ?_⟩
  have hmono := Tuple.monotone_sort (fun i => (above T ρ i).card) hij.le
  have hlt := card_above_lt T ρ h
  simp only [Function.comp_apply] at hmono
  omega

end Langlands.AllFieldBZ.Whittaker.PadicMirabolicNondegeneracy
