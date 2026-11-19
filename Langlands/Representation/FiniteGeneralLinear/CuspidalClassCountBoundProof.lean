import Langlands.Representation.FiniteGeneralLinear.CuspidalClassCountBoundStatement
import Langlands.Representation.FiniteGeneralLinear.GenericClassCount
import Langlands.FieldTheory.PolynomialFactorCount
import Mathlib.SetTheory.Cardinal.NatCard

/-! The finite cuspidal class bound from the count of Gelfand–Graev constituents. -/

noncomputable section

namespace Langlands.FiniteGeneralLinear

open Langlands.FieldTheory

universe u w

variable {k : Type u} [Field k]

private def cuspidalRankFiberEquiv {n : ℕ} (hn : 0 < n) :
    {a : PositiveCuspidalLabel k // cuspidalLabelRank a = n} ≃ CuspidalModelClass n k where
  toFun := fun ⟨⟨⟨r, _⟩, a⟩, h⟩ => h ▸ a
  invFun := fun a => ⟨⟨⟨n, hn⟩, a⟩, rfl⟩
  left_inv := by
    rintro ⟨⟨⟨r, hr⟩, a⟩, h⟩
    change r = n at h
    subst r
    rfl
  right_inv := fun _ => rfl

@[instance_reducible]
private def unique_cuspidalMultiset_zero : Unique (CuspidalMultiset 0 k) where
  default := ⟨0, by simp⟩
  uniq m := by
    apply Subtype.ext
    change m.val = 0
    by_contra hm
    obtain ⟨a, ha⟩ := Multiset.exists_mem_of_ne_zero hm
    have hz := Multiset.sum_eq_zero_iff.mp m.property (cuspidalLabelRank a)
      (Multiset.mem_map_of_mem _ ha)
    exact (Nat.ne_of_gt a.1.property) hz

private theorem finite_cuspidalMultiset [Finite k] (n : ℕ) : Finite (CuspidalMultiset n k) := by
  cases n with
  | zero =>
    let := unique_cuspidalMultiset_zero (k := k)
    infer_instance
  | succ n =>
    obtain ⟨ψ, hψ⟩ := AddChar.exists_apply_ne_zero.mpr (one_ne_zero : (1 : k) ≠ 0)
    have hψ' : ψ ≠ 0 := fun h => hψ (by simp [h])
    exact Finite.of_equiv _ (genericClassesEquivCuspidalMultisets ψ hψ' n)

private theorem card_cuspidalModelClass [Finite k] {n : ℕ} (hn : 0 < n) :
    Nat.card (CuspidalModelClass n k) = Nat.card (irreduciblePolynomialLabels n k) := by
  have h (m : ℕ) :
      Nat.card (CuspidalMultiset m k) = Nat.card (WeightedMultiset (PolynomialLabel.weight (k := k)) m) := by
    cases m with
    | zero =>
      let := unique_cuspidalMultiset_zero (k := k)
      exact Nat.card_unique.trans (card_polynomialFactorMultiset_zero (k := k)).symm
    | succ m =>
      exact (card_cuspidalMultiset_succ (k := k) m).trans (card_polynomialFactorMultiset_succ m).symm
  have hFiber := WeightedMultiset.card_fiber_eq_of_card_eq (fun a => a.1.property)
    PolynomialLabel.weight_pos (finite_cuspidalMultiset (k := k)) (fun _ => inferInstance) h n
  calc
    Nat.card (CuspidalModelClass n k) =
        Nat.card {a : PositiveCuspidalLabel k // cuspidalLabelRank a = n} :=
      Nat.card_congr (cuspidalRankFiberEquiv hn).symm
    _ = Nat.card {p : PolynomialLabel k // p.weight = n} := hFiber
    _ = Nat.card (irreduciblePolynomialLabels n k) := Nat.card_congr (polynomialLabelFiberEquiv n)

/-- The number of finite-field cuspidal classes is bounded by the number of polynomial labels. -/
theorem cuspidalClassCountBound : CuspidalClassCountBoundStatement.{u, w} := by
  intro k _ _ n hn
  have : Finite (CuspidalModelClass n k) := by
    unfold CuspidalModelClass
    infer_instance
  have : Finite (irreduciblePolynomialLabels n k) :=
    (irreduciblePolynomialLabels_finite n k).to_subtype
  rw [ENat.card_congr (CuspidalModelClass.equivCuspidalClass (n := n) (k := k))]
  change ENat.card (CuspidalModelClass n k) ≤ ENat.card (irreduciblePolynomialLabels n k)
  rw [ENat.card_eq_coe_natCard, ENat.card_eq_coe_natCard, card_cuspidalModelClass hn]

end Langlands.FiniteGeneralLinear
