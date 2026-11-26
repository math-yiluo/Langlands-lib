import Langlands.Representation.FiniteGeneralLinear.CuspidalClassCountBoundProof
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.FieldTheory.PrimitiveElement

/-!
# Existence of irreducible cuspidal representations of `GL_n` over a finite field

Over a finite field `k` and in every positive rank `n`, the finite-dimensional cuspidal
model classes are equinumerous with Bushnell–Kutzko's label set `𝔍(n, k)`, and this set is
nonempty: the minimal polynomial of a primitive element of a degree-`n` extension of `k`
lies in it. Hence `GL_n(k)` has an irreducible cuspidal complex representation.
-/

noncomputable section

namespace Langlands.FiniteGeneralLinear

open Langlands.FieldTheory Polynomial

universe u

variable {k : Type u} [Field k]

/-- Over a finite field, `𝔍(n, k)` is nonempty in every positive degree. -/
theorem irreduciblePolynomialLabels_nonempty [Finite k] {n : ℕ} (hn : 0 < n) :
    (irreduciblePolynomialLabels n k).Nonempty := by
  obtain ⟨p, hp⟩ := CharP.exists k
  have : Fact p.Prime := ⟨CharP.char_is_prime k p⟩
  have : NeZero n := ⟨hn.ne'⟩
  let L := FiniteField.Extension k p n
  obtain ⟨α, hα⟩ := Field.exists_primitive_element k L
  have hint : IsIntegral k α := .of_finite k α
  have hdeg : (minpoly k α).natDegree = n := by
    rw [← IntermediateField.adjoin.finrank hint, hα, IntermediateField.finrank_top',
      FiniteField.finrank_extension]
  by_cases h1 : n = 1
  · subst h1
    refine ⟨X - C 1, mem_irreduciblePolynomialLabels_iff.mpr
      ⟨monic_X_sub_C 1, irreducible_X_sub_C 1, natDegree_X_sub_C 1, ?_⟩⟩
    intro h
    have h0 := congrArg (fun P : k[X] => P.coeff 0) h
    simp at h0
  · exact ⟨minpoly k α, (mem_irreduciblePolynomialLabels_iff_of_ne_one h1).mpr
      ⟨minpoly.monic hint, minpoly.irreducible hint, hdeg⟩⟩

@[instance_reducible]
private def uniqueCuspidalMultisetZero : Unique (CuspidalMultiset 0 k) where
  default := ⟨0, by simp⟩
  uniq m := by
    apply Subtype.ext
    change m.val = 0
    by_contra hm
    obtain ⟨a, ha⟩ := Multiset.exists_mem_of_ne_zero hm
    have hz := Multiset.sum_eq_zero_iff.mp m.property (cuspidalLabelRank a)
      (Multiset.mem_map_of_mem _ ha)
    exact (Nat.ne_of_gt a.1.property) hz

private theorem finite_cuspidalMultiset' [Finite k] (n : ℕ) :
    Finite (CuspidalMultiset n k) := by
  cases n with
  | zero =>
    let := uniqueCuspidalMultisetZero (k := k)
    infer_instance
  | succ n =>
    obtain ⟨ψ, hψ⟩ := AddChar.exists_apply_ne_zero.mpr (one_ne_zero : (1 : k) ≠ 0)
    have hψ' : ψ ≠ 0 := fun h => hψ (by simp [h])
    exact Finite.of_equiv _ (genericClassesEquivCuspidalMultisets ψ hψ' n)

private def cuspidalRankFiberEquiv' {n : ℕ} (hn : 0 < n) :
    {a : PositiveCuspidalLabel k // cuspidalLabelRank a = n} ≃ CuspidalModelClass n k where
  toFun := fun ⟨⟨⟨r, _⟩, a⟩, h⟩ => h ▸ a
  invFun := fun a => ⟨⟨⟨n, hn⟩, a⟩, rfl⟩
  left_inv := by
    rintro ⟨⟨⟨r, hr⟩, a⟩, h⟩
    change r = n at h
    subst r
    rfl
  right_inv := fun _ => rfl

/-- In positive rank, the finite-dimensional cuspidal model classes of `GL_n(k)` are as
many as the labels in `𝔍(n, k)`. -/
theorem natCard_cuspidalModelClass [Finite k] {n : ℕ} (hn : 0 < n) :
    Nat.card (CuspidalModelClass n k) = Nat.card (irreduciblePolynomialLabels n k) := by
  have h (m : ℕ) : Nat.card (CuspidalMultiset m k) =
      Nat.card (WeightedMultiset (PolynomialLabel.weight (k := k)) m) := by
    cases m with
    | zero =>
      let := uniqueCuspidalMultisetZero (k := k)
      exact Nat.card_unique.trans (card_polynomialFactorMultiset_zero (k := k)).symm
    | succ m =>
      exact (card_cuspidalMultiset_succ (k := k) m).trans
        (card_polynomialFactorMultiset_succ m).symm
  have hFiber := WeightedMultiset.card_fiber_eq_of_card_eq (fun a => a.1.property)
    PolynomialLabel.weight_pos (finite_cuspidalMultiset' (k := k)) (fun _ => inferInstance) h n
  calc
    Nat.card (CuspidalModelClass n k) =
        Nat.card {a : PositiveCuspidalLabel k // cuspidalLabelRank a = n} :=
      Nat.card_congr (cuspidalRankFiberEquiv' hn).symm
    _ = Nat.card {p : PolynomialLabel k // p.weight = n} := hFiber
    _ = Nat.card (irreduciblePolynomialLabels n k) :=
      Nat.card_congr (polynomialLabelFiberEquiv n)

/-- Over a finite field, `GL_n(k)` has a finite-dimensional cuspidal model class in every
positive rank. -/
theorem cuspidalModelClass_nonempty [Finite k] {n : ℕ} (hn : 0 < n) :
    Nonempty (CuspidalModelClass n k) := by
  have hfin : Finite (irreduciblePolynomialLabels n k) :=
    (irreduciblePolynomialLabels_finite n k).to_subtype
  have hne : Nonempty (irreduciblePolynomialLabels n k) :=
    (irreduciblePolynomialLabels_nonempty hn).to_subtype
  have hpos : 0 < Nat.card (irreduciblePolynomialLabels n k) := Nat.card_pos
  rw [← natCard_cuspidalModelClass hn] at hpos
  exact (Nat.card_pos_iff.mp hpos).1

/-- **Existence of cuspidal representations.** Over a finite field `k` and in every positive
rank `n`, there is a finite-dimensional irreducible cuspidal complex representation of
`GL_n(k)`. -/
theorem exists_irreducible_cuspidal_fdRep [Finite k] {n : ℕ} (hn : 0 < n) :
    ∃ V : FDRep ℂ (GeneralLinear n k), Representation.IsIrreducible V.ρ ∧ IsCuspidal V.ρ := by
  obtain ⟨a⟩ := cuspidalModelClass_nonempty (k := k) hn
  exact ⟨FiniteRep.VirtualCharacter.rep a.1, FiniteRep.VirtualCharacter.isIrreducible_rep a.1,
    a.2⟩

end Langlands.FiniteGeneralLinear
