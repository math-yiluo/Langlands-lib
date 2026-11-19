import Langlands.Combinatorics.WeightedMultiset
import Langlands.FieldTheory.IrreduciblePolynomialLabels
import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.BigOperators

/-! # Counting monic polynomial factorizations of fixed degree -/

noncomputable section

namespace Langlands.FieldTheory

open Polynomial UniqueFactorizationMonoid

variable {k : Type*} [Field k]

/-- The monic irreducible polynomial labels in all degrees, excluding `X`. -/
abbrev PolynomialLabel (k : Type*) [Field k] := {p : k[X] // p.Monic ∧ Irreducible p ∧ p ≠ X}

/-- Degree as the weight of a polynomial label. -/
def PolynomialLabel.weight (p : PolynomialLabel k) : ℕ := p.val.natDegree

theorem PolynomialLabel.weight_pos (p : PolynomialLabel k) : 0 < p.weight := p.2.2.1.natDegree_pos

theorem PolynomialLabel.coeff_zero_ne_zero (p : PolynomialLabel k) : p.val.coeff 0 ≠ 0 := by
  intro hz
  have h := irreducible_X.associated_of_dvd p.2.2.1 (X_dvd_iff.mpr hz)
  exact p.2.2.2 (eq_of_monic_of_associated monic_X p.2.1 h).symm

/-- The fiber of the weight function is the published polynomial label subtype. -/
def polynomialLabelFiberEquiv (n : ℕ) :
    {p : PolynomialLabel k // p.weight = n} ≃ irreduciblePolynomialLabels n k where
  toFun p := ⟨p.val.val, mem_irreduciblePolynomialLabels_iff.mpr ⟨p.val.2.1, p.val.2.2.1, p.2, p.val.2.2.2⟩⟩
  invFun p :=
    let h := mem_irreduciblePolynomialLabels_iff.mp p.2
    ⟨⟨p.val, h.1, h.2.1, h.2.2.2⟩, h.2.2.1⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Monic degree-`n` polynomials with nonzero constant coefficient. -/
abbrev MonicNonzeroConstant (n : ℕ) (k : Type*) [Field k] :=
  {p : k[X] // IsMonicOfDegree p n ∧ p.coeff 0 ≠ 0}

instance [Finite k] (n : ℕ) : Finite (MonicNonzeroConstant n k) :=
  ((finite_setOf_natDegree_le k n).subset fun _ h => h.1.natDegree_eq.le).to_subtype

open Classical in
private theorem factors_prod_eq_monic (p : k[X]) (hp : p.Monic) :
    (normalizedFactors p).prod = p := by
  simpa only [hp.leadingCoeff, map_one, one_mul] using leadingCoeff_mul_prod_normalizedFactors p

open Classical in
private theorem normalizedFactors_labels (p : k[X]) (hp : p.Monic) (h0 : p.coeff 0 ≠ 0)
    (f : k[X]) (hf : f ∈ normalizedFactors p) : f.Monic ∧ Irreducible f ∧ f ≠ X := by
  obtain ⟨hi, hm, hd⟩ := (Polynomial.mem_normalizedFactors_iff hp.ne_zero).mp hf
  exact ⟨hm, hi, fun hX => h0 (X_dvd_iff.mp (hX ▸ hd))⟩

private def multiplyLabels {n : ℕ} (s : WeightedMultiset (PolynomialLabel.weight (k := k)) n) :
    MonicNonzeroConstant n k := by
  let t := s.val.map (Subtype.val : PolynomialLabel k → k[X])
  have hmonic (f : k[X]) (hf : f ∈ t) : f.Monic := by
    obtain ⟨p, _, rfl⟩ := Multiset.mem_map.mp hf
    exact p.2.1
  refine ⟨t.prod, ⟨?_, monic_multiset_prod_of_monic _ _ fun p _ => p.2.1⟩, ?_⟩
  · rw [natDegree_multiset_prod_of_monic _ hmonic]
    simp only [t, Multiset.map_map, Function.comp_def]
    exact s.2
  · rw [coeff_zero_multiset_prod, Multiset.map_map]
    intro hz
    obtain ⟨p, _, hp⟩ := Multiset.mem_map.mp (Multiset.prod_eq_zero_iff.mp hz)
    exact PolynomialLabel.coeff_zero_ne_zero p hp

private theorem multiplyLabels_injective {n : ℕ} :
    Function.Injective (multiplyLabels (k := k) (n := n)) := by
  classical
  intro s t h
  let a := s.val.map (Subtype.val : PolynomialLabel k → k[X])
  let b := t.val.map (Subtype.val : PolynomialLabel k → k[X])
  have hp : a.prod = b.prod := congrArg Subtype.val h
  have hnorm (s : Multiset (PolynomialLabel k)) :
      normalizedFactors (s.map Subtype.val).prod = s.map Subtype.val := by
    rw [normalizedFactors_prod_eq]
    · rw [Multiset.map_map]
      apply Multiset.map_congr rfl
      intro p _
      exact (normalize_eq_self_iff_monic p.2.2.1.ne_zero).mpr p.2.1
    · intro f hf
      obtain ⟨p, _, rfl⟩ := Multiset.mem_map.mp hf
      exact p.2.2.1
  have he := congrArg normalizedFactors hp
  change normalizedFactors (s.val.map Subtype.val).prod =
    normalizedFactors (t.val.map Subtype.val).prod at he
  rw [hnorm, hnorm] at he
  exact Subtype.ext (Multiset.map_injective Subtype.val_injective he)

private theorem multiplyLabels_surjective {n : ℕ} :
    Function.Surjective (multiplyLabels (k := k) (n := n)) := by
  classical
  intro p
  let t := normalizedFactors p.val
  let f (a : {a // a ∈ t}) : PolynomialLabel k :=
    ⟨a.val, normalizedFactors_labels p.val p.2.1.monic p.2.2 a.val a.2⟩
  let s := t.attach.map f
  have hs : s.map Subtype.val = t := by
    change (t.attach.map f).map Subtype.val = t
    rw [Multiset.map_map]
    exact t.attach_map_val
  have hm (q : k[X]) (hq : q ∈ t) : q.Monic :=
    (normalizedFactors_labels p.val p.2.1.monic p.2.2 q hq).1
  have hprod : t.prod = p.val := factors_prod_eq_monic p.val p.2.1.monic
  have hwn : (s.map PolynomialLabel.weight).sum = n := by
    rw [← show (s.map Subtype.val).map natDegree = s.map PolynomialLabel.weight from Multiset.map_map _ _ _,
      hs, ← natDegree_multiset_prod_of_monic t hm, hprod]
    exact p.2.1.natDegree_eq
  refine ⟨⟨s, hwn⟩, Subtype.ext ?_⟩
  change (s.map Subtype.val).prod = p.val
  rw [hs, hprod]

/-- Monic factorization gives an equivalence between the prescribed total weight and degree. -/
def polynomialFactorMultisetEquiv (n : ℕ) :
    WeightedMultiset (PolynomialLabel.weight (k := k)) n ≃ MonicNonzeroConstant n k :=
  Equiv.ofBijective multiplyLabels ⟨multiplyLabels_injective, multiplyLabels_surjective⟩

instance [Finite k] (n : ℕ) : Finite (WeightedMultiset (PolynomialLabel.weight (k := k)) n) :=
  Finite.of_injective _ (polynomialFactorMultisetEquiv (k := k) n).injective

/-- The degree-zero factorization is empty and has product one. -/
theorem card_polynomialFactorMultiset_zero :
    Nat.card (WeightedMultiset (PolynomialLabel.weight (k := k)) 0) = 1 := by
  rw [Nat.card_congr (polynomialFactorMultisetEquiv (k := k) 0)]
  let : Unique (MonicNonzeroConstant 0 k) :=
    { default := ⟨1, ⟨natDegree_one, monic_one⟩, by simp⟩
      uniq := fun p => Subtype.ext (isMonicOfDegree_zero_iff.mp p.2.1) }
  exact Nat.card_unique

private def polynomialFromCoeffs {n : ℕ} (a : kˣ) (c : Fin n → k) : k[X] :=
  X ^ (n + 1) + ∑ i : Fin (n + 1), monomial i.val (Fin.cases (a : k) c i)

private theorem coeff_polynomialFromCoeffs_lt {n : ℕ} (a : kˣ) (c : Fin n → k) (i : Fin (n + 1)) :
    (polynomialFromCoeffs a c).coeff i.val = Fin.cases (a : k) c i := by
  classical
  rw [polynomialFromCoeffs, coeff_add, coeff_X_pow, ite_eq_right i.isLt.ne, zero_add, finsetSum_coeff,
    Finset.sum_eq_single i]
  · exact coeff_monomial_same _ _
  · intro j _ hji
    exact coeff_monomial_of_ne _ (fun h => hji (Fin.ext h.symm))
  · simp

private theorem polynomialFromCoeffs_monic {n : ℕ} (a : kˣ) (c : Fin n → k) :
    IsMonicOfDegree (polynomialFromCoeffs a c) (n + 1) := by
  classical
  apply (isMonicOfDegree_iff _ _).mpr
  have hz (m : ℕ) (hm : n + 1 ≤ m) :
      ((∑ i : Fin (n + 1), monomial i.val (Fin.cases (a : k) c i)) : k[X]).coeff m = 0 := by
    rw [finsetSum_coeff]
    apply Finset.sum_eq_zero
    intro i _
    exact coeff_monomial_of_ne _ (by omega)
  refine ⟨natDegree_le_iff_coeff_eq_zero.mpr fun m hm => ?_, ?_⟩
  · simp only [polynomialFromCoeffs, coeff_add, coeff_X_pow, ite_eq_right (ne_of_gt hm),
      hz m (Nat.le_of_lt hm), zero_add]
  · simp only [polynomialFromCoeffs, coeff_add, coeff_X_pow, ite_true, hz _ le_rfl, add_zero]

/-- A monic polynomial in rank `n+1` is specified by its nonzero constant coefficient and its
remaining `n` free coefficients. -/
def monicNonzeroConstantCoeffs (n : ℕ) : MonicNonzeroConstant (n + 1) k ≃ kˣ × (Fin n → k) where
  toFun p := (Units.mk0 (p.val.coeff 0) p.2.2, fun i => p.val.coeff i.succ.val)
  invFun x := ⟨polynomialFromCoeffs x.1 x.2, polynomialFromCoeffs_monic _ _, by
    simpa only [Fin.val_zero, Fin.cases_zero] using
      (coeff_polynomialFromCoeffs_lt x.1 x.2 0).trans_ne x.1.ne_zero⟩
  left_inv p := by
    apply Subtype.ext
    apply Polynomial.ext
    intro j
    by_cases hj : j < n + 1
    · let i : Fin (n + 1) := ⟨j, hj⟩
      change (polynomialFromCoeffs (Units.mk0 (p.val.coeff 0) p.2.2)
        (fun l : Fin n => p.val.coeff l.succ.val)).coeff i.val = p.val.coeff i.val
      rw [coeff_polynomialFromCoeffs_lt]
      refine Fin.cases ?_ (fun l => ?_) i
      · rfl
      · rfl
    · exact (polynomialFromCoeffs_monic _ _).coeff_eq p.2.1 (Nat.le_of_not_gt hj)
  right_inv x := by
    apply Prod.ext
    · apply Units.ext
      exact coeff_polynomialFromCoeffs_lt x.1 x.2 0
    · funext i
      exact coeff_polynomialFromCoeffs_lt x.1 x.2 i.succ

/-- The positive-degree polynomial count matches the Gelfand–Graev endomorphism dimension. -/
theorem card_polynomialFactorMultiset_succ (n : ℕ) :
    Nat.card (WeightedMultiset (PolynomialLabel.weight (k := k)) (n + 1)) = Nat.card kˣ * Nat.card k ^ n := by
  rw [Nat.card_congr (polynomialFactorMultisetEquiv (k := k) (n + 1)),
    Nat.card_congr (monicNonzeroConstantCoeffs (k := k) n), Nat.card_prod, Nat.card_fun, Nat.card_fin]

end Langlands.FieldTheory
