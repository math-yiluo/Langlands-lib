/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.FieldTheory.TriangularFieldModelEquations
public import Mathlib.Algebra.Polynomial.Monic
public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-! # Bounded monomial spanning for triangular quotients

Source: Stacks Project, Algebra, proofs of Tags 07BV and 08JZ.
-/

@[expose] public section

universe u
namespace FieldTheory

private theorem triangularFieldModel_bounded_mul
    (k : Type u) [Field k] (d m : ℕ) (h : MvPolynomial (Fin d) k)
    (p : (i : Fin m) → Polynomial (MvPolynomial (Fin (d + 1 + i.val)) k))
    (e : Fin m → ℕ) (hp : ∀ i, (p i).Monic)
    (he : ∀ i, (p i).natDegree = e i)
    (psi : Localization.Away h →ₐ[k]
      (MvPolynomial (Fin (d + 1 + m)) k ⧸
        Ideal.ofList (triangularFieldModelEquations k d m h p)))
    (hpsi : ∀ r : MvPolynomial (Fin d) k,
      psi (algebraMap _ (Localization.Away h) r) = Ideal.Quotient.mk _
        (MvPolynomial.rename (fun j : Fin d ↦
          (⟨j.val, by omega⟩ : Fin (d + 1 + m))) r))
    (a : (i : Fin m) → Fin (e i)) (j : Fin m) :
    letI := psi.toRingHom.toAlgebra
    (∏ i : Fin m,
      (Ideal.Quotient.mk
        (Ideal.ofList (triangularFieldModelEquations k d m h p)) (MvPolynomial.X
        (⟨d + 1 + i.val, by omega⟩ : Fin (d + 1 + m)))) ^ (a i).val) *
      Ideal.Quotient.mk
        (Ideal.ofList (triangularFieldModelEquations k d m h p)) (MvPolynomial.X
        (⟨d + 1 + j.val, by omega⟩ : Fin (d + 1 + m))) ∈
      Submodule.span (Localization.Away h) (Set.range fun b : (i : Fin m) → Fin (e i) ↦
        ∏ i : Fin m,
          (Ideal.Quotient.mk
        (Ideal.ofList (triangularFieldModelEquations k d m h p)) (MvPolynomial.X
            (⟨d + 1 + i.val, by omega⟩ : Fin (d + 1 + m)))) ^ (b i).val) := by
  classical
  let I := Ideal.ofList (triangularFieldModelEquations k d m h p)
  let Q := MvPolynomial (Fin (d + 1 + m)) k ⧸ I
  let D := Localization.Away h
  let pi : MvPolynomial (Fin (d + 1 + m)) k →+* Q := Ideal.Quotient.mk I
  let : Algebra D Q := psi.toRingHom.toAlgebra
  let y (i : Fin m) : Q := pi (MvPolynomial.X ⟨d + 1 + i.val, by omega⟩)
  let v (a : (i : Fin m) → Fin (e i)) : Q := ∏ i, y i ^ (a i).val
  let S : Submodule D Q := Submodule.span D (Set.range v)
  have smul_eq (r : D) (z : Q) : r • z = psi r * z := rfl
  have hloc : pi (MvPolynomial.rename (fun j : Fin d ↦
      (⟨j.val, by omega⟩ : Fin (d + 1 + m))) h) *
      pi (MvPolynomial.X ⟨d, by omega⟩) = 1 := by
    apply sub_eq_zero.mp
    rw [← map_mul, ← map_one pi, ← map_sub]
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    apply Ideal.subset_span
    exact List.mem_cons_self
  have ht : pi (MvPolynomial.X ⟨d, by omega⟩) =
      psi (IsLocalization.Away.invSelf (S := D) h) := by
    have hinv := congrArg psi (IsLocalization.Away.mul_invSelf (S := D) h)
    rw [map_mul, map_one, hpsi] at hinv
    calc
      pi (MvPolynomial.X ⟨d, by omega⟩) =
          pi (MvPolynomial.X ⟨d, by omega⟩) *
            (pi (MvPolynomial.rename (fun j : Fin d ↦
              (⟨j.val, by omega⟩ : Fin (d + 1 + m))) h) *
              psi (IsLocalization.Away.invSelf (S := D) h)) := by rw [hinv, mul_one]
      _ = psi (IsLocalization.Away.invSelf (S := D) h) := by
        rw [← mul_assoc, mul_comm (pi (MvPolynomial.X _)), hloc, one_mul]
  let coeffMap (i : Fin m) : MvPolynomial (Fin (d + 1 + i.val)) k →+* Q :=
    pi.comp (MvPolynomial.rename (fun l : Fin (d + 1 + i.val) ↦
      (⟨l.val, by omega⟩ : Fin (d + 1 + m)))).toRingHom
  have coeff_mul (i : Fin m)
      (hi : ∀ j : Fin m, j.val < i.val → ∀ z ∈ S, z * y j ∈ S)
      (r : MvPolynomial (Fin (d + 1 + i.val)) k) (z : Q) (hz : z ∈ S) :
      z * coeffMap i r ∈ S := by
    induction r using MvPolynomial.induction_on generalizing z with
    | C c =>
      have hc := hpsi (MvPolynomial.C c)
      simp only [MvPolynomial.rename_C] at hc
      simp only [coeffMap, RingHom.comp_apply, MvPolynomial.rename_C,
        AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
      rw [← hc, mul_comm]
      exact S.smul_mem _ hz
    | add r s hr hs =>
      simpa only [map_add, mul_add] using S.add_mem (hr z hz) (hs z hz)
    | mul_X r l hr =>
      rw [map_mul, ← mul_assoc]
      have hzr := hr z hz
      have hmap : coeffMap i (MvPolynomial.X l) =
          pi (MvPolynomial.X (⟨l.val, by omega⟩ : Fin (d + 1 + m))) := by
        simp [coeffMap]
      rw [hmap]
      by_cases hl : l.val < d
      · let l' : Fin d := ⟨l.val, hl⟩
        have hx := hpsi (MvPolynomial.X l')
        simp only [MvPolynomial.rename_X] at hx
        rw [← hx, mul_comm]
        exact S.smul_mem _ hzr
      · by_cases hle : l.val = d
        · have hindex : (⟨l.val, by omega⟩ : Fin (d + 1 + m)) = ⟨d, by omega⟩ :=
            Fin.ext hle
          rw [hindex, ht, mul_comm]
          exact S.smul_mem _ hzr
        · let l' : Fin m := ⟨l.val - (d + 1), by omega⟩
          have hindex : (⟨l.val, by omega⟩ : Fin (d + 1 + m)) =
              ⟨d + 1 + l'.val, by omega⟩ := by
            apply Fin.ext
            dsimp [l']
            omega
          rw [hindex]
          exact hi l' (by dsimp [l']; omega) _ hzr
  have root (i : Fin m) : Polynomial.eval₂ (coeffMap i) (y i) (p i) = 0 := by
    have hmem : Polynomial.eval₂
        (MvPolynomial.rename (fun l : Fin (d + 1 + i.val) ↦
          (⟨l.val, by omega⟩ : Fin (d + 1 + m)))).toRingHom
        (MvPolynomial.X ⟨d + 1 + i.val, by omega⟩) (p i) ∈ I := by
      apply Ideal.subset_span
      simp only [triangularFieldModelEquations, List.mem_cons, List.mem_ofFn]
      exact Or.inr ⟨i, rfl⟩
    have hh := Ideal.Quotient.eq_zero_iff_mem.mpr hmem
    simpa only [Polynomial.hom_eval₂] using hh
  have reduce (i : Fin m) : y i ^ e i =
      -(∑ n ∈ Finset.range (e i), coeffMap i ((p i).coeff n) * y i ^ n) := by
    have hh := root i
    rw [Polynomial.eval₂_eq_sum_range, he i, Finset.sum_range_succ] at hh
    have hc : (p i).coeff (e i) = 1 := by rw [← he i]; exact (hp i).coeff_natDegree
    rw [hc, map_one, one_mul] at hh
    exact eq_neg_of_add_eq_zero_right hh
  have stable : ∀ (n : ℕ) (i : Fin m), i.val = n → ∀ z ∈ S, z * y i ∈ S := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro i hin z hz
      have lower (j : Fin m) (hji : j.val < i.val) (z : Q) (hz : z ∈ S) :
          z * y j ∈ S := ih j.val (by omega) j rfl z hz
      induction hz using Submodule.span_induction with
      | mem z hz =>
        obtain ⟨a, rfl⟩ := hz
        let w : Q := ∏ l ∈ Finset.univ.erase i, y l ^ (a l).val
        have update (b : Fin (e i)) : v (Function.update a i b) = w * y i ^ b.val := by
          dsimp [v, w]
          rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
          simp only [Function.update_self]
          congr 1
          apply Finset.prod_congr rfl
          intro l hl
          rw [Function.update_of_ne (Finset.ne_of_mem_erase hl)]
        have hv : v a = w * y i ^ (a i).val := by
          simpa only [Function.update_eq_self] using update (a i)
        rw [hv, mul_assoc, ← pow_succ]
        by_cases hb : (a i).val + 1 < e i
        · rw [← update ⟨(a i).val + 1, hb⟩]
          exact Submodule.subset_span ⟨_, rfl⟩
        · have heq : (a i).val + 1 = e i := by have := (a i).isLt; omega
          rw [heq, reduce, mul_neg, Finset.mul_sum]
          apply S.neg_mem
          apply S.sum_mem
          intro b hb
          have hblt := Finset.mem_range.mp hb
          have hvb : w * y i ^ b ∈ S := by
            rw [← update ⟨b, hblt⟩]
            exact Submodule.subset_span ⟨_, rfl⟩
          have hh := coeff_mul i lower ((p i).coeff b) _ hvb
          rw [mul_right_comm, mul_assoc] at hh
          exact hh
      | zero => simp
      | add z w _ _ hz hw => simpa only [add_mul] using S.add_mem hz hw
      | smul r z _ hz =>
        simpa only [smul_eq, mul_assoc] using S.smul_mem r hz
  exact stable j.val j rfl (v a) (Submodule.subset_span ⟨a, rfl⟩)

/-- Bounded monomials span the triangular quotient.
Source: Stacks Project, Algebra, proofs of Tags 07BV and 08JZ.
(blueprint: lem-weil-pbc-triangular-field-model-bounded-spanning).

Proof: Identify the quotient by hT-1 with D=k[X][1/h] via the localization
presentation. Agreement on k[X] identifies psi with its canonical map. Split
off the last tower variable and identify the simultaneous quotient with the
successive monic quotients by the universal maps fixing every variable. Divide
an arbitrary representative by the mapped last monic polynomial. Its remainder
has degree below e_i, and represents the same quotient class. Inductively
expand each remainder coefficient in earlier bounded monomials. Collecting
coefficients gives the displayed expansion indexed by all bounded exponent
tuples. The base case m=0 is the localization presentation and its single
coefficient. If h=0 both rings are zero. If some e_i=0, monicity makes p_i=1,
so the quotient is zero; its zero element is represented by the unique function
on the empty exponent set. The argument needs no field evaluation. -/
theorem triangularFieldModel_bounded_spanning
    (k : Type u) [Field k] (d m : ℕ) (h : MvPolynomial (Fin d) k)
    (p : (i : Fin m) → Polynomial (MvPolynomial (Fin (d + 1 + i.val)) k))
    (e : Fin m → ℕ) (hp : ∀ i, (p i).Monic)
    (he : ∀ i, (p i).natDegree = e i)
    (psi : Localization.Away h →ₐ[k]
      (MvPolynomial (Fin (d + 1 + m)) k ⧸
        Ideal.ofList (triangularFieldModelEquations k d m h p)))
    (hpsi : ∀ r : MvPolynomial (Fin d) k,
      psi (algebraMap _ (Localization.Away h) r) = Ideal.Quotient.mk _
        (MvPolynomial.rename (fun j : Fin d ↦
          (⟨j.val, by omega⟩ : Fin (d + 1 + m))) r))
    (q : (MvPolynomial (Fin (d + 1 + m)) k ⧸
        Ideal.ofList (triangularFieldModelEquations k d m h p))) :
    ∃ c : (((i : Fin m) → Fin (e i)) → Localization.Away h), (∑ a : ((i : Fin m) → Fin (e i)),
        psi (c a) * (∏ i : Fin m,
          (Ideal.Quotient.mk _ (MvPolynomial.X
            (⟨d + 1 + i.val, by omega⟩ : Fin (d + 1 + m)))) ^ (a i).val)) = q := by
  classical
  let I := Ideal.ofList (triangularFieldModelEquations k d m h p)
  let Q := MvPolynomial (Fin (d + 1 + m)) k ⧸ I
  let D := Localization.Away h
  let pi : MvPolynomial (Fin (d + 1 + m)) k →+* Q := Ideal.Quotient.mk I
  let : Algebra D Q := psi.toRingHom.toAlgebra
  let y (i : Fin m) : Q := pi (MvPolynomial.X ⟨d + 1 + i.val, by omega⟩)
  let v (a : (i : Fin m) → Fin (e i)) : Q := ∏ i, y i ^ (a i).val
  let S : Submodule D Q := Submodule.span D (Set.range v)
  have smul_eq (r : D) (z : Q) : r • z = psi r * z := rfl
  have one_mem : (1 : Q) ∈ S := by
    by_cases hz : ∃ i, e i = 0
    · obtain ⟨i, hi⟩ := hz
      have hpi : p i = 1 := Polynomial.eq_one_of_monic_natDegree_zero (hp i)
        ((he i).trans hi)
      have hmem : (1 : MvPolynomial (Fin (d + 1 + m)) k) ∈ I := by
        apply Ideal.subset_span
        simp only [triangularFieldModelEquations, List.mem_cons, List.mem_ofFn]
        right
        exact ⟨i, by simp [hpi]⟩
      have hzero : (1 : Q) = 0 := by
        simpa only [map_one] using (Ideal.Quotient.eq_zero_iff_mem.mpr hmem)
      rw [hzero]
      exact S.zero_mem
    · have hpos (i : Fin m) : 0 < e i := by
        have := not_exists.mp hz i
        omega
      let a : (i : Fin m) → Fin (e i) := fun i ↦ ⟨0, hpos i⟩
      have hv : v a = 1 := by simp [v, a]
      rw [← hv]
      exact Submodule.subset_span ⟨a, rfl⟩
  have image_mem (r : D) : psi r ∈ S := by
    simpa only [smul_eq, mul_one] using S.smul_mem r one_mem
  have hloc : pi (MvPolynomial.rename (fun j : Fin d ↦
      (⟨j.val, by omega⟩ : Fin (d + 1 + m))) h) *
      pi (MvPolynomial.X ⟨d, by omega⟩) = 1 := by
    apply sub_eq_zero.mp
    rw [← map_mul, ← map_one pi, ← map_sub]
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    apply Ideal.subset_span
    exact List.mem_cons_self
  have ht : pi (MvPolynomial.X ⟨d, by omega⟩) =
      psi (IsLocalization.Away.invSelf (S := D) h) := by
    have hinv := congrArg psi (IsLocalization.Away.mul_invSelf (S := D) h)
    rw [map_mul, map_one, hpsi] at hinv
    calc
      pi (MvPolynomial.X ⟨d, by omega⟩) =
          pi (MvPolynomial.X ⟨d, by omega⟩) *
            (pi (MvPolynomial.rename (fun j : Fin d ↦
              (⟨j.val, by omega⟩ : Fin (d + 1 + m))) h) *
              psi (IsLocalization.Away.invSelf (S := D) h)) := by rw [hinv, mul_one]
      _ = psi (IsLocalization.Away.invSelf (S := D) h) := by
        rw [← mul_assoc, mul_comm (pi (MvPolynomial.X _)), hloc, one_mul]
  have mul_y (z : Q) (hz : z ∈ S) (j : Fin m) : z * y j ∈ S := by
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨a, rfl⟩ := hz
      exact triangularFieldModel_bounded_mul k d m h p e hp he psi hpsi a j
    | zero => simp
    | add z w _ _ hz hw => simpa only [add_mul] using S.add_mem hz hw
    | smul r z _ hz =>
      simpa only [smul_eq, mul_assoc] using S.smul_mem r hz
  have mul_X (z : Q) (hz : z ∈ S) (j : Fin (d + 1 + m)) :
      z * pi (MvPolynomial.X j) ∈ S := by
    by_cases hj : j.val < d
    · let j' : Fin d := ⟨j.val, hj⟩
      have hx := hpsi (MvPolynomial.X j')
      simp only [MvPolynomial.rename_X] at hx
      have hindex : (⟨j'.val, by omega⟩ : Fin (d + 1 + m)) = j := Fin.ext rfl
      rw [hindex] at hx
      rw [← hx, mul_comm]
      exact S.smul_mem (algebraMap _ D (MvPolynomial.X j')) hz
    · by_cases hje : j.val = d
      · have hindex : j = (⟨d, by omega⟩ : Fin (d + 1 + m)) := Fin.ext hje
        rw [hindex, ht, mul_comm]
        exact S.smul_mem (IsLocalization.Away.invSelf (S := D) h) hz
      · let j' : Fin m := ⟨j.val - (d + 1), by omega⟩
        have hindex : j = (⟨d + 1 + j'.val, by omega⟩ : Fin (d + 1 + m)) := by
          apply Fin.ext
          dsimp [j']
          omega
        rw [hindex]
        exact mul_y z hz j'
  have all_mem (f : MvPolynomial (Fin (d + 1 + m)) k) : pi f ∈ S := by
    induction f using MvPolynomial.induction_on with
    | C a =>
      have hc := hpsi (MvPolynomial.C a)
      simp only [MvPolynomial.rename_C] at hc
      rw [← hc]
      exact image_mem _
    | add f g hf hg => simpa only [map_add] using S.add_mem hf hg
    | mul_X f j hf => simpa only [map_mul] using mul_X (pi f) hf j
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective q
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun D).mp (all_mem f)
  exact ⟨c, hc⟩

end FieldTheory
