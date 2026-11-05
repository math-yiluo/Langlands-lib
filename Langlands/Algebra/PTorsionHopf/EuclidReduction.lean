import Langlands.Algebra.PTorsionHopf.AdditivePolynomials
import Mathlib.RingTheory.Bialgebra.Primitive
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.Algebraic.Basic

/-! # Reducing primitive generating tuples along additive relations -/

noncomputable section

universe u

open Polynomial Coalgebra

namespace Langlands.Algebra.PTorsionHopf

variable {k : Type u} [Field k] {A : Type u} [CommRing A] [Bialgebra k A]

/-- A finite family of primitive elements generating the algebra. -/
def IsPrimitiveGenerating {s : ℕ} (y : Fin s → A) : Prop :=
  (∀ i, Bialgebra.IsPrimitiveElem k (y i)) ∧ Algebra.adjoin k (Set.range y) = ⊤

/-- Frobenius powers of primitive elements are primitive. -/
theorem isPrimitiveElem_pow_char_pow (p : ℕ) [Fact p.Prime] [CharP k p] {x : A}
    (hx : Bialgebra.IsPrimitiveElem k x) (n : ℕ) :
    Bialgebra.IsPrimitiveElem k (x ^ p ^ n) := by
  refine ⟨?_, ?_⟩
  · rw [← Bialgebra.counitAlgHom_apply, map_pow, Bialgebra.counitAlgHom_apply, hx.counit_eq_zero,
      zero_pow (pow_ne_zero _ (Fact.out : p.Prime).ne_zero)]
  · rw [← Bialgebra.comulAlgHom_apply, map_pow, Bialgebra.comulAlgHom_apply,
      hx.comul_eq_tmul_add_tmul, add_pow_char_pow_of_algebra (k := k) p n,
      Algebra.TensorProduct.tmul_pow, Algebra.TensorProduct.tmul_pow, one_pow]

variable [IsDomain A]

/-- A primitive element of a domain that is algebraic over the field is zero. -/
theorem eq_zero_of_aeval_eq_zero {x : A} (hx : Bialgebra.IsPrimitiveElem k x) {f : k[X]}
    (hf : f ≠ 0) (h : aeval x f = 0) : x = 0 := by
  by_contra hx0
  have hint : IsIntegral k x := (show IsAlgebraic k x from ⟨f, hf, h⟩).isIntegral
  have hu := (hint.isUnit hx0).map (Bialgebra.counitAlgHom k A)
  rw [Bialgebra.counitAlgHom_apply, hx.counit_eq_zero] at hu
  exact not_isUnit_zero hu

open Classical in
/-- The size of a polynomial for the reduction: its degree plus one if it is nonzero. -/
def relTerm (g : k[X]) : ℕ := if g = 0 then 0 else g.natDegree + 1

theorem relTerm_of_ne_zero {g : k[X]} (hg : g ≠ 0) : relTerm g = g.natDegree + 1 := by
  simp [relTerm, hg]

theorem relTerm_zero : relTerm (0 : k[X]) = 0 := by simp [relTerm]

variable (p : ℕ) [Fact p.Prime] [CharP k p] [PerfectRing k p]

include p in
/-- **Euclid reduction.** An additive relation, not all of whose polynomials vanish, among a
primitive generating tuple of length `s + 1` produces a primitive generating tuple of length
`s`. The induction is on the total size of the relation. -/
theorem exists_isPrimitiveGenerating_of_relation :
    ∀ (N : ℕ) {s : ℕ} (y : Fin (s + 1) → A) (f : Fin (s + 1) → k[X]),
      IsPrimitiveGenerating (k := k) y → (∀ i, IsAdditivePoly (f i)) → (∃ i, f i ≠ 0) →
      ∑ i, aeval (y i) (f i) = 0 → ∑ i, relTerm (f i) ≤ N →
      ∃ y' : Fin s → A, IsPrimitiveGenerating (k := k) y' := by
  intro N
  induction N with
  | zero =>
    intro s y f _ _ hne _ hN
    obtain ⟨i, hi⟩ := hne
    have h := (Finset.single_le_sum (f := fun j => relTerm (f j)) (fun j _ => Nat.zero_le _)
      (Finset.mem_univ i)).trans hN
    rw [relTerm_of_ne_zero hi] at h
    omega
  | succ N ih =>
    intro s y f hy hf hne hrel hN
    classical
    by_cases hsingle : ∃ a, f a ≠ 0 ∧ ∀ b, b ≠ a → f b = 0
    · obtain ⟨a, ha, hb⟩ := hsingle
      have hya : y a = 0 := by
        rw [Finset.sum_eq_single a (fun b _ hba => by rw [hb b hba, map_zero]) (by simp)] at hrel
        exact eq_zero_of_aeval_eq_zero (hy.1 a) ha hrel
      refine ⟨fun j => y (a.succAbove j), fun j => hy.1 _, ?_⟩
      rw [eq_top_iff, ← hy.2, Algebra.adjoin_le_iff]
      rintro _ ⟨i, rfl⟩
      by_cases hia : i = a
      · subst hia
        rw [hya]
        exact Subalgebra.zero_mem _
      · obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hia
        exact Algebra.subset_adjoin ⟨j, rfl⟩
    · set S := Finset.univ.filter (fun i => f i ≠ 0) with hSdef
      have hS : S.Nonempty := by
        obtain ⟨i, hi⟩ := hne
        exact ⟨i, by simp [hSdef, hi]⟩
      obtain ⟨a, haS, hamin⟩ := S.exists_min_image (fun i => (f i).natDegree) hS
      have ha : f a ≠ 0 := (Finset.mem_filter.1 haS).2
      obtain ⟨b, hba, hb⟩ : ∃ b, b ≠ a ∧ f b ≠ 0 := by
        by_contra h
        push Not at h
        exact hsingle ⟨a, ha, h⟩
      have hab : (f a).natDegree ≤ (f b).natDegree := hamin b (by simp [hSdef, hb])
      obtain ⟨-, ea, hea⟩ := (hf a).natDegree_eq_pow p ha
      obtain ⟨-, eb, heb⟩ := (hf b).natDegree_eq_pow p hb
      have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
      have heab : ea ≤ eb := by
        rw [hea, heb] at hab
        exact (Nat.pow_le_pow_iff_right hp1).1 hab
      set q := p ^ (eb - ea) with hq
      set c := (iterateFrobeniusEquiv k p ea).symm ((f b).leadingCoeff / (f a).leadingCoeff)
        with hcdef
      have hc : c ^ p ^ ea = (f b).leadingCoeff / (f a).leadingCoeff := by
        rw [← iterateFrobeniusEquiv_def, hcdef, RingEquiv.apply_symm_apply]
      have hc0 : c ≠ 0 := by
        intro h
        rw [h, zero_pow (pow_ne_zero _ (by omega))] at hc
        exact div_ne_zero (leadingCoeff_ne_zero.2 hb) (leadingCoeff_ne_zero.2 ha) hc.symm
      set g : k[X] := C c * X ^ q with hgdef
      have hg : IsAdditivePoly g := isAdditivePoly_C_mul_X_pow p c (eb - ea)
      have hgdeg : g.natDegree = q := natDegree_C_mul_X_pow q c hc0
      have hgval : aeval (y b) g = c • y b ^ q := by
        rw [hgdef, map_mul, aeval_C, map_pow, aeval_X, Algebra.smul_def]
      set y' := Function.update y a (y a + c • y b ^ q) with hy'def
      set f' := Function.update f b (f b - (f a).comp g) with hf'def
      have hy'a : y' a = y a + c • y b ^ q := by rw [hy'def, Function.update_self]
      have hy'b : y' b = y b := by rw [hy'def, Function.update_of_ne hba]
      have hf'a : f' a = f a := by rw [hf'def, Function.update_of_ne (Ne.symm hba)]
      have hf'b : f' b = f b - (f a).comp g := by rw [hf'def, Function.update_self]
      -- the strict decrease at `b`
      have hcompdeg : ((f a).comp g).natDegree = (f b).natDegree := by
        rw [natDegree_comp, hgdeg, hea, heb, hq, ← pow_add, Nat.add_sub_cancel' heab]
      have hcomp0 : (f a).comp g ≠ 0 := by
        intro h
        rw [h, natDegree_zero, heb] at hcompdeg
        exact pow_ne_zero _ (by omega) hcompdeg.symm
      have hcomplc : ((f a).comp g).leadingCoeff = (f b).leadingCoeff := by
        rw [leadingCoeff_comp (by rw [hgdeg]; exact pow_ne_zero _ (by omega)), hgdef,
          leadingCoeff_C_mul_X_pow, hea, hc, mul_div_cancel₀ _ (leadingCoeff_ne_zero.2 ha)]
      have hltb : relTerm (f' b) < relTerm (f b) := by
        rw [hf'b, relTerm_of_ne_zero hb]
        by_cases h0 : f b - (f a).comp g = 0
        · rw [h0, relTerm_zero]
          omega
        · rw [relTerm_of_ne_zero h0]
          have hdeg := degree_sub_lt_left (p := f b) (q := (f a).comp g)
            (by rw [degree_eq_natDegree hb, degree_eq_natDegree hcomp0, hcompdeg]) hb
            hcomplc.symm
          have := natDegree_lt_natDegree h0 hdeg
          omega
      refine ih y' f' ?_ ?_ ?_ ?_ ?_
      · refine ⟨fun i => ?_, ?_⟩
        · by_cases hia : i = a
          · subst hia
            rw [hy'a]
            exact (hy.1 i).add ((isPrimitiveElem_pow_char_pow p (hy.1 b) _).smul c)
          · rw [hy'def, Function.update_of_ne hia]
            exact hy.1 i
        · rw [eq_top_iff, ← hy.2, Algebra.adjoin_le_iff]
          rintro _ ⟨i, rfl⟩
          by_cases hia : i = a
          · subst hia
            have hyi : y i = y' i - c • y' b ^ q := by rw [hy'a, hy'b, add_sub_cancel_right]
            rw [hyi]
            exact Subalgebra.sub_mem _ (Algebra.subset_adjoin (Set.mem_range_self i))
              (Subalgebra.smul_mem _
                (Subalgebra.pow_mem _ (Algebra.subset_adjoin (Set.mem_range_self b)) _) _)
          · have hyi : y i = y' i := by rw [hy'def, Function.update_of_ne hia]
            rw [hyi]
            exact Algebra.subset_adjoin (Set.mem_range_self i)
      · intro i
        by_cases hib : i = b
        · subst hib
          rw [hf'b]
          exact (hf i).sub ((hf a).comp hg)
        · rw [hf'def, Function.update_of_ne hib]
          exact hf i
      · exact ⟨a, by rw [hf'a]; exact ha⟩
      · set δ := aeval (c • y b ^ q) (f a) with hδ
        have hT : ∀ i, aeval (y' i) (f' i) =
            aeval (y i) (f i) + ((if i = a then δ else 0) - (if i = b then δ else 0)) := by
          intro i
          by_cases hia : i = a
          · subst hia
            rw [hy'a, hf'a, hf i A, ite_eq_left rfl, ite_eq_right hba.symm, sub_zero]
          · by_cases hib : i = b
            · subst hib
              rw [hy'b, hf'b, map_sub, aeval_comp, hgval, ite_eq_right hia, ite_eq_left rfl]
              ring
            · rw [hy'def, hf'def, Function.update_of_ne hia, Function.update_of_ne hib,
                ite_eq_right hia, ite_eq_right hib, sub_zero, add_zero]
        rw [Finset.sum_congr rfl fun i _ => hT i, Finset.sum_add_distrib, Finset.sum_sub_distrib,
          Finset.sum_ite_eq', Finset.sum_ite_eq', hrel]
        simp
      · have hlt : ∑ i, relTerm (f' i) < ∑ i, relTerm (f i) := by
          refine Finset.sum_lt_sum (fun i _ => ?_) ⟨b, Finset.mem_univ b, hltb⟩
          by_cases hib : i = b
          · subst hib
            exact hltb.le
          · rw [hf'def, Function.update_of_ne hib]
        omega

end Langlands.Algebra.PTorsionHopf
