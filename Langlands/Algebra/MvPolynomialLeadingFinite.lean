import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.MvPolynomial.Symmetric.NewtonIdentities
import Mathlib.RingTheory.Polynomial.Vieta
import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic

/-! # Finiteness of polynomial rings from leading forms -/

noncomputable section

universe u v w

set_option autoImplicit false

namespace Langlands.Algebra.MvPolynomialLeadingFinite

open MvPolynomial Finsupp

variable {k : Type u} [Field k] {σ : Type v}

/-- All monomials of `p` have total degree at most `m`. -/
def DegLE (m : ℕ) (p : MvPolynomial σ k) : Prop := ∀ α ∈ p.support, α.degree ≤ m

/-- All monomials of `p` have total degree less than `m`. -/
def DegLT (m : ℕ) (p : MvPolynomial σ k) : Prop := ∀ α ∈ p.support, α.degree < m

section Degrees

variable {m n : ℕ} {p q : MvPolynomial σ k}

theorem DegLT.degLE (h : DegLT m p) : DegLE m p := fun α hα => (h α hα).le

theorem DegLT.mono (h : DegLT m p) (hmn : m ≤ n) : DegLT n p :=
  fun α hα => lt_of_lt_of_le (h α hα) hmn

theorem degLT_add (hp : DegLT m p) (hq : DegLT m q) : DegLT m (p + q) := by
  classical
  intro α hα
  rcases Finset.mem_union.mp (MvPolynomial.support_add hα) with h | h
  · exact hp α h
  · exact hq α h

theorem degLT_smul (c : k) (hp : DegLT m p) : DegLT m (c • p) :=
  fun α hα => hp α (MvPolynomial.support_smul hα)

theorem degLT_sub (hp : DegLT m p) (hq : DegLT m q) : DegLT m (p - q) := by
  rw [sub_eq_add_neg, ← neg_one_smul k q]
  exact degLT_add hp (degLT_smul _ hq)

theorem degLT_zero : DegLT m (0 : MvPolynomial σ k) := fun α hα => by simp at hα

theorem degLT_sum {ι : Type*} (s : Finset ι) (f : ι → MvPolynomial σ k)
    (h : ∀ i ∈ s, DegLT m (f i)) : DegLT m (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (degLT_zero (m := m))
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact degLT_add (h i (Finset.mem_insert_self i s))
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

theorem degLE_mul (hp : DegLE m p) (hq : DegLE n q) : DegLE (m + n) (p * q) := by
  classical
  intro α hα
  obtain ⟨β, hβ, γ, hγ, rfl⟩ := Finset.mem_add.mp (support_mul p q hα)
  rw [map_add]
  exact Nat.add_le_add (hp β hβ) (hq γ hγ)

theorem degLT_mul_left (hp : DegLT m p) (hq : DegLE n q) : DegLT (m + n) (p * q) := by
  classical
  intro α hα
  obtain ⟨β, hβ, γ, hγ, rfl⟩ := Finset.mem_add.mp (support_mul p q hα)
  rw [map_add]
  exact Nat.add_lt_add_of_lt_of_le (hp β hβ) (hq γ hγ)

theorem degLT_mul_right (hp : DegLE m p) (hq : DegLT n q) : DegLT (m + n) (p * q) := by
  classical
  intro α hα
  obtain ⟨β, hβ, γ, hγ, rfl⟩ := Finset.mem_add.mp (support_mul p q hα)
  rw [map_add]
  exact Nat.add_lt_add_of_le_of_lt (hp β hβ) (hq γ hγ)

theorem degLE_of_isHomogeneous (h : p.IsHomogeneous m) : DegLE m p := fun α hα => by
  have := h (MvPolynomial.mem_support_iff.mp hα)
  have h1 : (weight (1 : σ → ℕ)) α = α.degree := by
    rw [Finsupp.degree_eq_weight_one]; rfl
  rw [h1] at this
  exact this.le

end Degrees

section Leading

variable {J : Type w} (f t : J → MvPolynomial σ k) (n : J → ℕ)
  (ht : ∀ j, (t j).IsHomogeneous (n j)) (hft : ∀ j, DegLT (n j) (f j - t j))

include ht hft in
theorem degLE_f (j : J) : DegLE (n j) (f j) := by
  have h : f j = (f j - t j) + t j := by ring
  intro α hα
  rw [h] at hα
  classical
  rcases Finset.mem_union.mp (MvPolynomial.support_add hα) with h' | h'
  · exact (hft j α h').le
  · exact degLE_of_isHomogeneous (ht j) α h'

include ht hft in
theorem degLE_pow_f (j : J) (e : ℕ) : DegLE (e * n j) (f j ^ e) := by
  induction e with
  | zero => intro α hα; simp at hα; simp [hα]
  | succ e ih =>
    rw [pow_succ, show (e + 1) * n j = e * n j + n j by ring]
    exact degLE_mul ih (degLE_f f t n ht hft j)

include ht hft in
theorem degLT_pow_sub (j : J) (e : ℕ) (he : e ≠ 0) :
    DegLT (e * n j) (f j ^ e - t j ^ e) := by
  induction e with
  | zero => exact absurd rfl he
  | succ e ih =>
    have hsplit : f j ^ (e + 1) - t j ^ (e + 1) =
        (f j - t j) * f j ^ e + t j * (f j ^ e - t j ^ e) := by ring
    rw [hsplit]
    refine degLT_add ?_ ?_
    · have := degLT_mul_left (hft j) (degLE_pow_f f t n ht hft j e)
      exact this.mono (by ring_nf; omega)
    · rcases Nat.eq_zero_or_pos e with h | h
      · subst h
        simpa using (degLT_zero (m := (0 + 1) * n j))
      · have := degLT_mul_right (degLE_of_isHomogeneous (ht j)) (ih h.ne')
        exact this.mono (by ring_nf; omega)

include ht hft in
theorem degLE_prod_f (s : Finset J) (e : J → ℕ) :
    DegLE (∑ j ∈ s, e j * n j) (∏ j ∈ s, f j ^ e j) := by
  classical
  induction s using Finset.induction_on with
  | empty => intro α hα; simp at hα; simp [hα]
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi]
    exact degLE_mul (degLE_pow_f f t n ht hft i (e i)) ih

include ht hft in
theorem degLT_prod_sub (s : Finset J) (e : J → ℕ) (he : ∀ j ∈ s, e j ≠ 0) :
    DegLT (∑ j ∈ s, e j * n j) (∏ j ∈ s, f j ^ e j - ∏ j ∈ s, t j ^ e j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (degLT_zero (m := 0))
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi, Finset.sum_insert hi]
    have hsplit : f i ^ e i * ∏ j ∈ s, f j ^ e j - t i ^ e i * ∏ j ∈ s, t j ^ e j =
        (f i ^ e i - t i ^ e i) * ∏ j ∈ s, f j ^ e j +
          t i ^ e i * (∏ j ∈ s, f j ^ e j - ∏ j ∈ s, t j ^ e j) := by ring
    rw [hsplit]
    refine degLT_add ?_ ?_
    · exact degLT_mul_left (degLT_pow_sub f t n ht hft i (e i) (he i (Finset.mem_insert_self i s)))
        (degLE_prod_f f t n ht hft s e)
    · have hp : (t i ^ e i).IsHomogeneous (e i * n i) := by
        rw [mul_comm]; exact (ht i).pow (e i)
      exact degLT_mul_right (degLE_of_isHomogeneous hp)
        (ih fun j hj => he j (Finset.mem_insert_of_mem hj))

include ht in
theorem isHomogeneous_aeval_monomial (d : J →₀ ℕ) (r : k) :
    (aeval t (monomial d r)).IsHomogeneous (weight n d) := by
  classical
  rw [aeval_monomial, ← Algebra.smul_def]
  refine (homogeneousSubmodule σ k _).smul_mem r ?_
  rw [mem_homogeneousSubmodule, weight_apply, Finsupp.prod, Finsupp.sum]
  refine IsHomogeneous.prod _ _ _ fun j _ => ?_
  have := (ht j).pow (d j)
  rwa [mul_comm, ← smul_eq_mul] at this

include ht hft in
/-- For a polynomial `Q` weighted homogeneous of weight `m` (variable `j` of weight `n j`),
substituting `f` instead of the leading forms `t` changes `Q(t)` only in degrees below `m`. -/
theorem degLT_aeval_sub {Q : MvPolynomial J k} {m : ℕ} (hQ : Q.IsWeightedHomogeneous n m) :
    DegLT m (aeval f Q - aeval t Q) := by
  classical
  induction hQ using IsWeightedHomogeneous.induction_on with
  | zero => simpa using (degLT_zero (m := m))
  | add p q _ _ hp hq =>
    rw [map_add, map_add, add_sub_add_comm]
    exact degLT_add hp hq
  | monomial d r hr =>
    rw [aeval_monomial, aeval_monomial, ← mul_sub, ← Algebra.smul_def]
    refine degLT_smul r ?_
    rw [← hr, weight_apply, Finsupp.sum, Finsupp.prod, Finsupp.prod]
    have h := degLT_prod_sub f t n ht hft d.support d (fun j hj => Finsupp.mem_support_iff.mp hj)
    simpa only [smul_eq_mul] using h

include ht in
/-- Taking a homogeneous component commutes with substituting homogeneous leading forms. -/
theorem homogeneousComponent_aeval (m : ℕ) (Q : MvPolynomial J k) :
    homogeneousComponent m (aeval t Q) = aeval t (weightedHomogeneousComponent n m Q) := by
  classical
  induction Q using MvPolynomial.induction_on' with
  | monomial d r =>
    rw [homogeneousComponent_of_mem (isHomogeneous_aeval_monomial t n ht d r),
      weightedHomogeneousComponent_of_mem (isWeightedHomogeneous_monomial n d r rfl)]
    split_ifs <;> simp
  | add p q hp hq => rw [map_add, map_add, hp, hq, map_add, map_add]

end Leading

section MainFinite

/-- The degree-`m` component of a product with a monomial. -/
theorem homogeneousComponent_mul_monomial (x : MvPolynomial σ k) (β : σ →₀ ℕ) (m : ℕ) :
    homogeneousComponent m (x * monomial β 1) =
      if β.degree ≤ m then homogeneousComponent (m - β.degree) x * monomial β 1 else 0 := by
  classical
  ext α
  have hdeg (h : β ≤ α) : (α - β).degree + β.degree = α.degree := by
    rw [← map_add, tsub_add_cancel_of_le h]
  rw [coeff_homogeneousComponent, coeff_mul_monomial']
  by_cases hβm : β.degree ≤ m
  · simp only [hβm, ↓reduceIte, coeff_mul_monomial', coeff_homogeneousComponent, mul_one]
    by_cases hβα : β ≤ α
    · have h := hdeg hβα
      by_cases hα : α.degree = m
      · have h' : (α - β).degree = m - β.degree := by omega
        simp [hβα, hα, h']
      · have h' : ¬ (α - β).degree = m - β.degree := by omega
        simp [hβα, hα, h']
    · simp [hβα]
  · simp only [hβm, ↓reduceIte, AddMonoidAlgebra.coeff_zero, Finsupp.coe_zero, Pi.zero_apply]
    by_cases hα : α.degree = m
    · by_cases hβα : β ≤ α
      · have h := hdeg hβα
        omega
      · simp [hβα]
    · simp [hα]

variable {J : Type w} (f t : J → MvPolynomial σ k) (n : J → ℕ)
  (ht : ∀ j, (t j).IsHomogeneous (n j)) (hft : ∀ j, DegLT (n j) (f j - t j))

include ht hft in
/-- **Finiteness from leading forms.** Let the polynomial ring be a finite module over the
subalgebra generated by homogeneous forms `t j` of degrees `n j`, and let each `f j` differ from
`t j` only in lower degrees. Then the polynomial ring is a finite module over every subalgebra
containing all `f j`. -/
theorem moduleFinite_of_leading
    (hfin : Module.Finite (Algebra.adjoin k (Set.range t)) (MvPolynomial σ k))
    (A : Subalgebra k (MvPolynomial σ k)) (hA : ∀ j, f j ∈ A) :
    Module.Finite A (MvPolynomial σ k) := by
  classical
  let T := Algebra.adjoin k (Set.range t)
  obtain ⟨G, hG⟩ := hfin.fg_top
  let S : Finset (σ →₀ ℕ) := G.biUnion fun g => g.support
  let mon : (σ →₀ ℕ) → MvPolynomial σ k := fun β => monomial β 1
  let M : Submodule A (MvPolynomial σ k) := Submodule.span A (mon '' S)
  have hmonT : ∀ x : MvPolynomial σ k, x ∈ Submodule.span T (mon '' S) := by
    have hle : (G : Set (MvPolynomial σ k)) ⊆ Submodule.span T (mon '' S) := by
      intro g hg
      rw [g.as_sum]
      refine Submodule.sum_mem _ fun β hβ => ?_
      have hβS : β ∈ S := Finset.mem_biUnion.mpr ⟨g, hg, hβ⟩
      rw [show monomial β (g.coeff β) = (algebraMap k T (g.coeff β)) • mon β by
        rw [Algebra.smul_def]
        simp [mon, C_mul_monomial]]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨β, hβS, rfl⟩)
    intro x
    have hx : x ∈ Submodule.span T (G : Set (MvPolynomial σ k)) := by rw [hG]; trivial
    exact (Submodule.span_le.mpr hle) hx
  have hAf (Q : MvPolynomial J k) : aeval f Q ∈ A := by
    have h : Algebra.adjoin k (Set.range f) ≤ A :=
      Algebra.adjoin_le (by rintro _ ⟨j, rfl⟩; exact hA j)
    apply h
    rw [Algebra.adjoin_range_eq_range_aeval]
    exact ⟨Q, rfl⟩
  have key (N : ℕ) : ∀ γ : σ →₀ ℕ, γ.degree = N → mon γ ∈ M := by
    induction N using Nat.strong_induction_on with
    | _ N ih =>
    intro γ hγ
    obtain ⟨l, hl, hlx⟩ := (Finsupp.mem_span_image_iff_linearCombination T).mp (hmonT (mon γ))
    have hQ (β : σ →₀ ℕ) : ∃ Q : MvPolynomial J k, aeval t Q = (l β : MvPolynomial σ k) := by
      have h : (l β : MvPolynomial σ k) ∈ Algebra.adjoin k (Set.range t) := (l β).property
      rw [Algebra.adjoin_range_eq_range_aeval] at h
      exact h
    choose Q hQ using hQ
    have hsum : mon γ = ∑ β ∈ S, aeval t (Q β) * mon β := by
      rw [← hlx, Finsupp.linearCombination_apply, Finsupp.sum_of_support_subset l hl]
      · refine Finset.sum_congr rfl fun β _ => ?_
        rw [Subalgebra.smul_def, hQ, smul_eq_mul]
      · intro β _; simp
    let Q' : (σ →₀ ℕ) → MvPolynomial J k := fun β =>
      if β.degree ≤ N then weightedHomogeneousComponent n (N - β.degree) (Q β) else 0
    have hsum' : mon γ = ∑ β ∈ S, aeval t (Q' β) * mon β := by
      have h := congrArg (homogeneousComponent N) hsum
      rw [homogeneousComponent_of_mem (show mon γ ∈ homogeneousSubmodule σ k N by
          rw [mem_homogeneousSubmodule, ← hγ]
          exact isHomogeneous_monomial _ rfl), ite_eq_left rfl, map_sum] at h
      rw [h]
      refine Finset.sum_congr rfl fun β _ => ?_
      rw [homogeneousComponent_mul_monomial]
      simp only [Q']
      split_ifs
      · rw [homogeneousComponent_aeval t n ht]
      · simp
    set y := ∑ β ∈ S, aeval f (Q' β) * mon β
    have hy : y ∈ M := Submodule.sum_mem _ fun β hβ => by
      rw [show aeval f (Q' β) * mon β = (⟨aeval f (Q' β), hAf _⟩ : A) • mon β from rfl]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨β, hβ, rfl⟩)
    have hr : DegLT N (mon γ - y) := by
      rw [hsum', ← Finset.sum_sub_distrib]
      refine degLT_sum _ _ fun β _ => ?_
      rw [← sub_mul]
      simp only [Q']
      split_ifs with hβ
      · have h1 := degLT_aeval_sub f t n ht hft
          (weightedHomogeneousComponent_isWeightedHomogeneous (w := n) (N - β.degree) (Q β))
        have h2 : DegLT (N - β.degree) (aeval t (weightedHomogeneousComponent n (N - β.degree)
            (Q β)) - aeval f (weightedHomogeneousComponent n (N - β.degree) (Q β))) := by
          rw [← neg_sub, ← neg_one_smul k]
          exact degLT_smul _ h1
        have h3 := degLT_mul_left h2 (degLE_of_isHomogeneous
          (isHomogeneous_monomial (d := β) (1 : k) rfl))
        exact h3.mono (by omega)
      · simpa using (degLT_zero (m := N))
    have hrM : mon γ - y ∈ M := by
      rw [(mon γ - y).as_sum]
      refine Submodule.sum_mem _ fun α hα => ?_
      have hαN := hr α hα
      rw [show monomial α ((mon γ - y).coeff α) = ((mon γ - y).coeff α) • mon α by
        simp [mon, smul_monomial]]
      exact Submodule.smul_of_tower_mem _ _ (ih α.degree hαN α rfl)
    have := M.add_mem hrM hy
    rwa [sub_add_cancel] at this
  have htop : (⊤ : Submodule A (MvPolynomial σ k)) ≤ M := by
    intro x _
    rw [x.as_sum]
    refine Submodule.sum_mem _ fun α _ => ?_
    rw [show monomial α (x.coeff α) = (x.coeff α) • mon α by simp [mon, smul_monomial]]
    exact Submodule.smul_of_tower_mem _ _ (key α.degree α rfl)
  refine ⟨⟨S.image mon, ?_⟩⟩
  rw [Finset.coe_image]
  exact top_le_iff.mp htop

end MainFinite


section PowerSums

variable [CharZero k] {S : Type v} [CommRing S] [Nontrivial S] [Algebra k S] {Q : Type w}
  [Fintype Q]
  (ℓ : Q → S) (A : Subalgebra k S)
  (hA : ∀ m, 1 ≤ m → m ≤ Fintype.card Q → ∑ q, ℓ q ^ m ∈ A)

omit [Nontrivial S] in
include hA in
/-- By Newton's identities, the elementary symmetric functions of `ℓ` lie in every
subalgebra containing the power sums `∑ ℓ q ^ m`, `1 ≤ m ≤ card Q`. -/
theorem aeval_esymm_mem (j : ℕ) (hj : j ≤ Fintype.card Q) : aeval ℓ (esymm Q k j) ∈ A := by
  induction j using Nat.strong_induction_on with
  | _ j ih =>
  rcases Nat.eq_zero_or_pos j with rfl | hpos
  · simp [esymm_zero]
  have hN := congrArg (aeval ℓ) (mul_esymm_eq_sum Q k j)
  have hR : aeval ℓ ((-1) ^ (j + 1) * ∑ a ∈ Finset.antidiagonal j with a.1 < j,
      (-1) ^ a.1 * esymm Q k a.1 * psum Q k a.2) ∈ A := by
    rw [map_mul, map_sum]
    refine A.mul_mem (by simpa using A.pow_mem (A.neg_mem A.one_mem) (j + 1)) ?_
    refine A.sum_mem fun a ha => ?_
    obtain ⟨ha1, ha2⟩ := Finset.mem_filter.mp ha
    have hsum := Finset.mem_antidiagonal.mp ha1
    rw [map_mul, map_mul]
    refine A.mul_mem (A.mul_mem (by simpa using A.pow_mem (A.neg_mem A.one_mem) a.1)
      (ih a.1 ha2 (by omega))) ?_
    have : aeval ℓ (psum Q k a.2) = ∑ q, ℓ q ^ a.2 := by simp [psum]
    rw [this]
    exact hA a.2 (by omega) (by omega)
  rw [← hN, map_mul, map_natCast] at hR
  have hj0 : (j : k) ≠ 0 := Nat.cast_ne_zero.mpr hpos.ne'
  have h := A.smul_mem hR (j : k)⁻¹
  rwa [Algebra.smul_def, ← mul_assoc, ← map_natCast (algebraMap k S), ← map_mul,
    inv_mul_cancel₀ hj0, map_one, one_mul] at h

include hA in
/-- Each `ℓ q` is integral over every subalgebra containing the power sums of `ℓ`. -/
theorem isIntegral_of_powerSums (q : Q) : IsIntegral A (ℓ q) := by
  classical
  let s : Multiset S := Finset.univ.val.map ℓ
  let f : Polynomial S := (s.map fun x => Polynomial.X - Polynomial.C x).prod
  have hcard : Multiset.card s = Fintype.card Q := by simp [s, Finset.card_univ]
  have hmonic : f.Monic :=
    Polynomial.monic_multiset_prod_of_monic _ _ fun x _ => Polynomial.monic_X_sub_C x
  have hnat : f.natDegree = Multiset.card s := by
    simp [f]
  have hlifts : f ∈ Polynomial.lifts (algebraMap A S) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro i
    by_cases hi : i ≤ Multiset.card s
    · rw [Multiset.prod_X_sub_C_coeff s hi]
      have he : s.esymm (Multiset.card s - i) = aeval ℓ (esymm Q k (Multiset.card s - i)) := by
        rw [aeval_esymm_eq_multiset_esymm]
      rw [he]
      have hm : (-1) ^ (Multiset.card s - i) * aeval ℓ (esymm Q k (Multiset.card s - i)) ∈ A :=
        A.mul_mem (by simpa using A.pow_mem (A.neg_mem A.one_mem) _)
          (aeval_esymm_mem ℓ A hA _ (by omega))
      exact ⟨⟨_, hm⟩, rfl⟩
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]
      exact ⟨0, map_zero _⟩
  obtain ⟨g, hg, -, hgm⟩ := Polynomial.lifts_and_degree_eq_and_monic hlifts hmonic
  refine ⟨g, hgm, ?_⟩
  rw [← Polynomial.eval_map, hg, Polynomial.eval_multiset_prod]
  apply Multiset.prod_eq_zero
  rw [Multiset.map_map]
  exact Multiset.mem_map.mpr ⟨ℓ q, Multiset.mem_map.mpr ⟨q, Finset.mem_univ_val q, rfl⟩,
    by simp⟩

end PowerSums

end Langlands.Algebra.MvPolynomialLeadingFinite
