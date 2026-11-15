import Mathlib.RingTheory.MvPolynomial.Groebner
import Mathlib.RingTheory.Ideal.Quotient.Defs

/-!
# Monic generators with pairwise coprime squarefree leading monomials

Let `m` be a monomial order and `g : γ → k[X_σ]` a finite family of `m`-monic polynomials over
a field. Suppose the leading monomials `m.degree (g j)` have pairwise disjoint supports.
Then they form a Gröbner basis of `Ideal.span (Set.range g)`
(`CoprimeGroebner.exists_degree_le`): every nonzero element of the ideal has a leading
monomial divisible by some `m.degree (g j)`. This is Buchberger's first criterion. If
moreover the leading monomials are squarefree, the ideal is radical
(`CoprimeGroebner.isRadical`).

The proof uses the subspaces `lvl m g D` spanned by the products `X^u * g j` with
`u + m.degree (g j) ≤ D`. A representation of `f` whose top level `D` exceeds the degree of
`f` is lowered with the Koszul syzygies `X^(δ - d j) g j - X^(δ - d j') g j'`.
-/

noncomputable section

set_option autoImplicit false

namespace Langlands.Archimedean.Kostant

namespace CoprimeGroebner

open MvPolynomial

open scoped MonomialOrder

variable {σ : Type*} (m : MonomialOrder σ) {k : Type*} [Field k] {γ : Type*}
  (g : γ → MvPolynomial σ k)

/-- The `k`-span of the products `X^u * g j` whose formal degree `u + m.degree (g j)` is at
most `D`. -/
def lvl (D : m.syn) : Submodule k (MvPolynomial σ k) :=
  Submodule.span k
    {f | ∃ (j : γ) (u : σ →₀ ℕ), m.toSyn (u + m.degree (g j)) ≤ D ∧ f = monomial u 1 * g j}

theorem lvl_mono {D D' : m.syn} (h : D ≤ D') : lvl m g D ≤ lvl m g D' :=
  Submodule.span_mono fun _ ⟨j, u, hu, hf⟩ => ⟨j, u, hu.trans h, hf⟩

/-- The elements lying in some `lvl m g D'` with `D' < D`. -/
def lvlLT (D : m.syn) : Submodule k (MvPolynomial σ k) where
  carrier := {f | f = 0 ∨ ∃ D' < D, f ∈ lvl m g D'}
  zero_mem' := Or.inl rfl
  add_mem' := by
    intro f f' hf hf'
    simp only [Set.mem_ofPred_eq] at hf hf' ⊢
    rcases hf with rfl | ⟨D₁, h₁, hf⟩ <;> rcases hf' with rfl | ⟨D₂, h₂, hf'⟩
    · left; simp
    · right; exact ⟨D₂, h₂, by simpa using hf'⟩
    · right; exact ⟨D₁, h₁, by simpa using hf⟩
    · right
      exact ⟨max D₁ D₂, max_lt h₁ h₂,
        add_mem (lvl_mono m g (le_max_left _ _) hf) (lvl_mono m g (le_max_right _ _) hf')⟩
  smul_mem' := by
    intro c f hf
    simp only [Set.mem_ofPred_eq] at hf ⊢
    rcases hf with rfl | ⟨D', h', hf⟩
    · left; simp
    · right; exact ⟨D', h', Submodule.smul_mem _ c hf⟩

theorem mem_lvlLT_iff {D : m.syn} {f : MvPolynomial σ k} :
    f ∈ lvlLT m g D ↔ f = 0 ∨ ∃ D' < D, f ∈ lvl m g D' :=
  Iff.rfl

theorem monomial_mul_mem_lvl {D : m.syn} {j : γ} {u : σ →₀ ℕ}
    (hu : m.toSyn (u + m.degree (g j)) ≤ D) (c : k) : monomial u c * g j ∈ lvl m g D := by
  have : monomial u c * g j = c • (monomial u 1 * g j) := by
    rw [← smul_mul_assoc, smul_monomial, smul_eq_mul, mul_one]
  rw [this]
  exact Submodule.smul_mem _ c (Submodule.subset_span ⟨j, u, hu, rfl⟩)

theorem mul_mem_lvl {D : m.syn} {j : γ} {p : MvPolynomial σ k}
    (hp : ∀ u ∈ p.support, m.toSyn (u + m.degree (g j)) ≤ D) : p * g j ∈ lvl m g D := by
  rw [p.as_sum, Finset.sum_mul]
  exact Submodule.sum_mem _ fun u hu => monomial_mul_mem_lvl m g (hp u hu) _

theorem mul_mem_lvlLT {D : m.syn} {j : γ} {p : MvPolynomial σ k}
    (hp : ∀ u ∈ p.support, m.toSyn (u + m.degree (g j)) < D) : p * g j ∈ lvlLT m g D := by
  rw [p.as_sum, Finset.sum_mul]
  exact Submodule.sum_mem _ fun u hu => Or.inr ⟨_, hp u hu, monomial_mul_mem_lvl m g le_rfl _⟩

/-- Elements of `lvl m g D` have degree at most `D`. -/
theorem degree_le_of_mem_lvl {D : m.syn} {f : MvPolynomial σ k} (hf : f ∈ lvl m g D) :
    m.toSyn (m.degree f) ≤ D := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨j, u, hu, rfl⟩ := hf
    calc m.toSyn (m.degree (monomial u (1 : k) * g j))
        ≤ m.toSyn (m.degree (monomial u (1 : k)) + m.degree (g j)) :=
          MonomialOrder.degree_mul_le
      _ = m.toSyn (m.degree (monomial u (1 : k))) + m.toSyn (m.degree (g j)) := map_add _ _ _
      _ ≤ m.toSyn u + m.toSyn (m.degree (g j)) :=
          add_le_add (MonomialOrder.degree_monomial_le 1) le_rfl
      _ = m.toSyn (u + m.degree (g j)) := (map_add _ _ _).symm
      _ ≤ D := hu
  | zero => rw [MonomialOrder.degree_zero, map_zero]; exact m.zero_le D
  | add f f' _ _ hf hf' => exact le_trans MonomialOrder.degree_add_le (max_le hf hf')
  | smul c f _ hf => exact le_trans MonomialOrder.degree_smul_le hf

theorem coeff_eq_zero_of_mem_lvlLT {δ : σ →₀ ℕ} {f : MvPolynomial σ k}
    (hf : f ∈ lvlLT m g (m.toSyn δ)) : f.coeff δ = 0 := by
  rcases hf with rfl | ⟨D', hD', hf⟩
  · simp
  · exact MonomialOrder.coeff_eq_zero_of_lt (lt_of_le_of_lt (degree_le_of_mem_lvl m g hf) hD')

/-- The product `X^(δ - m.degree (g j)) * g j`, of formal degree `δ` when
`m.degree (g j) ≤ δ`. -/
def tm (δ : σ →₀ ℕ) (j : γ) : MvPolynomial σ k := monomial (δ - m.degree (g j)) 1 * g j

theorem coeff_tm (hmon : ∀ j, m.Monic (g j)) {δ : σ →₀ ℕ} {j : γ}
    (h : m.degree (g j) ≤ δ) : (tm m g δ j).coeff δ = 1 := by
  rw [tm, coeff_monomial_mul', ite_eq_left tsub_le_self, tsub_tsub_cancel_of_le h, one_mul]
  exact (hmon j).coeff_degree

/-- Every element of `lvl m g (m.toSyn δ)` is an element of the lower level plus a
combination of the `tm m g δ j` with `m.degree (g j) ≤ δ`. -/
theorem exists_decomp [Fintype γ] [DecidableEq γ] {δ : σ →₀ ℕ} {f : MvPolynomial σ k}
    (hf : f ∈ lvl m g (m.toSyn δ)) :
    ∃ v ∈ lvlLT m g (m.toSyn δ), ∃ c : γ → k, (∀ j, ¬ m.degree (g j) ≤ δ → c j = 0) ∧
      f = v + ∑ j, c j • tm m g δ j := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨j, u, hu, rfl⟩ := hf
    rcases hu.lt_or_eq with hlt | heq
    · exact ⟨_, Or.inr ⟨_, hlt, monomial_mul_mem_lvl m g le_rfl (1 : k)⟩, 0, fun _ _ => rfl,
        by simp⟩
    · have hδ : u + m.degree (g j) = δ := m.toSyn.injective heq
      refine ⟨0, zero_mem _, Pi.single j 1, fun i hi => ?_, ?_⟩
      · have hij : i ≠ j := by
          rintro rfl
          exact hi (hδ ▸ le_add_self)
        simp [hij]
      · rw [zero_add, Fintype.sum_eq_single j (fun i hi => by simp [hi]),
          Pi.single_eq_same, one_smul, tm, ← hδ, add_tsub_cancel_right]
  | zero => exact ⟨0, zero_mem _, 0, fun _ _ => rfl, by simp⟩
  | add f f' _ _ hf hf' =>
    obtain ⟨v, hv, c, hc, rfl⟩ := hf
    obtain ⟨v', hv', c', hc', rfl⟩ := hf'
    refine ⟨v + v', add_mem hv hv', c + c', fun j hj => by simp [hc j hj, hc' j hj], ?_⟩
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
    abel
  | smul a f _ hf =>
    obtain ⟨v, hv, c, hc, rfl⟩ := hf
    refine ⟨a • v, Submodule.smul_mem _ a hv, a • c, fun j hj => by simp [hc j hj], ?_⟩
    simp only [Pi.smul_apply, smul_eq_mul, smul_add, Finset.smul_sum, smul_smul]

/-- Terms of a polynomial times a monomial, bounded by a bound on the polynomial. -/
theorem toSyn_lt_of_mem_support_monomial_mul {e : σ →₀ ℕ} {p : MvPolynomial σ k} {D : m.syn}
    (hp : ∀ w ∈ p.support, m.toSyn w < D) {u : σ →₀ ℕ}
    (hu : u ∈ (monomial e (1 : k) * p).support) : m.toSyn u < m.toSyn e + D := by
  rw [mem_support_iff, coeff_monomial_mul'] at hu
  split_ifs at hu with he
  · rw [one_mul] at hu
    have h := hp _ (mem_support_iff.2 hu)
    rw [← tsub_add_cancel_of_le he, map_add, add_comm (m.toSyn (u - e))]
    exact add_lt_add_of_le_of_lt le_rfl h
  · exact absurd rfl hu

/-- The support of the tail `g j - X^(m.degree (g j))` of a monic polynomial lies strictly
below its leading monomial. -/
theorem toSyn_lt_of_mem_support_tail (hmon : ∀ j, m.Monic (g j)) (j : γ) {u : σ →₀ ℕ}
    (hu : u ∈ (g j - monomial (m.degree (g j)) 1).support) :
    m.toSyn u < m.toSyn (m.degree (g j)) := by
  classical
  rw [mem_support_iff, coeff_sub, coeff_monomial] at hu
  by_cases h : m.degree (g j) = u
  · subst h
    rw [ite_eq_left rfl, (hmon j).coeff_degree, sub_self] at hu
    exact absurd rfl hu
  · rw [ite_eq_right h, sub_zero] at hu
    exact lt_of_le_of_ne (MonomialOrder.le_degree (mem_support_iff.2 hu))
      (fun h' => h (m.toSyn.injective h').symm)

/-- **Koszul syzygy.** For `j ≠ j'` with disjoint leading monomials dividing `δ`, the
difference `tm δ j - tm δ j'` lies strictly below level `δ`. -/
theorem tm_sub_tm_mem_lvlLT (hmon : ∀ j, m.Monic (g j))
    (hdisj : ∀ j j', j ≠ j' → ∀ v, m.degree (g j) v = 0 ∨ m.degree (g j') v = 0)
    {δ : σ →₀ ℕ} {j j' : γ} (hjj : j ≠ j') (hj : m.degree (g j) ≤ δ)
    (hj' : m.degree (g j') ≤ δ) : tm m g δ j - tm m g δ j' ∈ lvlLT m g (m.toSyn δ) := by
  have hsum : m.degree (g j) + m.degree (g j') ≤ δ := by
    rw [Finsupp.le_def] at hj hj' ⊢
    intro v
    rw [Finsupp.add_apply]
    rcases hdisj j j' hjj v with h | h
    · rw [h, zero_add]; exact hj' v
    · rw [h, add_zero]; exact hj v
  obtain ⟨e, rfl⟩ : ∃ e, δ = e + (m.degree (g j) + m.degree (g j')) :=
    ⟨_, (tsub_add_cancel_of_le hsum).symm⟩
  set d := m.degree (g j) with hd
  set d' := m.degree (g j') with hd'
  have h₁ : e + (d + d') - d = e + d' := by
    rw [add_comm d d', ← add_assoc, add_tsub_cancel_right]
  have h₂ : e + (d + d') - d' = e + d := by
    rw [← add_assoc, add_tsub_cancel_right]
  have key : tm m g (e + (d + d')) j - tm m g (e + (d + d')) j' =
      (monomial e (1 : k) * (g j - monomial d 1)) * g j' -
        (monomial e (1 : k) * (g j' - monomial d' 1)) * g j := by
    have hm₁ : monomial (e + d') (1 : k) = monomial e 1 * monomial d' 1 := by
      rw [monomial_mul_monomial, mul_one]
    have hm₂ : monomial (e + d) (1 : k) = monomial e 1 * monomial d 1 := by
      rw [monomial_mul_monomial, mul_one]
    rw [tm, tm, ← hd, ← hd', h₁, h₂, hm₁, hm₂]
    ring
  rw [key]
  refine sub_mem (mul_mem_lvlLT m g fun u hu => ?_) (mul_mem_lvlLT m g fun u hu => ?_)
  · have h := toSyn_lt_of_mem_support_monomial_mul m
      (fun w hw => toSyn_lt_of_mem_support_tail m g hmon j hw) hu
    rw [map_add, map_add, map_add, ← add_assoc]
    exact add_lt_add_of_lt_of_le h le_rfl
  · have h := toSyn_lt_of_mem_support_monomial_mul m
      (fun w hw => toSyn_lt_of_mem_support_tail m g hmon j' hw) hu
    rw [map_add, map_add, map_add, add_comm (m.toSyn d) (m.toSyn d'), ← add_assoc]
    exact add_lt_add_of_lt_of_le h le_rfl

/-- An element of level `δ` whose coefficient at `δ` vanishes lies strictly below level
`δ`. -/
theorem mem_lvlLT_of_coeff_eq_zero [Fintype γ] (hmon : ∀ j, m.Monic (g j))
    (hdisj : ∀ j j', j ≠ j' → ∀ v, m.degree (g j) v = 0 ∨ m.degree (g j') v = 0)
    {δ : σ →₀ ℕ} {f : MvPolynomial σ k} (hf : f ∈ lvl m g (m.toSyn δ)) (h0 : f.coeff δ = 0) :
    f ∈ lvlLT m g (m.toSyn δ) := by
  classical
  obtain ⟨v, hv, c, hc, rfl⟩ := exists_decomp m g hf
  have hcoeff : ∑ j, c j = 0 := by
    rw [AddMonoidAlgebra.coeff_add, Finsupp.add_apply, coeff_eq_zero_of_mem_lvlLT m g hv, zero_add, coeff_sum] at h0
    rw [← h0]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [coeff_smul, smul_eq_mul]
    by_cases hj : m.degree (g j) ≤ δ
    · rw [coeff_tm m g hmon hj, mul_one]
    · rw [hc j hj, zero_mul]
  refine add_mem hv ?_
  by_cases hS : ∃ j₀, m.degree (g j₀) ≤ δ
  · obtain ⟨j₀, hj₀⟩ := hS
    have : ∑ j, c j • tm m g δ j = ∑ j, c j • (tm m g δ j - tm m g δ j₀) := by
      simp only [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, hcoeff, zero_smul,
        sub_zero]
    rw [this]
    refine Submodule.sum_mem _ fun j _ => ?_
    by_cases hj : m.degree (g j) ≤ δ
    · refine Submodule.smul_mem _ _ ?_
      by_cases hjj : j = j₀
      · rw [hjj, sub_self]
        exact zero_mem _
      · exact tm_sub_tm_mem_lvlLT m g hmon hdisj hjj hj hj₀
    · rw [hc j hj, zero_smul]
      exact zero_mem _
  · rw [Finset.sum_eq_zero fun j _ => by rw [hc j fun h => hS ⟨j, h⟩, zero_smul]]
    exact zero_mem _

/-- Every element of `Ideal.span (Set.range g)` lies in some level. -/
theorem exists_mem_lvl [Fintype γ] {f : MvPolynomial σ k}
    (hf : f ∈ Ideal.span (Set.range g)) : ∃ D, f ∈ lvl m g D := by
  classical
  obtain ⟨h, rfl⟩ := Ideal.mem_span_range_iff_exists_fun.1 hf
  obtain ⟨D, hD⟩ := (Finset.univ.biUnion fun j =>
    (h j).support.image fun u => m.toSyn (u + m.degree (g j))).bddAbove
  refine ⟨D, Submodule.sum_mem _ fun j _ => mul_mem_lvl m g fun u hu => hD ?_⟩
  exact Finset.mem_coe.2 (Finset.mem_biUnion.2 ⟨j, Finset.mem_univ _, Finset.mem_image_of_mem _ hu⟩)

/-- **Buchberger's first criterion.** Monic generators with pairwise disjoint leading
monomials form a Gröbner basis: the leading monomial of every nonzero element of the ideal
is divisible by some leading monomial `m.degree (g j)`. -/
theorem exists_degree_le [Fintype γ] (hmon : ∀ j, m.Monic (g j))
    (hdisj : ∀ j j', j ≠ j' → ∀ v, m.degree (g j) v = 0 ∨ m.degree (g j') v = 0)
    {f : MvPolynomial σ k} (hf : f ∈ Ideal.span (Set.range g)) (hf0 : f ≠ 0) :
    ∃ j, m.degree (g j) ≤ m.degree f := by
  classical
  obtain ⟨D, hD⟩ := exists_mem_lvl m g hf
  clear hf
  induction D using WellFoundedLT.induction generalizing f with
  | _ D ih =>
  obtain ⟨δ, rfl⟩ := m.toSyn.surjective D
  by_cases hc : f.coeff δ = 0
  · rcases mem_lvlLT_of_coeff_eq_zero m g hmon hdisj hD hc with h | ⟨D', hD', hf'⟩
    · exact absurd h hf0
    · exact ih D' hD' hf0 hf'
  · have hdeg : m.degree f = δ := by
      apply m.toSyn.injective
      exact le_antisymm (degree_le_of_mem_lvl m g hD)
        (MonomialOrder.le_degree (mem_support_iff.2 hc))
    obtain ⟨v, hv, c, hc', hfe⟩ := exists_decomp m g hD
    by_contra hne
    push Not at hne
    apply hc
    rw [hfe, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, coeff_eq_zero_of_mem_lvlLT m g hv, zero_add, coeff_sum]
    refine Finset.sum_eq_zero fun j _ => ?_
    simp [hc' j (hdeg ▸ hne j)]

/-- **Radicality.** If moreover the leading monomials are squarefree, the ideal generated by
`g` is radical. -/
theorem isRadical [Fintype γ] (hmon : ∀ j, m.Monic (g j))
    (hdisj : ∀ j j', j ≠ j' → ∀ v, m.degree (g j) v = 0 ∨ m.degree (g j') v = 0)
    (hsq : ∀ j v, m.degree (g j) v ≤ 1) : (Ideal.span (Set.range g)).IsRadical := by
  intro f hf
  obtain ⟨N, hN⟩ := hf
  obtain ⟨c, r, hfr, -, hr⟩ := MonomialOrder.div (m := m) (b := g)
    (fun j => by rw [(hmon j).leadingCoeff_eq_one]; exact isUnit_one) f
  have hlin : Finsupp.linearCombination (MvPolynomial σ k) g c ∈ Ideal.span (Set.range g) := by
    show _ ∈ Submodule.span (MvPolynomial σ k) (Set.range g)
    rw [← Finsupp.range_linearCombination]
    exact LinearMap.mem_range_self _ c
  by_cases hr0 : r = 0
  · rw [hfr, hr0, add_zero]
    exact hlin
  exfalso
  have hrN : r ^ N ∈ Ideal.span (Set.range g) := by
    rw [← Ideal.Quotient.eq_zero_iff_mem] at hN ⊢
    have : Ideal.Quotient.mk (Ideal.span (Set.range g)) r =
        Ideal.Quotient.mk (Ideal.span (Set.range g)) f := by
      rw [hfr, map_add, Ideal.Quotient.eq_zero_iff_mem.2 hlin, zero_add]
    rw [map_pow, this, ← map_pow, hN]
  obtain ⟨j, hj⟩ := exists_degree_le m g hmon hdisj hrN (pow_ne_zero N hr0)
  rw [MonomialOrder.degree_pow] at hj
  have hle : m.degree (g j) ≤ m.degree r := by
    rw [Finsupp.le_def] at hj ⊢
    intro v
    have h₁ := hj v
    rw [Finsupp.smul_apply, smul_eq_mul] at h₁
    have h₂ := hsq j v
    rcases Nat.eq_zero_or_pos (m.degree r v) with h | h
    · rw [h, mul_zero] at h₁
      omega
    · omega
  exact hr _ (MonomialOrder.degree_mem_support hr0) j hle

end CoprimeGroebner

end Langlands.Archimedean.Kostant
