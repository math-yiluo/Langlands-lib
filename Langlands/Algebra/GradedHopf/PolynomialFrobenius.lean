import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.RingTheory.MvPolynomial.Expand
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Algebra.Field.Subfield.Basic

/-! # Polynomials with vanishing partial derivatives -/

noncomputable section

open MvPolynomial

namespace Langlands.Algebra.GradedHopf

variable {σ k : Type*} [Field k]

/-- If all partial derivatives of `F` vanish, then every exponent of every monomial of `F`
vanishes in `k`. -/
theorem cast_eq_zero_of_pderiv_eq_zero {F : MvPolynomial σ k} (hF : ∀ i, pderiv i F = 0)
    {m : σ →₀ ℕ} (hm : m ∈ F.support) (i : σ) : (m i : k) = 0 := by
  classical
  by_cases h0 : m i = 0
  · simp [h0]
  have hle : Finsupp.single i 1 ≤ m := Finsupp.single_le_iff.2 (Nat.one_le_iff_ne_zero.2 h0)
  set m' := m - Finsupp.single i 1 with hm'def
  have hm' : m' + Finsupp.single i 1 = m := tsub_add_cancel_of_le hle
  have hmi : m i = m' i + 1 := by
    rw [← hm', Finsupp.add_apply, Finsupp.single_eq_same]
  have h : F.coeff (m' + Finsupp.single i 1) * ((m' i : k) + 1) = 0 := by
    rw [← coeff_pderiv, hF i]
    simp
  rw [hm'] at h
  have hc : F.coeff m ≠ 0 := mem_support_iff.1 hm
  rw [hmi, Nat.cast_add, Nat.cast_one]
  exact (mul_eq_zero.1 h).resolve_left hc

/-- In characteristic zero, a polynomial all of whose partial derivatives vanish is
constant. -/
theorem eq_C_of_pderiv_eq_zero [CharZero k] {F : MvPolynomial σ k} (hF : ∀ i, pderiv i F = 0) :
    F = C (F.coeff 0) := by
  classical
  ext m
  rw [coeff_C]
  split_ifs with h
  · rw [h]
  · by_contra hc
    obtain ⟨i, hi⟩ : ∃ i, m i ≠ 0 := by
      by_contra h'
      push Not at h'
      exact h (Finsupp.ext fun i => (h' i).symm)
    exact hi (Nat.cast_eq_zero.1 (cast_eq_zero_of_pderiv_eq_zero hF (mem_support_iff.2 hc) i))

/-- In characteristic `p`, a polynomial all of whose partial derivatives vanish is a polynomial
in the `p`-th powers of the variables. -/
theorem exists_expand_of_pderiv_eq_zero (p : ℕ) [Fact p.Prime] [CharP k p]
    {F : MvPolynomial σ k} (hF : ∀ i, pderiv i F = 0) :
    ∃ H : MvPolynomial σ k, F = expand p H := by
  classical
  have hdvd : ∀ m ∈ F.support, ∀ i, p ∣ m i := fun m hm i =>
    (CharP.cast_eq_zero_iff k p _).1 (cast_eq_zero_of_pderiv_eq_zero hF hm i)
  let d : (σ →₀ ℕ) → (σ →₀ ℕ) := fun m => Finsupp.mapRange (fun n => n / p) (Nat.zero_div p) m
  have hd : ∀ m ∈ F.support, p • d m = m := fun m hm => by
    ext i
    simp [d, Nat.mul_div_cancel' (hdvd m hm i)]
  refine ⟨∑ m ∈ F.support, monomial (d m) (F.coeff m), ?_⟩
  rw [map_sum]
  conv_lhs => rw [F.as_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [expand_monomial, hd m hm]

variable (p : ℕ) [Fact p.Prime] [CharP k p]

/-- A family `b` in `k` is `p`-independent if it is linearly independent over the subfield of
`p`-th powers: `∑ⱼ bⱼ cⱼ ^ p = 0` forces all `cⱼ = 0`. -/
def PIndependent {r : ℕ} (b : Fin r → k) : Prop :=
  ∀ c : Fin r → k, ∑ j, b j * c j ^ p = 0 → ∀ j, c j = 0

/-- Every polynomial is a combination `∑ⱼ bⱼ • Gⱼ⁽ᵖ⁾`, with `p`-independent coefficients `bⱼ`,
of polynomials `Gⱼ` with support in that of `H`, where `G⁽ᵖ⁾` raises all coefficients of `G`
to the `p`-th power. -/
theorem exists_pIndependent_decomposition (H : MvPolynomial σ k) :
    ∃ (r : ℕ) (b : Fin r → k) (G : Fin r → MvPolynomial σ k), PIndependent p b ∧
      H = ∑ j, b j • (G j).map (frobenius k p) ∧ ∀ j, (G j).support ⊆ H.support := by
  classical
  let K : Subfield k := (frobenius k p).fieldRange
  let V : Submodule K k := Submodule.span K (Set.range fun m : H.support => H.coeff m)
  have : FiniteDimensional K V := FiniteDimensional.span_of_finite K (Set.finite_range _)
  let B := Module.finBasis K V
  have hmem : ∀ m ∈ H.support, H.coeff m ∈ V := fun m hm =>
    Submodule.subset_span ⟨⟨m, hm⟩, rfl⟩
  have hrepr : ∀ m (hm : m ∈ H.support),
      ∑ j, ((B.repr ⟨H.coeff m, hmem m hm⟩ j : K) : k) * (B j : k) = H.coeff m := by
    intro m hm
    have := congrArg (fun v : V => (v : k)) (B.sum_repr ⟨H.coeff m, hmem m hm⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at this
    exact Eq.trans (Finset.sum_congr rfl fun j _ => rfl) this
  have hK : ∀ x : K, ∃ y : k, y ^ p = x := fun x => by
    obtain ⟨y, hy⟩ := x.2
    exact ⟨y, by rw [← hy]; rfl⟩
  choose γ hγ using fun (m : H.support) (j : Fin (Module.finrank K V)) =>
    hK (B.repr ⟨H.coeff m, hmem m m.2⟩ j)
  refine ⟨Module.finrank K V, fun j => (B j : k),
    fun j => ∑ m : H.support, monomial (m : σ →₀ ℕ) (γ m j), ?_, ?_, ?_⟩
  · intro c hc j
    have hli := B.linearIndependent
    rw [Fintype.linearIndependent_iff] at hli
    have h0 : ∑ i, (⟨c i ^ p, ⟨c i, rfl⟩⟩ : K) • B i = 0 := by
      apply Subtype.ext
      simp only [Submodule.coe_sum, Submodule.coe_smul, Submodule.coe_zero]
      rw [← hc]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [mul_comm]
      rfl
    have := hli _ h0 j
    have h1 : c j ^ p = 0 := congrArg Subtype.val this
    exact (pow_eq_zero_iff (Fact.out : p.Prime).ne_zero).1 h1
  · ext m
    simp only [coeff_sum, coeff_smul, coeff_map, smul_eq_mul]
    by_cases hm : m ∈ H.support
    · rw [← hrepr m hm]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [mul_comm]
      congr 1
      rw [← hγ ⟨m, hm⟩ j, Finset.sum_eq_single ⟨m, hm⟩]
      · simp [coeff_monomial, frobenius_def]
      · intro m' _ hne
        rw [coeff_monomial, ite_eq_right_iff.2 (fun h : (m' : σ →₀ ℕ) = m =>
          absurd (Subtype.ext h) hne)]
      · intro h
        exact absurd (Finset.mem_univ _) h
    · rw [notMem_support_iff.1 hm]
      symm
      refine Finset.sum_eq_zero fun j _ => ?_
      refine mul_eq_zero_of_right _ ?_
      rw [Finset.sum_eq_zero fun m' _ => ?_, map_zero]
      rw [coeff_monomial, ite_eq_right_iff.2 (fun h : (m' : σ →₀ ℕ) = m =>
        absurd (h ▸ m'.2) hm)]
  · intro j m hm
    rw [mem_support_iff, coeff_sum] at hm
    obtain ⟨m', -, hm'⟩ := Finset.exists_ne_zero_of_sum_ne_zero hm
    rw [coeff_monomial] at hm'
    split_ifs at hm' with h
    · exact h ▸ m'.2
    · exact absurd rfl hm'

/-- If `b` is `p`-independent and `∑ⱼ bⱼ • hⱼ ^ p = 0` in a polynomial ring, then all `hⱼ`
vanish. -/
theorem eq_zero_of_sum_smul_pow_eq_zero {τ : Type*} {r : ℕ} {b : Fin r → k}
    (hb : PIndependent p b) {h : Fin r → MvPolynomial τ k} (hh : ∑ j, b j • h j ^ p = 0) :
    ∀ j, h j = 0 := by
  have hp0 : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  have key : ∀ m, ∑ j, b j * (h j).coeff m ^ p = 0 := by
    intro m
    have := congrArg (fun F : MvPolynomial τ k => F.coeff (p • m)) hh
    simp only [coeff_sum, coeff_smul, smul_eq_mul] at this
    calc ∑ j, b j * (h j).coeff m ^ p = ∑ j, b j * (h j ^ p).coeff (p • m) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [← map_frobenius_expand p, coeff_map, coeff_expand_smul p hp0, frobenius_def]
      _ = 0 := by rw [this]; simp
  intro j
  ext m
  simpa using hb (fun j => (h j).coeff m) (key m) j

end Langlands.Algebra.GradedHopf
