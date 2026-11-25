/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.RingTheory.Valuation.ResiduallyIndependentRadicals
public import WeilConjectures.FieldTheory.AdjoinSimplePow
public import Mathlib.FieldTheory.PurelyInseparable.Tower

/-!
# `p`-independence is preserved by separable extensions of a rational function field

Let `k → Q` be fields of characteristic `p`, `x ∈ Q` transcendental over `k`, and `b` a
`p`-independent family of `k`. Then the monomials `∏ b i ^ E i` (`0 ≤ E i < p`) stay linearly
independent over the `p`-th powers of elements of `Q` separable over `k⟮x⟯`
(`Field.PowIndependent.eq_zero_of_isSeparable`). In particular, `b` stays `p`-independent in any
extension of `k` which is separable algebraic over `k⟮x⟯`
(`Field.PowIndependent.map_of_isSeparable`).

Proof: the monomials are linearly independent over `k⟮x⟯ ^ p = k ^ p ⟮x ^ p⟯` (expand in powers of
the transcendental `x ^ p`), and the extension `k⟮x⟯ / k⟮x⟯ ^ p` is purely inseparable while the
`p`-th powers of separable elements are separable over `k⟮x⟯ ^ p`; separable and purely
inseparable extensions are linearly disjoint
(`IntermediateField.linearDisjoint_of_isPurelyInseparable_of_isSeparable`).
-/

@[expose] public section

open IntermediateField Polynomial

namespace Field

variable {k Q : Type*} [Field k] [Field Q] [Algebra k Q] (p : ℕ) [Fact p.Prime] [CharP Q p]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **`p`-independence over `k⟮x⟯ ^ p`.** The monomials in a `p`-independent family of `k` are
linearly independent over the `p`-th powers of `k⟮x⟯` when `x` is transcendental over `k`. -/
theorem PowIndependent.eq_zero_of_mem_adjoin {x : Q} (hx : Transcendental k x) {b : ι → k}
    (hb : PowIndependent p b) (m : (ι → Fin p) → Q) (hm : ∀ E, m E ∈ k⟮x⟯)
    (h : ∑ E, m E ^ p * ∏ i, algebraMap k Q (b i) ^ (E i : ℕ) = 0) : ∀ E, m E = 0 := by
  classical
  have hp := (Fact.out : p.Prime)
  have : CharP k p := (algebraMap k Q).charP (algebraMap k Q).injective p
  choose r s hs hrs using fun E ↦ exists_mul_aeval_eq_aeval_of_mem_adjoin_simple (hm E)
  let f : (ι → Fin p) → k[X] := fun E ↦ r E * ∏ E' ∈ Finset.univ.erase E, s E'
  have hD : aeval x (∏ E', s E') ≠ 0 := by
    rw [map_prod]
    exact Finset.prod_ne_zero_iff.2 fun E _ ↦ hs E
  have hf (E : ι → Fin p) : m E * aeval x (∏ E', s E') = aeval x (f E) := by
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ E), map_mul, ← mul_assoc, hrs, map_mul]
  have hP : ∑ E, f E ^ p * C (∏ i, b i ^ (E i : ℕ)) = 0 := by
    refine transcendental_iff.1 hx _ ?_
    have h' := congr(($h) * aeval x (∏ E', s E') ^ p)
    rw [zero_mul, Finset.sum_mul] at h'
    rw [map_sum, ← h']
    refine Finset.sum_congr rfl fun E _ ↦ ?_
    rw [map_mul, map_pow, ← hf, aeval_C]
    simp only [map_prod (algebraMap k Q), map_pow]
    ring
  have hcoeff (n : ℕ) (E : ι → Fin p) : (f E).coeff n = 0 := by
    refine hb (fun E ↦ (f E).coeff n) ?_ E
    have h' := congr(($hP).coeff (p * n))
    rw [finsetSum_coeff, coeff_zero] at h'
    rw [← h']
    refine Finset.sum_congr rfl fun E _ ↦ ?_
    rw [coeff_mul_C, ← map_frobenius_expand p, coeff_map, coeff_expand_mul' hp.pos, frobenius_def]
  intro E
  have h' := hf E
  have hfE : f E = 0 := Polynomial.ext fun n ↦ by rw [hcoeff n E, coeff_zero]
  rw [hfE, map_zero] at h'
  exact (mul_eq_zero.1 h').resolve_right hD

/-- **`p`-independence over separable elements.** -/
theorem PowIndependent.eq_zero_of_isSeparable {x : Q} (hx : Transcendental k x) {b : ι → k}
    (hb : PowIndependent p b) (g : (ι → Fin p) → Q) (hg : ∀ E, IsSeparable k⟮x⟯ (g E))
    (h : ∑ E, g E ^ p * ∏ i, algebraMap k Q (b i) ^ (E i : ℕ) = 0) : ∀ E, g E = 0 := by
  classical
  have hp := (Fact.out : p.Prime)
  -- `F₀ = k⟮x⟯ ^ p` and `M' = k⟮x⟯` as an extension of `F₀`
  let F₀ : Subfield Q := (k⟮x⟯).toSubfield.map (frobenius Q p)
  have : CharP F₀ p := (algebraMap F₀ Q).charP (algebraMap F₀ Q).injective p
  have hF₀ (c : F₀) : (c : Q) ∈ k⟮x⟯ := by
    obtain ⟨m, hm, hc⟩ := Subfield.mem_map.1 c.2
    rw [← hc, frobenius_def]
    exact pow_mem hm p
  let M' : IntermediateField F₀ Q := (k⟮x⟯).toSubfield.toIntermediateField hF₀
  have : IsPurelyInseparable F₀ M' := by
    refine (isPurelyInseparable_iff_pow_mem F₀ p).2 fun y ↦ ⟨1, ?_⟩
    rw [pow_one]
    refine ⟨⟨y ^ p, Subfield.mem_map.2 ⟨y, y.2, by rw [frobenius_def]⟩⟩, ?_⟩
    ext
    rfl
  -- the Frobenius `k⟮x⟯ → F₀`
  let φ : k⟮x⟯ →+* F₀ := ((frobenius Q p).comp (algebraMap k⟮x⟯ Q)).codRestrict F₀
    fun m ↦ Subfield.mem_map.2 ⟨m, m.2, rfl⟩
  have hsep (E : ι → Fin p) : g E ^ p ∈ separableClosure F₀ Q := by
    refine (Polynomial.Separable.map (hg E) (f := φ)).of_dvd (minpoly.dvd F₀ _ ?_)
    have h' := hom_eval₂ (minpoly k⟮x⟯ (g E)) (algebraMap k⟮x⟯ Q) (frobenius Q p) (g E)
    rw [← aeval_def, minpoly.aeval, map_zero, frobenius_def] at h'
    rw [aeval_def, eval₂_map, h']
    rfl
  -- the monomials, as elements of `M'`
  let v : (ι → Fin p) → M' := fun E ↦
    ⟨∏ i, algebraMap k Q (b i) ^ (E i : ℕ), prod_mem fun i _ ↦ pow_mem
      (IntermediateField.algebraMap_mem k⟮x⟯ (b i)) _⟩
  have hv : LinearIndependent F₀ v := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    choose m hm hmc using fun E ↦ Subfield.mem_map.1 (c E).2
    have hm0 := hb.eq_zero_of_mem_adjoin p hx m hm ?_
    · intro E
      ext
      simp [← hmc, hm0 E]
    · have h' := congrArg (algebraMap M' Q) hc
      simp only [frobenius_def] at hmc
      simpa [map_sum, Algebra.smul_def, hmc, v, Subfield.algebraMap_ofSubfield] using h'
  have hli := ((separableClosure F₀ Q).linearDisjoint_of_isPurelyInseparable_of_isSeparable
    M').linearIndependent_right' hv
  rw [Fintype.linearIndependent_iff] at hli
  intro E
  have h' := hli (fun E ↦ ⟨g E ^ p, hsep E⟩) ?_ E
  · exact (pow_eq_zero_iff hp.ne_zero).1 congr(($h').1)
  · simpa [Algebra.smul_def, v] using h

/-- **`p`-independence is preserved by extensions separable over a rational function field.** -/
theorem PowIndependent.map_of_isSeparable {x : Q} (hx : Transcendental k x)
    (hsep : ∀ y : Q, IsSeparable k⟮x⟯ y) {b : ι → k} (hb : PowIndependent p b) :
    PowIndependent p fun i ↦ algebraMap k Q (b i) :=
  fun g h ↦ hb.eq_zero_of_isSeparable p hx g (fun E ↦ hsep (g E)) h

end Field
