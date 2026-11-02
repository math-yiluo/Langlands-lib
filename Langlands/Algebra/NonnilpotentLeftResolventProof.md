# Renard B.III: a nonzero shift without a left inverse

`Langlands/Algebra/NonnilpotentLeftResolventProof.lean` proves the published
proposition `Langlands.Renard.NonnilpotentLeftResolventStatement`, from
`Langlands.Algebra.SeparationStatements`. The theorem is

```lean
theorem Langlands.Renard.nonnilpotentLeftResolvent (A : Type u) [Ring A] [Algebra ℂ A] :
    NonnilpotentLeftResolventStatement A
```

that is, for every unital associative complex algebra `A` in an arbitrary universe `u`,

```lean
Module.rank ℂ A ≤ Cardinal.aleph0 →
  ∀ a : A, ¬ IsNilpotent a →
    ∃ z : ℂ, z ≠ 0 ∧ ∀ b : A, b * (a - algebraMap ℂ A z) ≠ 1
```

The conclusion is one-sided: the shift `a - z` has no left inverse. The proof uses
no hypothesis beyond the statement's. `A` need not be commutative or nontrivial, and
no finite dimension, topology or algebraicity is assumed. The theorem has the single
universe parameter `u`, and its axioms are `propext`, `Classical.choice` and
`Quot.sound`.

## Source

David Renard, *Représentations des groupes réductifs p-adiques*, French edition dated
9 July 2026, registered as `renard-2026-representations-groupes-reductifs-padiques`
(SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`). The
relevant passages are B.I (Amitsur's theorem and its proof, printed pages 271–272 /
PDF pages 277–278) and the second sentence of the proof of the Lemme in B.III (printed
page 273 / PDF page 279): "Comme *a* est non nilpotent, d'après le théorème d'Amitsur
B.I et sa démonstration, il existe λ ∈ ℂ^× tel que *a* − λ1_*A* soit non inversible à
gauche."

The 2010-edition list *corrections et compléments*
(`renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`), PDF page 19,
corrects the 2010 version of this sentence (p. 315, l. 11) to exactly the 2026
wording: the shift is only claimed to have no left inverse, and the earlier claim that
it is a right zero divisor is removed. The Library has no errata note for the 2026
edition.

## How the source argument is adapted

B.I proves that Spec(*a*) = {0} forces *a* to be nilpotent, where Spec uses two-sided
inverses. If every *a* − λ1_*A* with λ ≠ 0 is invertible, then the uncountable family of
inverses (*a* − λ1_*A*)⁻¹, λ ∈ ℂ^×, is linearly dependent because the dimension is
countable. Multiplying a dependence relation by the product of the factors
*a* − λ_*i*1_*A* gives a nonconstant polynomial *P* with *P*(*a*) = 0. Writing
*P*(*t*) = *c t*^*n* (*t* − α_1) ⋯ (*t* − α_*r*) with α_*j* ≠ 0 and cancelling the
invertible factors gives *a*^*n* = 0.

B.III needs this argument with left inverses only. The proof below runs it so, by
contradiction from the assumption that every *a* − *z* with *z* ≠ 0 has a left
inverse. Each step uses the left inverses on the correct side:

- In a dependence relation Σ μ_*i* *b*_*i* = 0 the product N(*a*) = Π (*a* − λ_*j*) is
  multiplied **on the right**, since *b*_*i* (*a* − λ_*i*) = 1 only for multiplication
  on the left of *a* − λ_*i*. The factors are polynomials in *a*, so the factor
  *a* − λ_*i* can be placed first.
- The factors *a* − α_*j* of *P*(*a*) are cancelled by multiplying **on the left** by
  their left inverses.

The Lean proof organizes the dependence argument as its contrapositive. Either *a* is
algebraic, and the cancellation argument applies, or *a* is transcendental, and then
the left inverses are linearly independent. The second case contradicts countable
dimension. In the source a dependence relation produces the polynomial *P*. Here
transcendence plays that role: the polynomial built from a relation must be zero, and
evaluating it at the nodes kills the coefficients. The source also states that *P* is
nonconstant. The Lean proof does not need this, because a nonzero constant *c* with
*a*^*m* · *c* = 0 already gives *a*^*m* = 0. This also covers the zero algebra.

## Declarations

All declarations are theorems in namespace `Langlands.Renard`.

### `isNilpotent_of_leftInverse_of_aeval_eq_zero`

```lean
theorem isNilpotent_of_leftInverse_of_aeval_eq_zero {A : Type u} [Ring A] [Algebra ℂ A]
    {a : A} (hleft : ∀ z : ℂ, z ≠ 0 → ∃ b : A, b * (a - algebraMap ℂ A z) = 1) :
    ∀ (n : ℕ) (q : ℂ[X]), q.natDegree ≤ n → q ≠ 0 → ∀ m : ℕ,
      aeval a (X ^ m * q) = 0 → IsNilpotent a
```

If every nonzero shift of `a` has a left inverse, then a nonzero polynomial `q` with
`a ^ m * q(a) = 0` forces `a` to be nilpotent. This is the cancellation step of B.I.
The proof is by induction on the degree bound `n`, for all `q` and `m`.

- `n = 0`: `q = C c` with `c ≠ 0` (`eq_C_of_natDegree_le_zero`). Then
  `aeval a (X ^ m * C c) = c • a ^ m`, so `a ^ m = 0` by `smul_eq_zero`.
- `n + 1`: if `q.natDegree ≤ n`, the induction hypothesis applies. Otherwise `q` has
  positive degree, so it has a root `w` (`IsAlgClosed.exists_root`). Then
  `q = (X - C w) * q'` with `q' = q /ₘ (X - C w)` (`mul_divByMonic_eq_iff_isRoot`),
  `q' ≠ 0`, and `q'.natDegree ≤ n` (`natDegree_divByMonic`).
  - If `w = 0`, then `X ^ m * (X * q') = X ^ (m + 1) * q'`, and the induction
    hypothesis applies with `m + 1`.
  - If `w ≠ 0`, let `b` be a left inverse of `a - algebraMap ℂ A w`. In the
    commutative ring `ℂ[X]`, `X ^ m * ((X - C w) * q') = (X - C w) * (X ^ m * q')`, so
    `(a - algebraMap ℂ A w) * aeval a (X ^ m * q') = 0`. Multiplying on the left by `b`
    gives `aeval a (X ^ m * q') = 0`, and the induction hypothesis applies with `m`.

Because the power `X ^ m` and `q` are kept in one polynomial, every commutation
happens in `ℂ[X]` before `aeval` is applied. No commutativity in `A` is used.

### `linearIndependent_of_leftInverse_of_transcendental`

```lean
theorem linearIndependent_of_leftInverse_of_transcendental {A : Type u} [Ring A]
    [Algebra ℂ A] {a : A} (ha : Transcendental ℂ a) {s : Set ℂ} (b : s → A)
    (hb : ∀ z : s, b z * (a - algebraMap ℂ A z) = 1) : LinearIndependent ℂ b
```

If `a` is transcendental over `ℂ`, then any family of left inverses `b z` of the shifts
`a - z`, for `z` in a set `s ⊆ ℂ`, is linearly independent. By
`linearIndependent_iff'`, take a finite set `t ⊆ s` and coefficients `g` with
`∑ i ∈ t, g i • b i = 0`, and fix `k ∈ t`.

- Let `N = ∏ j ∈ t, (X - C j)` and `P i = ∏ j ∈ t.erase i, (X - C j)`. For `i ∈ t`,
  `Finset.mul_prod_erase` gives `N = (X - C i) * P i`, so
  `b i * N(a) = b i * (a - algebraMap ℂ A i) * (P i)(a) = (P i)(a)`.
- Multiplying the relation on the right by `N(a)` gives
  `aeval a (∑ i ∈ t, g i • P i) = 0`. Since `a` is transcendental, the polynomial
  `∑ i ∈ t, g i • P i` is zero.
- Evaluating at `k`: for `i ≠ k` the product `P i` contains the factor `X - C k`, so
  `eval k (P i) = 0`. The sum reduces to `g k * ∏ j ∈ t.erase k, (k - j)`. Each factor
  is nonzero, because `j ≠ k` in `s` means `(j : ℂ) ≠ k`. Hence `g k = 0`.

### `nonnilpotentLeftResolvent`

The main theorem. Assume `Module.rank ℂ A ≤ ℵ₀` and that `a` is not nilpotent, and
suppose, for a contradiction, that every `a - algebraMap ℂ A z` with `z ≠ 0` has a left
inverse.

- If `a` is algebraic, take `q ≠ 0` with `aeval a q = 0`. Then
  `isNilpotent_of_leftInverse_of_aeval_eq_zero` with `n = q.natDegree` and `m = 0`
  makes `a` nilpotent, a contradiction.
- Otherwise `a` is transcendental. Choose left inverses `b z` for `z` in
  `s = {z : ℂ | z ≠ 0}`. By `linearIndependent_of_leftInverse_of_transcendental` they
  are linearly independent, so `LinearIndependent.cardinal_lift_le_rank` gives
  `Cardinal.lift.{u} #s ≤ Cardinal.lift.{0} (Module.rank ℂ A) ≤ ℵ₀`. Hence `s` is
  countable (`Cardinal.lift_le_aleph0`, `Cardinal.le_aleph0_iff_set_countable`). Then
  `Set.univ ⊆ insert 0 s` is countable, contradicting `not_countable_complex`.

The universe lift is the only place where the carrier universe `u` appears: the
index set lives in `Type`, and the cardinal comparison is made after lifting.

## Scope

This module proves only the one-sided resolvent assertion. The principal-left-ideal
equivalence, the simple-quotient step, the unital separation lemma, the B.I
statements and the nonunital reductions of the source are separate obligations and
are not proved here.

## Provenance and credit

Worker 972 wrote this module and this note. The proof is the argument of the proof of
B.I, run with left inverses as B.III requires. The informal route recorded in
`Langlands/Algebra/SeparationStatements.md` (Worker 221 and Worker 6) describes the same
source argument. The Lean proof here was written independently of it and of the
private division-algebra argument in `Langlands.Representation.Schur.CountableDimensionProof`.
No code was taken from either.

## Checks

In Lean environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f` the module compiles with no
errors or warnings. Inspection of `Langlands.Renard.nonnilpotentLeftResolvent` reports
the level parameter `u` and the axioms `propext`, `Classical.choice` and `Quot.sound`. A
private check confirmed that `@Langlands.Renard.nonnilpotentLeftResolvent` has type
`∀ (A : Type u) [Ring A] [Algebra ℂ A], NonnilpotentLeftResolventStatement.{u} A`.
