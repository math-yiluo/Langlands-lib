# An irreducibility criterion for integer polynomials (helper for Tadić's Proposition 3.8)

Author: Worker 4021. Module
`Langlands.Representation.Classification.TadicRectanglePrimeAlgebra`, namespace
`Langlands.Classification.TadicRectanglePrime`. It is a helper module of the proof
`Langlands.Classification.TadicRectanglePrime.tadicRectangleSoclePrime` of
`Langlands.Classification.TadicRectangleSoclePrime` (module
`TadicRectangleSoclePrimeProof`). It imports only Mathlib, contains only theorems and one
auxiliary ring homomorphism, and uses only the axioms `propext`, `Classical.choice` and
`Quot.sound`.

## Provenance

This is pure commutative algebra, abstracted from the degree argument in Tadić's proof of
Proposition 3.8 (M. Tadić, *Classification of unitary representations in irreducible
representations of general linear group (non-Archimedean case)*, Ann. Sci. ÉNS (4) 19
(1986), literature ID `tadic-1986-unitary`, printed pp.354–356, PDF pp.21–23). There
Tadić writes `⟨a(n,d)^ρ⟩ = P₁ × P₂` with homogeneous factors of positive degree. He splits
the leading monomial `⟨Δ_1⟩ × ⋯ × ⟨Δ_n⟩` between the factors, finds a consecutive pair
`Δ_k, Δ_(k+1)` separated by the split, and studies how the factors share the monomial in
which `Δ_k, Δ_(k+1)` are replaced by their union and intersection. A degree count then
gives a contradiction. Neither the criterion below nor the homogeneity lemma is stated in
the source; they are the internal algebraic core of the proof, stated for an arbitrary
variable type `σ` and arbitrary positive weights. The way the contradiction is reached
differs from Tadić's (see `irreducible_of_adjacent` below).

## Factors of weighted homogeneous polynomials

Section `Weighted`, for a commutative ring `R`, a variable type `σ` and weights
`w : σ → ℕ`. Mathlib's `Finsupp.weight w μ = ∑ μ i * w i` is the weight of the monomial
`μ`, and `MvPolynomial.IsWeightedHomogeneous w φ W` says that every monomial of `φ` with
nonzero coefficient has weight `W`.

- `weightSubst w : MvPolynomial σ R →+* Polynomial (MvPolynomial σ R)` substitutes
  `X_i ↦ t^(w i) X_i` (Mathlib's `eval₂Hom`, constants `c ↦ C (C c)`).
- `weightSubst_monomial_one`, `weightSubst_monomial`: the monomial `c X^μ` goes to
  `t^(weight w μ) · c X^μ`. Induction on `μ` (`Finsupp.induction`).
- `coeff_coeff_weightSubst`: the coefficient of `X^ν` in the coefficient of `t^k` of
  `weightSubst w φ` is `φ.coeff ν` if `weight w ν = k` and `0` otherwise. Induction on `φ`
  (`MvPolynomial.induction_on'`). So the coefficient of `t^k` is the weight-`k` component
  of `φ`.
- `coeff_weightSubst_ne_zero`, `weightSubst_ne_zero`: if `φ.coeff μ ≠ 0`, then the
  coefficient of `t^(weight w μ)` of `weightSubst w φ` is nonzero; in particular
  `φ ≠ 0` gives `weightSubst w φ ≠ 0`.
- `isWeightedHomogeneous_left_of_mul`: over a domain `R`, if `P₁ * P₂` is weighted
  homogeneous of some weight `W` and `P₁, P₂ ≠ 0`, then `P₁` is weighted homogeneous (of
  weight `natDegree (weightSubst w P₁)`). Proof: `weightSubst w (P₁ * P₂)` has only
  the coefficient of `t^W`, so its `natDegree` is at most `W` and its
  `natTrailingDegree` is at least `W`. `MvPolynomial σ R` is a domain, so both degrees
  are additive (`Polynomial.natDegree_mul`, `Polynomial.natTrailingDegree_mul`). With
  `natTrailingDegree ≤ natDegree` for each factor, the two degrees of
  `weightSubst w P₁` coincide. Every monomial `ν` of `P₁` has weight between them, so
  equal to `natDegree (weightSubst w P₁)`.

## The irreducibility criterion

Section `Criterion`. Throughout, `s : ℕ → σ` lists variables and `n : ℕ` is their number.

- `exists_split_of_coeff_mul_ne_zero`: if `(P₁ * P₂).coeff μ ≠ 0`, then `μ = β + γ`
  with `P₁.coeff β ≠ 0` and `P₂.coeff γ ≠ 0` (Mathlib's `coeff_mul` over the
  antidiagonal).
- `sum_single_apply_of_mem`, `sum_single_apply_of_not_mem`, `weight_sum_single`: for
  `t ⊆ {0, …, n-1}` and `s` injective on `{0, …, n-1}`, the monomial
  `∑ i ∈ t, single (s i) 1` has exponent `1` at `s j` for `j ∈ t`, `0` at `s j` for
  `j ∉ t`, and `0` at variables outside the image of `s`. If `w (s j) = D` for
  `j < n`, its weight is `card t * D`.

### `irreducible_of_adjacent`

Hypotheses: positive weights `w` (`hw`); `Q : MvPolynomial σ ℤ` weighted homogeneous of
some weight `W` (`hQ`); `0 < n`; `s` injective on `{0, …, n-1}` (`hs`); `w (s j) = D` for
`j < n` (`hD`); and

- `h0`: the monomial `e₀ = X_{s 0} ⋯ X_{s (n-1)}` has coefficient `1` in `Q`;
- `h1`: every monomial of `Q` has exponent at most `1` at every `s j`, `j < n`;
- `h2`: for every `k` with `k + 1 < n` there is a monomial `μ` of `Q` (nonzero
  coefficient) with `μ (s k) = μ (s (k+1)) = 0`, `μ (s j) = 1` for every other `j < n`,
  and such that no `ν ≤ μ` with `ν (s j) = 0` for all `j < n` has weight `D`.

Conclusion: `Irreducible Q`.

Proof as implemented. By `h0` and `h1`, `Q ≠ 0` and `degreeOf (s j) Q = 1` for `j < n`.

The core is the statement `key`, for a factorization `Q = P₁ * P₂`:
both factors are nonzero, and `degreeOf_mul_eq` gives
`degreeOf (s j) P₁ + degreeOf (s j) P₂ = 1` for `j < n`. By
`isWeightedHomogeneous_left_of_mul`, `P₁` is weighted homogeneous of some weight `W₁`.
Let `p = {j < n | degreeOf (s j) P₁ = 1}`. Split `e₀ = β + γ` by
`exists_split_of_coeff_mul_ne_zero`. Since `β (s j) ≤ degreeOf (s j) P₁`,
`γ (s j) ≤ degreeOf (s j) P₂` and `β (s j) + γ (s j) = 1`, the monomial `β` is
`∑ j ∈ p, single (s j) 1`, so `W₁ = card p * D`. Then:

1. If `degreeOf (s j) P₁ = 0` for all `j < n`, then `p = ∅` and `W₁ = 0`. Since all
   weights are positive, the only monomial of weight `0` is `0`, so `P₁ = C c` is a
   constant. From `c * P₂.coeff e₀ = Q.coeff e₀ = 1`, `c` is a unit of `ℤ`, so `P₁` is a
   unit.
2. It is impossible that `degreeOf (s k) P₁ = 1` and `degreeOf (s (k+1)) P₁ = 0` for
   some `k + 1 < n`. Take `μ` from `h2` and split `μ = β' + γ'` with nonzero
   coefficients in `P₁` and `P₂`. As for `e₀`, the exponents of `β'` at the `s j` are
   `1` exactly for `j ∈ p \ {k}` (the exponent of `μ` is `0` at `s k` and `s (k+1)`,
   and `k + 1 ∉ p`). So `E = ∑ j ∈ p.erase k, single (s j) 1 ≤ β'`, and
   `ν = β' - E` satisfies `ν ≤ μ` and `ν (s j) = 0` for all `j < n`. By weighted
   homogeneity of `P₁`, `W₁ = weight β' = weight ν + (card p - 1) * D`. With
   `W₁ = card p * D` and `k ∈ p` this gives `weight ν = D`, contradicting `h2`.

Now `Q` is not a unit: `Q * Q' = 1` would give `degreeOf (s 0)` equal to `1 + …` on one
side and `0` on the other. Let `Q = P₁ * P₂`. If all `degreeOf (s j) P₁` are `0`,
`P₁` is a unit by 1. If all are `1`, all `degreeOf (s j) P₂` are `0`, and `P₂` is a unit
by 1 applied to `Q = P₂ * P₁`. Otherwise the `{0,1}`-valued function
`j ↦ degreeOf (s j) P₁` is not constant on `{0, …, n-1}`, so it changes between some
`k` and `k + 1`; part 2 applied to `(P₁, P₂)` or to `(P₂, P₁)` gives a contradiction.

Compared with Tadić's argument, the split of `e₀` is described by the degree pattern of
`P₁` in the variables `X_{s j}`, which is the same for every monomial, rather than by a
partition read off one product of monomials. The contradiction for a separated
adjacent pair is a single weight count: the part of `μ` taken by `P₁` beyond the
variables `X_{s j}` would have weight exactly `D`. Tadić instead shows that the union and
intersection must go to the same factor (degree divisibility, which needs `d ≥ 2`) and
then finds a variable of degree `2`. The criterion here needs no case distinction on `n`
or on `D`.

### `prime_of_adjacent`

Under the same hypotheses `Q` is `Prime`: `MvPolynomial σ ℤ` is a unique factorization
monoid (Mathlib, with `Mathlib.RingTheory.Int.Basic` and
`Mathlib.RingTheory.Polynomial.UniqueFactorization`), where irreducible elements are prime
(`UniqueFactorizationMonoid.irreducible_iff_prime`).
