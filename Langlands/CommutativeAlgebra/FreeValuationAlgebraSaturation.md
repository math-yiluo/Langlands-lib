# Scalar saturation in free valuation algebras

Let `R` be a commutative valuation domain, in arbitrary universe `u`, and let
`M` or `A` have independent universe `v`. There is no rank, discreteness,
Noetherianity or nonfield hypothesis on `R`.

`ScalarNormalization R M x` is actual normalization data: a nonzero scalar
`scalar`, a vector `vector`, and an `R`-linear `functional`, with proofs of
`x = scalar • vector` and `functional vector = 1`. The data type itself only
requires a commutative coefficient ring and a module. For a nonzero vector in
an `R`-free module over a valuation domain, `scalarNormalizationOfFree` chooses
such data using the existence proof below and classical choice. No uniqueness
or canonicity is asserted.

`exists_scalar_normalization_of_free` states that every nonzero vector `x` of
an `R`-free module has an expression `x = r • y`, with `r ≠ 0` and an actual
`R`-linear functional `l : M →ₗ[R] R` satisfying `l y = 1`. Choose a basis and
consider the finite nonempty support of the coordinates of `x`. Total
divisibility gives a nonzero coordinate dividing all the others. The proof
divides the coordinates by this one and uses the corresponding coordinate
functional. The private finite-support lemma proves the required common
divisor assertion by induction on the support.

`exists_scalar_normalization_not_mem` uses these chosen data to show that the vector `y` can be chosen
outside `m_R • M`, where `m_R = IsLocalRing.maximalIdeal R`. If `y` belonged to
this submodule, linearity would put `l y = 1` in `m_R`, contradicting that one
is a unit.

For a commutative `R`-algebra `A` that is free as an `R`-module, put
`P = Ideal.map (algebraMap R A) m_R`. If `P` is prime, then
`scalar_dvd_iff_mul_dvd_of_free_of_closedFibrePrime` proves, for every `s ∉ P`,
`a : A` and `r : R`,

```text
algebraMap R A r ∣ s * a  ↔  algebraMap R A r ∣ a.
```

For the nontrivial direction, normalize a nonzero `a = d • a₀` with `a₀ ∉ P`.
Compare `r` and `d` by total divisibility. If `r ∣ d`, the conclusion follows
immediately. Otherwise write `r = d * t` and cancel the nonzero scalar `d`
using torsion freeness of a free module. The given divisibility then implies
`t • z = s * a₀`. If `t` were a nonunit, the left side would lie in `P`, whereas
primality excludes this for the right side. Thus `t` is a unit, which supplies
the required quotient. The zero-vector case is handled separately. The proof
requires no domain assumption on `A` beyond the stated freeness and primality.

The provenance of the normalization is Laurent Moret-Bailly, *Une construction
d’extensions faiblement non ramifiées d’un anneau de valuation*, arXiv:1909.02917v3
(2022), Section 3.1, Proposition 3.1.1(2)(iii–iv),(3), PDF p.4. The Lean result
is the restriction to vectors of the original free module, with an explicit
coordinate functional witnessing primitivity. The scalar-divisibility
saturation assertion is derived here from this normalization and primality;
it does not invoke the paper's Theorem A or construct a valuation.

This result retains the actual `Module.Free R A` hypothesis. It does not assert
that a general smooth valuation algebra is free, and does not provide the
global unit lifts or prove the two-axis line-bundle extension statement.
