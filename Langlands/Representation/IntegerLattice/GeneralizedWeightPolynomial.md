# Polynomial matrices on actual generalized-weight blocks

This construction supplies explicit complex multivariate polynomial matrices
and coefficient polynomials for the last paragraph of Renard 2026,
Appendix C.III, printed p.280 / PDF286. It does not prove that evaluating the
product matrix gives the actual lattice action, or that the coefficient
polynomials assemble into the original matrix coefficient. Those comparisons
are intended for separate statement and proof units.

## Source and provenance

The governing source is David Renard, *Représentations des groupes réductifs
p-adiques*, French version dated 9 July 2026, Appendix C.III, printed
pp.279–280 / one-based PDF285–286. Its registered source identifier is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The source normalizes the generator on each simultaneous block, expands every
unipotent integer power as a finite binomial sum, and observes that its scalar
entries are polynomials. It then obtains general matrix coefficients by
linearity.

The source is retained at
`/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`.
Both cited pages were read directly, with the product display on PDF286 also
checked visually.

The supplementary 2010-edition corrections, registered as
`renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
are retained at
`/home/taskhub/pilot/literature/Renard — Représentations des groupes réductifs p-adiques- corrections et compléments (2010 edition errata).pdf`.
PDF18–19 were read directly. They correct the parentheses around
the whole scalar-times-unipotent factor in that edition's first product.
The 2026 display already has those parentheses. These definitions use the
published actual block and its normalized generator differences and introduce
no alternate action.

The exact polynomial witnesses, their names, the ordered product of polynomial
matrices, and the uniform ambient-dimension truncation are derived
formulations of this source passage. The source does not specify a preferred
polynomial representation or a minimal nilpotence bound. The coefficient
construction expresses the usual matrix-coordinate contraction explicitly.

## Constructions

All declarations are in `Langlands.IntegerLattice`. Let `V : Type u` be a
complex vector space and `A` an actual commuting invertible tuple on `V`,
`c : Fin d → ℂˣ`, `W = generalizedWeightBlock A c`, `r = finrank ℂ W`,
and `D = finrank ℂ V`. The entries of `A` and the block `W` are the existing
published constructions.

1. `coordinateBinomialPolynomial i k` substitutes the multivariate variable
   `X i` into the complex polynomial
   `(k!)⁻¹ • descPochhammer ℂ k`. Its evaluation at any
   `x : Fin d → ℂ` is `Ring.choose (x i) k`. In particular it represents the
   binomial coefficient at every positive, zero or negative integer.
2. For a basis `b : Basis (Fin r) ℂ W`,
   `generalizedWeightBinomialMatrixFactor A c b t` is the matrix with entries

   ```text
   sum (0 ≤ k < D), coordinateBinomialPolynomial t k
     * C (b.repr ((normalizedGeneratorDifference A c t ^ k) (b q)) p).
   ```

   It is a matrix over `MvPolynomial (Fin d) ℂ`, indexed by row `p` and
   column `q`. The endomorphism power is taken before applying it to `b q`.
3. `generalizedWeightPolynomialMatrix A c b` is the ordered matrix product
   of those factors, in the order of `List.ofFn` on `Fin d`. Matrices are
   multiplied as matrices over the commutative polynomial coefficient ring;
   no commutative-ring structure on the block endomorphism ring is assumed.
4. For a basis `B` of `V` indexed by
   `Σ a, Fin (finrank ℂ (generalizedWeightBlock A a))`, a vector `v` and
   an algebraic functional `ell : V →ₗ[ℂ] ℂ`,
   `generalizedWeightCoefficientPolynomial A c b B v ell` is

   ```text
   sum p, sum q, C (ell (b p : V) * B.repr v ⟨c,q⟩)
     * generalizedWeightPolynomialMatrix A c b p q.
   ```

   This is intended as the polynomial contribution of block `c` under the
   future action comparison with the compatibility hypothesis
   `∀ q, B ⟨c,q⟩ = (b q : V)`. The definition accepts the two bases without a
   compatibility assumption; the equality comparing it to the action must
   state and establish that compatibility. It chooses no decomposition or
   basis and assumes no desired coefficient identity.

The character factor is not part of these polynomials. A future comparison
will multiply their evaluations by `coordinateCharacter c`.
The local matrix depends on the chosen basis; neither uniqueness nor basis
independence is claimed here. The ambient coefficient coordinates in the
last construction come from the actual supplied basis `B`.

## Intrinsic laws and proof implementation

`eval_coordinateBinomialPolynomial` commutes complex evaluation with the
univariate substitution, identifies
`(MvPolynomial.eval x).comp MvPolynomial.C` with `RingHom.id ℂ`, and
applies the published
`Langlands.complexBinomialCoefficientPolynomial`. It proves the evaluation
formula for every complex point without any representation hypothesis.

`eval_generalizedWeightBinomialMatrixFactor` distributes evaluation through
the finite sum, products and scalar constants and uses that coordinate law.
It proves only the entrywise evaluation of one factor, without an
identification with an actual group action.

`generalizedWeightPolynomialMatrix_rank_zero` evaluates the empty ordered
product to the identity matrix. The full unit-label type need not be finite.
Every sum within a coefficient polynomial ranges over the finite local basis,
so zero blocks give empty sums. The theorem
`generalizedWeightCoefficientPolynomial_eq_zero_of_finrank_eq_zero`
establishes their zero contribution by the empty index type.

These constructions retain arbitrary carrier universe `u`, every natural
lattice rank, all unit labels and zero blocks. Their definitions and
intrinsic laws have no `FiniteDimensional ℂ V` premise: they use the
natural-number `finrank` and the explicitly supplied bases, and make no
action comparison. Existence of those bases is not asserted here. This
algebraic generality is internal; the future action and coefficient
comparisons have the source's finite-dimensional hypothesis.
At ambient dimension zero each factor has an empty binomial sum; its matrices
have zero rows and columns in the finite-dimensional setting because every
actual block is zero. No assumption
of positive rank, positive dimension or a nonzero block is imposed.

## Remaining comparisons

The published generalized-weight product theorem already gives the
character-times-binomial product of actual endomorphisms. A separate
statement and proof should identify the evaluation of this polynomial matrix
with the matrix of that action and then contract its entries against the
ambient block basis. They must choose compatible bases from the actual
decomposition, use one finite set of all nonzero blocks for all lattice
points, and retain negative coordinates and the zero cases.

This file supplies neither a new proof of the final coefficient proposition
nor a finite distinct enumeration of occurring characters. The latter has
its own focused task. No Appendix or whole-book completion is asserted.
