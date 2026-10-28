# Block matrix and integration helpers for unequal-rank JPSS integrals

The theorem
`Langlands.RankinSelberg.AdjacentBlockReduction.unequalRankBlockIntegration`
proves the published `UnequalRankBlockIntegrationStatement`. Its independent
universes are `uX`, `uP`, `uG`, `uF`, `uV`, in that order. The proof assembles
the nine universally quantified components directly from the nine exported
helper constants, without applying their parameters or adding a hypothesis.
Each helper retains its original name and full source telescope.

The proof imports `UnequalRankBlockMatrix` and
`UnequalRankBlockIntegrationStatement` by module name. It uses the published
`blockMatrixAt` definition; it does not redefine it. The other project imports
are `CompactCosetExpansion`, `Hecke.ActionIntegrand` and
`UnequalRankFiniteExpansionProof`. The statement pair and its import closure
are unchanged.

## Finite scalar integration in an algebraic coefficient model

`exists_coefficient_fiber_integral` starts with a smooth complex representation
`ρ` of a topological group `G`, an equivariant functional `ℓ`, a continuous
map `U : X → G`, an arbitrary parameter family `B : P → G`, and a coefficient
`f` in `coefficientModel ρ ℓ`. Its compact-support premise concerns the whole
function-valued family `x ↦ (p ↦ f(B(p)U(x)))`. One common compact support is
required before quantifying over parameters. The supplied measure on `X`
need only be finite on compact sets; `X` has measurable open sets.

Choose a preimage vector `v` of `f` under `modelMap`. Smoothness makes its orbit
map locally constant, and composition with `U` and all the functionals
`w ↦ ℓ(ρ(B(p))w)` gives local constancy of the whole family
`H(x)(p) = ℓ(ρ(B(p)U(x))v)`. The published
`exists_finite_schwartz_expansion` supplies a finite family of
Schwartz–Bruhat functions `φᵢ` and sample points `xᵢ`, all chosen before `p`,
such that

```
H(x)(p) = ∑ i, φᵢ(x) * H(xᵢ)(p).
```

Each scalar summand is integrable: `φᵢ` is continuous with compact support,
and its sampled coefficient is constant. Set
`cᵢ = ∫ x, φᵢ(x)` using the supplied measure, and form the finite algebraic
sum `w = ∑ i, cᵢ • ρ(U(xᵢ))v` in the original carrier. Linearity of the
representation and functional, finite-sum integration, and
`integral_mul_const` show that the coefficient of `w` at every `B(p)` is
the required integral. The same expansion proves genuine scalar
`Integrable` for each fiber. The result supplies one coefficient before
every parameter.

There is no topology or completeness assumption on the representation carrier
`V`, and no integral with values in `V`. The parameter type `P` has no
topology or measure. The domain, parameter, group and carrier universes are
independent. Empty finite expansions and empty parameter types are retained.

## Actual block matrices and continuity

`unequalRankMatrix_snoc` writes `Fin.snoc Y x` as the sum of the matrix with
last row zero and the matrix with all preceding rows zero. The published
`rectangularUnipotent_add` and associativity then factor the actual
unequal-rank matrix as its zero-last-row base multiplied on the right by the
last-row unipotent.

`blockMatrixAt_entry` eliminates the rank equation
`hr : r = n + (j + k + 1)` and applies the published entry formulas
`unequalRankMatrix_val` and `appendIdentity_entry`. The resulting entry is
the diagonal-inclusion entry plus the rectangular entry, with the exact
dependent finite indices from the statement.

`blockMatrixAt_snoc_zero` proves equality of units by equality of matrix
entries. In the rectangular range for the earlier rows, `Fin.snoc_castSucc`
identifies the entries. The extra row is `Fin.last j` and has value zero.
The two supplied rank equations keep both matrices in `GL_(r+1)`.

These three algebraic helpers require only a field. In the actual block
matrix the smaller group has rank `n+1`, the rectangle has `j` rows and
`n+1` columns, and the final identity block has size `k+1`. The fixed larger
group has rank `r+1`. In particular, `n = 0` means smaller rank one,
`j = 0` means no rectangular rows, and `k = 0` means a final identity block
of size one.

`continuous_lastRowUnipotent` composes the published
`continuous_rectangularUnipotent` with the continuous map `x ↦ Fin.snoc 0 x`.
Its coordinate proof separates the final row, where the map is the identity,
from the earlier rows, where it is constant zero. It requires a topological
ring structure on the field.

## The supplied product measures and genuine row Fubini

`rowMeasure ν t` is the finite product of the same supplied scalar additive
Haar measure `ν`. `rectangularMeasure ν j t` is the finite product of those
row measures over `j` rows. No measure is rescaled or replaced, and empty
products have unit point mass.

`rectangular_lastRow_measurePreserving` instantiates Mathlib's
`measurePreserving_piFinSuccAbove` at `Fin.last j`. The measurable equivalence
carries the rectangular measure on `j+1` rows to

```
(rowMeasure ν t).prod (rectangularMeasure ν j t).
```

The selected last row is the first product coordinate; the earlier rows are
the second. This helper retains the source's additive-group telescope,
supplied topology and measurable space, and sigma-finiteness of the supplied
scalar Haar. It adds no field or Borel-space assumption.

`rectangular_integral_lastRow` applies the inverse of that
measure-preserving equivalence. Its explicit hypothesis is `Integrable f`
on the whole rectangular space. Transport preserves this integrability, so
Mathlib's `integral_prod_symm` gives the order

```
∫ Y, ∫ x, f (Fin.snoc Y x) ∂rowMeasure ν t ∂rectangularMeasure ν j t.
```

The inverse equivalence inserts the last row, and `Fin.insertNth_last'`
identifies that insertion with `Fin.snoc`. Thus the earlier rows are outer
and the last row inner. This is a genuine Fubini proof with its scalar
integrability premise retained. It includes both `j = 0` and `t = 0`.

## Rectangular coefficient integrability

`blockCoefficient_integrable` assumes smoothness and one supplied compact
rectangular set `C` containing every nonzero block evaluation, uniformly
over the smaller-group variable `g`. It turns this hypothesis into compact
support of the entire function-valued rectangular family.
Apply `exists_coefficient_fiber_integral` with the continuous
`rectangularUnipotent j k`, the base family `appendIdentity n (j+k+1)`,
and the supplied `rectangularMeasure ν j (n+1)`. The measure is finite on
compact sets by the published finite-product measure instances. The
integrability part of the generic result gives the conclusion at each `g`.

The exact telescope retains the field topology, topological-ring structure,
measurable space, sigma-finite supplied scalar Haar and Borel-space instance
on the whole rectangle. It adds neither Hausdorffness nor a scalar-field
Borel-space instance. The representation carrier remains algebraic and in
an independent universe. Existence of the compact set `C` is a separate
obligation.

## The existing totalized outer integral

`unequalRankIntegralAt_eq_outer` eliminates the natural-number rank equation
and unfolds the existing iterated integral from `QuotientIntegrals`.
At each quotient point `q`, `Quotient.out_eq q` identifies the existing
quotient integrand with its formula at `q.out`. Applying
`integral_mul_const` twice within that rectangular integral takes out
`f'(q.out)` and
`determinantWeight abv q.out (s - ((j+k+1 : ℕ) : ℂ) / 2)`,
in the statement's order.

This identity uses the original arbitrary quotient and rectangular measures.
It adds no convergence premise, sigma-finiteness, support, or Haar
normalization. It compares the existing totalized iterated integrals and
does not interchange quotient and rectangular integration. It retains only
the source's field, topology and measurable-space assumptions; no
topological-ring instance is required by this helper.

## Provenance and scope

Worker 180 authored these nine proofs and their design in the unreviewed
shared adjacent-span draft, revision 11 of task
`798cefd9-ab16-4562-ab1a-085680064306`. The exact source pair is
`Langlands/Representation/RankinSelberg/UnequalRankBlockSpanProof.lean`
and its Markdown under
`revision-11-bdc9755f26661654885ff0567c2254dde91cbe61d4449ae448ada9bf4b058b63`.
Worker 52 extracted the nine ready helpers, preserved their full telescopes,
assembled the published aggregate and wrote this documentation. That
unfinished source module is not imported.

The original motivation is H. Jacquet, I. I. Piatetski-Shapiro and J. A.
Shalika, *Rankin–Selberg Convolutions*, American Journal of Mathematics 105
(1983), 367–464, registered as `jpss-1983-rankin-selberg`, SHA-256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
Printed pp.393–395 (one-based PDF pp.28–30) treat unequal ranks in the proof
of Theorem 2.7. Page 393 uses uniform rectangular support and finite
translates; pp.394–395 give the Fourier comparison and adjacent ideal
argument.

The predecessor is the same authors' *Automorphic Forms on GL(3) I*,
Annals of Mathematics (2) 109 (1979), 169–212, registered as
`jps-1979-gl3-i`, SHA-256
`6446822f267f9f95156ce7a193409209e56ce7858ed6d3d350480e73f35b1aa5`.
Printed pp.188–190 (one-based PDF pp.21–23) contain the block integrals
(4.1.1)–(4.1.3), Proposition 4.1.4, Lemma 4.1.5 and the finite-translates
and adjacent ideal argument. Both passages were read in the retained
originals during the statement extraction.

The general coefficient-fiber formulation, natural-number rank transport,
product-coordinate measure change and totalized outer-integral identity are
internal derived interfaces. They are not claimed to occur verbatim in
either original. Their concrete conventions are those of the published
`QuotientIntegrals`, `RowFourier`, `CompactCosetExpansion` and
`UnequalRankFiniteExpansionProof` pairs. The package proves no uniform
support existence, Fourier preimage existence, adjacent-span equality,
analytic continuation or functional equation.
