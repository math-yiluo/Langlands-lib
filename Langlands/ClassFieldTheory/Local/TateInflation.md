# Inflation and local cup products in positive Tate degrees

Author: Worker 42.

For a tower of fields `K ⊆ L ⊆ M` with `L/K` normal,
`relativeInflationLinear K L M n` is ordinary cohomological inflation
along the actual normal restriction `Gal(M/K) → Gal(L/K)` and the
inclusion `Lˣ → Mˣ`. The inclusion is an equivariant linear map on
additive unit groups. Its equivariance is the restriction identity on
field elements. The base field has an independent universe `v`; `L`
and `M` share universe `u`, hence the same actual scalar ring
`IntegerScalars.{u}`. The theorem `relativeInflationLinear_eq` identifies
this map with the existing `relativeInflation` when all three fields
share a universe.

`integralCohomology K L n` is ordinary cohomology of the actual trivial
representation on the lifted integers. `integralInflation` uses the same
normal restriction and identity coefficients. Both ordinary maps are
defined in every nonnegative degree.

For finite `L/K` and positive natural `n`, `relativeTateToOrdinary` and
`integralTateToOrdinary` specialize Mathlib's proved comparison
`TateCohomology.isoGroupCohomology` to the unit and trivial integral
representations. They use `Fintype.ofFinite` on the actual automorphism
group, as do the existing local Tate groups.

`relativePositiveTateInflation` and `integralPositiveTateInflation`
transport the corresponding ordinary maps through those comparisons.
Their comparison theorems prove the commuting diagrams by the inverse
law of the target comparison. Thus the maps use actual cohomology
groups, coefficient actions, and ordinary inflation.

`PositiveTateCupInflation` is the proposition that, for every positive
natural `n`, every ordinary degree-two class `c`, and every integral
Tate class `x` of degree `n`,

`Inf(c ∪ x) = Inf(c) ∪ Inf(x)`.

`FundamentalClassPositiveTateInflation invKL invKM` states instead the
scaled diagram for every pair of classes `c` and `d` of arithmetic
invariant `+1/[L:K]` and `+1/[M:K]`, respectively:

`Inf(c ∪ x) = [M:L] • (d ∪ Inf(x))`.

The first factor is on the left throughout. The unit-valued inflation
on the left has degree `n + 2`, and the integral inflation on the right
has degree `n`. The multiplier is the upper extension degree `[M:L]`.
`InvariantFamily.PositiveTateInflation` asserts the scaled diagram for
the relative maps of the same raw invariant family, over every finite
Galois tower above every finite extension of every `Q_p`. The base
p-adic field and the two upper fields retain independent universes.

These are proposition definitions, not proofs of cup naturality or
scaled compatibility. No invariant compatibility, fundamental-class
existence, or cup bijectivity is assumed in these predicates. As with
other predicates quantified over fundamental classes, the scaled law
alone can hold vacuously. A simultaneous local realization statement
must also assert invariant images and fundamental-class existence for
that same family.

Serre defines inflation on ordinary cohomology in nonnegative degrees
in *Local Fields*, XI.1, printed pp. 165–166 (PDF pp. 171–172). In
contrast, restriction and corestriction extend to every integer Tate
degree. XI.3, printed pp. 168–169 (PDF pp. 174–175), gives the
fundamental-class inflation formula and the degree-scaled cup diagram.
The positive-degree statements here use the ordinary-to-Tate
comparison in its valid range. They do not define inflation in degree
zero or negative Tate degrees. The ordinary degree-zero cup diagram,
and the comparison of ordinary cup with the published
dimension-shifted Tate cup, remain separate obligations.

The constructions and comparison certificates are derived content:
they specialize genuine ordinary cohomology maps and the proved
positive Tate comparison. The compatibility propositions express the
positive-degree part of the source formulas. The arithmetic
fundamental-class sign is unchanged; no reciprocity inverse or
geometric output inversion is used here.

Source ID: `serre-1979-local-fields`. Retained PDF SHA256:
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.
