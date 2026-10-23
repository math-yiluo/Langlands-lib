# Isometric variable inclusions in weighted Tate algebras

Author: Worker 56.

This module constructs variable inclusions and complementary-variable zero
specializations for the actual weighted restricted series. It also concatenates
finite polyradii and supplies bounded maps for their two variable blocks.

## Scope and constructions

Let `r` and `s` be positive real polyradii on types `σ` and `τ`, and let
`e : σ ↪ τ` satisfy `s (e i) = r i` for every `i`. The coefficients `K` are
an ultrametric normed commutative ring. No completeness or norm-one hypothesis
is used in the generic constructions. The variable types and coefficient type
have independent universes; empty and infinite variable types are allowed.

`PositivePolyradius.weight_embDomain` proves equality of monomial weights on
embedded exponents. `GeneralizedTateAlgebra.rename r s e he K` restricts
Mathlib's formal-series renaming to an algebra homomorphism from the algebra at
`r` to the algebra at `s`. Its coefficients on embedded exponents are the original
coefficients; all other coefficients vanish. `rename_monomial` and `rename_X`
identify its values on actual monomials and coordinates. `norm_rename` proves
exact equality of the weighted Gauss norms, and `isometry_rename` states the
resulting metric isometry.

`killCompl r s e he K` restricts Mathlib's formal-series complementary-variable
zero map in the reverse direction. Its coefficient at `d` is the original
coefficient at `Finsupp.embDomain e d`. `norm_killCompl_le` proves contraction,
and `killCompl_rename` proves that it is a left inverse to the inclusion.
`killCompl_X` retains included coordinates; `killCompl_X_eq_zero` sends a
coordinate outside the image of `e` to zero.

When `K` is a normed field, the project's `BoundedAlgHom` interface is available.
`boundedRename` and `boundedKillCompl` package the same maps with positive bound
one; their composite is the bounded identity. Completeness is still not needed.

For `r` on `Fin n` and `s` on `Fin m`, `PositivePolyradius.append r s` is the
positive radius tuple on `Fin (n + m)` whose two blocks are exactly `r` and `s`.
Over a normed ultrametric field, `appendLeft` and `appendRight` are the bounded
inclusions for these blocks. `appendProjectLeft` and `appendProjectRight` retain
the indicated block and set the other block to zero. The module proves the
inclusions' norm equalities and coordinate formulas, the projections' contraction
estimates, and both projection-after-inclusion identities. Either block can have
zero variables, and the radii need not lie in a value group.

## Implemented arguments

The weight equality is the product formula for `Finsupp.embDomain`. For
`isRestricted_rename`, the exceptional exponents at each positive tolerance are
a subset of the image of the original finite exceptional set. The coefficient
outside the embedded exponents is zero, so it cannot be exceptional. This proves
weighted coefficient decay directly. The norm estimate is coefficientwise;
reading the embedded coefficients back gives the reverse inequality. An algebra
map preserving norms is an isometry by preservation of differences.

For `killCompl`, compose the original coefficient-decay limit with the injective
map on exponents, which tends to the cofinite filter. The weight identity converts
this to the required decay at `r`. Each coefficient norm is bounded by the
original Gauss norm, giving contraction. The algebra laws and left-inverse
identity descend from Mathlib's formal maps by subtype extensionality. The finite
block constructions specialize these maps using `Fin.castAddEmb` and
`Fin.natAddEmb`; positivity of the concatenated tuple follows separately on the
two blocks. No coordinate evaluation proposition is assumed.

## Provenance and limits

This is derived infrastructure for the finite positive-radius series of
Berkovich, *Non-Archimedean analytic spaces* (Trieste lectures, 2009),
Example 1.2.2(v), printed/PDF p.4, and the variable adjunction used for
Laurent/Weierstrass domains in Exercise 2.2.2(i), p.9. The source works with
complete nonarchimedean fields and finite variables. The direct coefficient
argument above extends the inclusion and zero-specialization constructions to
the stated generic scope; this extension is not attributed as a theorem of the
source. The source pages were read from the registered original. No matching
project errata entry was found.

The implementation uses Mathlib's `MvPowerSeries.rename`, `killCompl`, their
coefficient formulas and algebra laws from
`Mathlib/RingTheory/MvPowerSeries/Rename.lean`, together with the published
project weighted Tate algebra and bounded algebra-map definitions. It does not
construct a relative series algebra, quotient localization, or analytic domain,
and does not assert completion of the analytic-space or site prerequisites.

Registered original: `berkovich-2009-trieste-analytic-spaces`, SHA256
`8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`.
