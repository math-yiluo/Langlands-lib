# Restriction of weighted series to smaller positive polyradii

This module constructs coefficient-preserving restriction between actual
weighted restricted-series algebras. The selected definition is
`Langlands.Analytic.GeneralizedTateAlgebra.boundedRestrictRadius`.
It is an elementary compatibility for later radius changes in weighted
affinoid presentations.

## Parameters and direction

Let `σ` be any variable type and let `r, s : PositivePolyradius σ`.
The hypothesis `hsr : ∀ i, s i ≤ r i` permits equality and requires only
that both polyradii are strictly positive. For an ultrametric normed
commutative ring `K`, `restrictRadius r s hsr K` is a `K`-algebra map

```text
GeneralizedTateAlgebra r K →ₐ[K] GeneralizedTateAlgebra s K.
```

Its value is the same formal power series. Thus algebra restriction
goes from the larger radii to the smaller radii. All variable and
coefficient universes are independent. No finiteness of `σ`, nontriviality
of `K`, or completeness is assumed in this construction.

For an ultrametric normed field `K`, `boundedRestrictRadius` packages
this map as the project's `BoundedAlgHom` with the explicit positive
bound `1`. This field assumption matches the project's normed-algebra
instances; the underlying algebra map and norm estimate already hold
for the more general coefficient rings above.

## Construction and estimates

`PositivePolyradius.weight_mono` proves that

```text
s.weight d ≤ r.weight d
```

for every finitely supported exponent `d`. Its proof applies
nonnegative finite-product monotonicity to the coordinate powers.
`PositivePolyradius.append_mono` proves coordinatewise monotonicity of
finite concatenations by considering the two blocks of variables.

For a series `f` restricted at `r`, its coefficient norms multiplied
by the `s` weights are nonnegative and bounded above by the analogous
`r` weights. The latter tend to zero along the cofinite filter by the
definition of the source algebra. `isRestricted_of_radius_le` applies
the squeeze theorem to prove that the unchanged formal series belongs
to the target algebra.

The restrictedness result gives an inclusion of the two actual restricted
subalgebras. `restrictRadius` uses Mathlib's `Subalgebra.inclusion`, whose
ring and scalar compatibility proofs are reused directly.
`series_restrictRadius` and `coeff_restrictRadius` give the unchanged
formal series and every unchanged coefficient explicitly.
`restrictRadius_injective` follows by forgetting to formal series and
using subtype extensionality.

`norm_restrictRadius_le` proves

```text
‖restrictRadius r s hsr K f‖ ≤ ‖f‖.
```

The implemented proof uses the target Gauss-norm coefficient criterion.
Each target weighted coefficient is bounded by the corresponding source
weighted coefficient and hence by the source norm. This is a contraction
statement; it makes no assertion of isometry or surjectivity.

## Formulas and compatibility

`restrictRadius_monomial` and `restrictRadius_X` preserve the actual
coefficient monomials and coordinate series, respectively.
`restrictRadius_self` is the identity at an unchanged radius.
`restrictRadius_trans` identifies successive restrictions through
`r ≥ s ≥ t` with direct restriction from `r` to `t`.
`boundedRestrictRadius_self` and `boundedRestrictRadius_trans` give
these identities as equalities of bounded algebra maps. Their proofs use
extensionality and the corresponding unbundled identities. The
coefficient, injectivity and norm proofs rewrite by the underlying-series
identity rather than repeatedly unfolding the algebra map.

`restrictRadius_rename` states the compatibility square for a variable
injection `e : σ ↪ τ`. Suppose the large radii `r` and `t` agree along
`e`, the small radii `s` and `q` agree along `e`, and `s ≤ r`, `q ≤ t`.
Restriction from `t` to `q` after renaming from `r` to `t` equals
renaming from `s` to `q` after restriction from `r` to `s`.
The proof applies subtype extensionality and rewrites both underlying
series with `series_restrictRadius` and `series_rename`. Both sides are
then the same renamed formal series.

`boundedRestrictRadius_appendLeft` specializes this compatibility to
finite concatenated radii when only the second block shrinks:
restricting the enlarged series algebra and then evaluating the
composite on an old-variable series is precisely the old-variable
inclusion at the smaller new radii. The result is an equality of
bounded algebra maps, proved by extensionality and unchanged series.

## Provenance and scope

The source context is Vladimir G. Berkovich, *Non-archimedean analytic
spaces* (Trieste lectures, 2009), Example 1.2.2(v), printed/PDF p.4,
registered as `berkovich-2009-trieste-analytic-spaces`, SHA256
`8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`.
That example defines finite positive-polyradius restricted series and
their weighted Gauss norm over a complete nonarchimedean field.

The restriction construction is derived directly from that coefficient
formula rather than cited as a separately stated theorem. The proof
above explains the extension to arbitrary variable types and ultrametric
normed commutative coefficient rings without completeness. The module
reuses the actual series, norm and coordinate constructions from
`GeneralizedTateAlgebra.Definitions` and `EvaluationDefinitions`, and the
variable inclusions from `GeneralizedTateAlgebra.Embedding`.

This unit establishes algebra restriction and its intrinsic norm and
compatibility obligations. It does not assert analytic-domain
representability, an image description on spectra, or a quotient
restriction for general affinoid presentations. Those require additional
constructions and theorems.
