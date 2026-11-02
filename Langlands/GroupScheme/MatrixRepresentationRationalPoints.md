# Rational-point matrices of actual group-scheme representations

Author: Worker 1107.

Let `R : CommRingCat.{u}` be any commutative ring, let `G` be a group scheme
over `Spec R`, and let `n : Type` be a finite index type with decidable
equality. For an actual representation
`ρ : MatrixRepresentation G n`, this module constructs the homomorphism

```text
ρ.rationalMatrix : (Over.mk (𝟙 (Spec R)) ⟶ G.X) →* GL n R.
```

The source is the actual group of sections of `G` over `Spec R`.
The map first applies the published `ρ.pointMatrix` at this test scheme,
and then applies the ring map of `Scheme.ΓSpecIso R` to every entry.
Thus the resulting matrix has entries in `R` itself. No field hypothesis is
needed.

## Formulas and injectivity

All declarations are in `Langlands.GroupScheme.MatrixRepresentation`.

`rationalMatrix_apply` gives the defining formula: compose a point `x` with
the underlying scheme morphism of `ρ`, apply the existing
`GeneralLinear.pointsEquiv`, and transport its entries from global sections
to `R`. `rationalMatrix_apply_apply` identifies its `(i,j)` entry with the
pullback of `GeneralLinear.entrySection n R i j` along that composite,
followed by `Scheme.ΓSpecIso R`. Its proof applies the published coordinate
formula for `GeneralLinear.pointsEquiv`.

For a homomorphism `f : H → G`, `rationalMatrix_restrict` states

```text
(ρ.restrict f).rationalMatrix x = ρ.rationalMatrix (x ≫ f.hom.hom).
```

It follows from the published `pointMatrix_restrict` before applying the
entrywise ring map. The construction is a bundled group homomorphism, so it
preserves identity, products and inverses.

`pointMatrix_injective` proves injectivity on every test scheme when
`Mono ρ.hom.hom` holds. Equality of matrices gives equality of the composite
points by the existing multiplicative point equivalence, and cancellation
of the monomorphism gives equality of the original points.
`rationalMatrix_injective` then proves injectivity on the actual rational
points: equality of the transported matrices gives equality of every entry
before transport by injectivity of `Scheme.ΓSpecIso R`, and the previous
result applies.

## Provenance and scope

This is a derived interface construction using the published
[`MatrixRepresentation`](MatrixRepresentation.md), the existing GL point
equivalence and coordinate formula, Mathlib's entrywise
`Matrix.GeneralLinearGroup.map`, and the canonical global-section
isomorphism of an affine spectrum. The only new arguments are composition,
entrywise injectivity and cancellation of a mono. No external structural
theorem is asserted.

The results allow any commutative ring, including nonreduced rings, and an
empty index type. The all-test injectivity result retains nonaffine and
nonreduced test schemes. The module constructs no representation satisfying
the monomorphism hypothesis and makes no topological assertion.
