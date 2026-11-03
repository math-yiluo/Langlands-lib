# Renard A.II.2: the categories in the fixed-dimension vector-space example

This construction implements the two categories and inclusion in the example
at A.II.2, printed p.251 / PDF257 of David Renard, *Représentations des groupes
réductifs p-adiques*, French version dated 9 July 2026. The original passage was
read. The registered source is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

For a field `k` and natural number `n`, `FixedDimensionVectorSpaces k n`
is the full subcategory of actual `ModuleCat k` objects satisfying both
`FiniteDimensional k X` and `Module.finrank k X = n`. All linear maps
between these objects are retained. Finite dimensionality is explicit:
Mathlib assigns finrank zero also to infinite-dimensional spaces, so the
natural-number equality alone would not express the source when `n = 0`.
The instance `fixedDimension_finite` and theorem `fixedDimension_finrank`
recover the two defining properties.

The field universe `u` and additional carrier-universe parameter `v` are
independent. Carriers lie in `Type (max u v)`. The coordinate space is
`ULift.{v} (Fin n → k)`, with its standard lifted vector-space structure.
This is a universe copy of `kⁿ`, not an assumed model: the ULift module
equivalence identifies its operations with those of `Fin n → k`.
The dimension and finite-dimensionality proofs show that
`standardCoordinateObject k n` is an actual object of the category, for
every `n`, including zero. No positivity, characteristic or field-size
restriction is added.

`OneObjectVectorSpaceCategory k n` is the full subcategory whose object
property is equality with that coordinate object. It has the actual object
`oneObjectVectorSpace k n`; `oneObjectVectorSpace_unique` proves that every
object equals it. All linear endomorphisms are retained, including
noninvertible maps. `fixedDimensionVectorSpaceInclusion k n` is its
canonical full-subcategory inclusion. This realizes the source's inclusion
functor directly. The full-subcategory Hom constructors and projections
provide the actual ambient linear maps and composition.

`coordinateVectorSpaceIso k n X` constructs an actual isomorphism in the
fixed-dimension category from the coordinate object to each `X`. It uses
Mathlib's `LinearEquiv.ofFinrankEq`, after the defining finite-dimensionality
instances and equality of dimensions are supplied, then turns the linear
equivalence into a `ModuleCat` isomorphism and a full-subcategory
isomorphism. Mathlib chooses bases using classical choice; this is the
choice of vector-space identifications described in the source. The
implemented route reuses Mathlib rather than transcribing an additional
proof from Renard's references.

This construction supplies the actual categories, actual inclusion and
intrinsic objectwise identifications. The assertion that this inclusion
admits one reverse functor and both natural isomorphisms remains a separate
statement and exact proof. No uniqueness or strict inverse for a
quasi-inverse, no comparison for all finite-dimensional spaces at once,
and no completion of A.II is claimed.
