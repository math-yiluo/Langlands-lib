# Actual finite split tangent tests

This internal algebra construction works in every common universe `u`. Let
`k` be a commutative ring, let `K` be a field with its specified `k`-algebra
structure, and let `ι : Type u` be a finite type. The abbreviation `ring K ι`
is the actual square-zero ring `TrivSqZeroExt K (ι → K)`, with multiplication
`(a, v)(b, w) = (ab, aw + bv)`. Empty index types are allowed.

The first coordinate is a surjective `k`-algebra augmentation to `K`.
`test k K ι` bundles this ring and augmentation as an actual `ArtinianTest`.
Its local-ring instance uses the square-zero extension unit criterion: an
element is a unit exactly when its first coordinate is. Its Artinian-ring
instance first regards the underlying finite product as an Artinian
`K`-module and then restricts scalars through the coordinatewise scalar
tower. `reduction` is the actual arrow to the residue test, and `sectionMap`
is the constant inclusion. `sectionMap_reduction` proves their section
identity. `reduction_elementary` proves surjectivity and annihilation of the
augmentation kernel by the maximal ideal: the two ideals are equal, and
two elements with zero first coordinate multiply to zero.

`axis i` is induced by the linear coordinate projection `v ↦ v i`.
`weighted c` is induced by `v ↦ ∑ i, c i * v i`. Both are actual augmented
arrows to the published dual-number test. Their composites with dual-number
reduction equal `reduction`, and their composites after `sectionMap` equal
the constant dual-number section.

With decidable equality on `ι`, `includeAxis i` is induced by the linear
map sending a scalar to the function supported at `i`. Its reduction is
the dual-number reduction. The two central coordinate identities are:

- `includeAxis_axis`: projection at the included coordinate is the identity;
  projection at a distinct coordinate is reduction followed by the constant
  section.
- `includeAxis_weighted`: the composite is precisely the published actual
  arrow `dualScale k K (c i)`, which sends epsilon to `c i` times epsilon.

These identities are proved by equality of the underlying algebra maps,
then by equality of their first and second coordinates. The weighted
identity reduces to evaluation of a finite sum on a single supported
function.

The provenance is internal: this module applies Mathlib's square-zero
extension functor to explicit linear maps and uses the already published
actual Artinian-test and dual-number interfaces. The specified section is
particular to this split ring; no section or coefficient-field structure
is imposed on general Artinian tests. This module constructs no Picard
family, formal hull, algebraization, or smooth atlas.
