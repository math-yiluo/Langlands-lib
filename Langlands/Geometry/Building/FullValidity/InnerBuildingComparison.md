# Identity-equivariant comparison from an inner-equivariant one

This is derived infrastructure for torus rebasing. Translation by `g` on a
valuation building is a building isomorphism: it preserves the chart-defined
facets and apartments, and on a translated apartment changes the group index
from `h` to `g*h` while retaining the affine coordinate.

Suppose a supplied building equivalence `Φ` intertwines `Int(g)` and has both
geometric directions. `BuildingEquivalence.ofInner` uses
`y ↦ Φ(g⁻¹ • y)`. Its equivariance for the identity follows from the equation
for `Φ` applied to `g⁻¹*k*g`. Both geometric directions follow by composing the
supplied comparisons with translation. The proof uses `IsFacet.smul`,
`IsApartment.smul`, `IsBuildingIso.trans`, and the actual group-scheme formula
`comp_innerIso_hom`, with `constantPoint_self` on rational points.

This constructs a comparison from supplied data. It does not assert existence
of a transported full KP datum or of a valid assignment.
