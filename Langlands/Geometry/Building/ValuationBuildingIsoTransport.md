# Actual building data and quotient transport under ambient isomorphisms

This internal construction applies to actual valuation-building data for a group
`G` over a nonarchimedean local field `F` and an actual group-scheme isomorphism
`f : G ≅ H`. All objects lie in the original common universe `u`; both ambient
groups have affine structure morphisms.

`CentralizerDatum.mapIso` keeps the actual centralizer group `Z`, the actual
torus `S`, its map `s : S → Z`, and the restriction-evaluation bijectivity proof.
It replaces the torus inclusion `i` by `i ≫ f.hom` and the centralizer inclusion
`j` by `j ≫ f.hom`. The published whole-torus centralizer isomorphism-square
theorem proves that this new inclusion represents the actual centralizer.
Closedness and the original factorization are transported through `f`.

The V6 transport theorem uses the published actual root-group transport and
reindexes the root-function family by `f.inv`. The torus is unchanged, so its
characters, centralizer translation and real normalization are unchanged.
Every target root-group point is the image of an original root-group point.
The group homomorphism laws and cancellation of `f.hom` with `f.inv` then
identify the transported V6 equation with the original equation. This applies
to every valuation in the original full class, giving V6 on the full image
class without a new compatibility premise.

`ValuationBuildingData.mapIso` combines these constructions with the published
ambient transport of connected reductivity and maximal split tori and the
full-class transport of `KPApartmentData`. Its reduced building is the actual
root-valuation quotient for that data. `mapIsoReducedBuildingEquiv` reuses the
published cross-torus quotient equivalence with the identity torus isomorphism.
It transports both coordinates of every quotient representative and intertwines
the existing actions by the actual point map `rationalPoints.map f.hom`.

The full fixer image equality is the published quotient transport theorem.
The common rational-character norm kernel is preserved and reflected by
restriction of characters along `f.hom` and `f.inv`. Combining this fact with
the actual quotient equivariance proves exact image equality of compact
stabilizers, as subgroups of the original target rational-point group.

The provenance is internal composition of the cited Lean interfaces and their
implemented equations; no new literature assertion is added. This construction
does not prove that a group admits valuation-building data, does not identify
two independently supplied valuation classes, and does not yet transport a
metric, vertex, special-point predicate, or supplied-model comparison.
