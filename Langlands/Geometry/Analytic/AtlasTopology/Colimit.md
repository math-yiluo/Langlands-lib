# Continuous gluing and the topological colimit of a net

Author: Worker 36.

This is derived topology infrastructure for Berkovich's actual atlas convention.
The source is Vladimir G. Berkovich, *Etale cohomology for non-Archimedean
analytic spaces*, Publications mathematiques de l'IHES 78 (1993), section 1.1,
printed pages 13–14 (PDF pages 10–11): the quasinet and net definitions and
Lemma 1.1.1(i). Section 1.2, Definition 1.2.3, printed page 16 (PDF page 13),
uses a net of actual affinoid domains. The registered source is
`berkovich-1993-etale-cohomology`, SHA256
`06b42aca1c8f237e607d2cf1f15a41fdc9718324a4dc9fd5bce66574254bb91c`.
The categorical colimit is an explicit consequence of those conventions,
rather than a separately numbered assertion of the source.

For a family `τ` of subsets of a topological space `X`, `Member τ` is the
subtype of actual family members, ordered by inclusion. The net condition
gives a common member through every point shared by two members: apply
quasinet coverage to that point in their intersection. This does not require
the intersection itself to belong to the family.

`CompatibleMaps τ Y` consists of supplied continuous maps from each actual
member subspace to `Y`, with equality under every contained-member inclusion.
Common members prove agreement on all overlaps. `glueFun` evaluates the
input map on a chosen member containing the point. The overlap argument
proves that it agrees with every member map, independently of that choice.
Quasinet continuity, proved in `QuasinetProperties` by finite neighborhood
unions, makes this function continuous. Coverage gives uniqueness.
`continuousMapEquiv` packages actual restriction and this constructed glue as
inverse operations. The source and target may have independent universes;
the construction also includes empty spaces and empty families when the
net condition holds.

`memberDiagram` sends a family member to its actual subspace in `TopCat` and
a containment to its continuous inclusion. `memberCocone` has vertex the
original space and its actual inclusion maps. `memberCoconeIsColimit`
constructs its universal arrow using the preceding glue, proves the cocone
equations on every member, and proves uniqueness by coverage. This is an
actual `CategoryTheory.Limits.IsColimit`, for the diagram in `TopCat` at
the universe of `X`. No openness, ambient Hausdorffness, compactness, finite
cover, or intersection closure is assumed.

`IndexedAffinoidAtlas.chartRangeCoconeIsColimit` applies this construction to
the range family of a supplied actual affinoid atlas, using its published
net property. Its objects are the actual chart ranges with their subspace
topologies and its maps are subspace inclusions. This result supplies the
topological colimit of an already supplied atlas. Affinoid algebra gluing,
construction of an atlas from abstract gluing data, extended atlas
comparison, analytic localization, sheaves and sites remain separate work.
