# Reindexing actual equivariant derived-section diagrams

This internal construction combines the published
`EtaleDerivedEquivariantDiagram` with the actual coefficient reindexing
functor of `EtaleEquivariantCoefficientReindex`. It supplies the induced
comparison directly from their formulas and claims no additional theorem
from the original literature.

Let `S : J ⥤ Scheme.{u}ᵒᵖ` be a diagram with etale underlying scheme maps,
let `R : Type u` be a commutative ring, and let an abstract group `G` act
compatibly at its vertices through `ρ` and `hρ`. For an index functor
`F : K ⥤ J`, `reindex_derivedSections` identifies derived sections of
the reindexed coefficient diagram with precomposition of the original
derived action diagram by `F`. This is equality of actual functors into
group actions in the bounded-below derived category of modules. Both
the action objects and the geometric derived transition maps are retained.
The identity isomorphism `reindexDerivedSectionsIso` records the comparison.

`reindexDerivedSectionsFunctorIso` makes it natural in the entire
equivariant coefficient diagram. The existing reindexing functor also
retains coefficient morphisms at the image vertices, so both functors have
the same object and morphism formulas. The isomorphism uses the constructed
objectwise identity comparisons; its coefficient naturality follows at
each vertex from the identity laws without a further compatibility
hypothesis.

The four `reindex_derivedSectionsHomologyIso_*_app` and
`reindex_derivedSectionsZeroIso_*_app` equations record that the canonical
forward and inverse comparisons with ordinary cohomology and ordinary
sections are precisely their original components at `F.obj i`. They are
definitional equations; equality of derived maps is not inferred from
their cohomology.

The index object and morphism universes and the group universe are
independent. The vertex sheaf categories use a common localization universe,
independently of the module derived-category localization universe.
The reindexed diagram uses the original sheaf localization instance at
each image vertex.
Coefficients are actual small-etale module sheaves placed in degree zero,
and their transitions need not be invertible. The scalar ring is fixed,
and global sections are ordinary. Compact supports, traces, topology,
smoothness, scalar change, inverse limits and actual Harris specialization
remain outside these constructions.
