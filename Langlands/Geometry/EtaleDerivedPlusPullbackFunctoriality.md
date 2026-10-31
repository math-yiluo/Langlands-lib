# Identity and composition of bounded-below derived etale pullback

This internal successor lifts the published ordinary section-chain identities
in `EtaleDerivedPullbackFunctoriality` to actual morphisms in D⁺ of modules.
It uses the actual small-etale global sections and restriction functors, for
etale scheme maps over a fixed commutative coefficient ring. The sheaf and
module derived-localization universes are independent.

`derivedResolutionSectionsMapWithCoefficients` constructs the extended section
chain map for a given source resolution, target resolution and map between the
restricted source resolution and the target. A map compatible with the
augmentations computes derived pullback followed by the target coefficient map.
The formula holds with any such source and target injective resolutions and
compatible lift. It follows from the generic
`DerivedPlusSourceFunctoriality.derivedMap_comp_map_ofResolutions` formula and
functoriality of extension by zero. For identities, the published identity
restriction lift makes the section chain composite the identity. For
composition, use the source resolution, its successive restrictions and its
restriction along the composite map; the published restriction-composition
lift identifies the two chain composites. Localization preserves these
equalities, and the adjacent resolution isomorphisms cancel.

These are equalities of the actual derived morphisms. They are not inferred
from equality of maps on cohomology. Ordinary sections are used throughout;
compact supports, arbitrary complexes of source sheaves, scalar change and
Harris geometric realization remain separate constructions.
