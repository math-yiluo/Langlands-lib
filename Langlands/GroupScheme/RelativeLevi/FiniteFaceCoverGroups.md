# Actual term and vector-layer groups over the finite affine cover

Let `D` be the constructed finite face-chart cover of a supplied relative parabolic. This module assembles the actual local root-weight term group schemes and the actual local exact-layer vector groups over one affine etale surjective cover source, together with the original inclusion, successive-step and quotient homomorphisms.

For each actual chart, `termGroup`, `layerGroup`, `termInclusion`, `termStep` and `layerProjection` name its original objects and maps. Their group laws are the original represented group laws. The term and layer schemes are affine, and successive chart inclusions have the original ambient composition equation.

Over the cover source, `FiniteParabolicFaceCover.termGroup` and `layerGroup` use the established assembly of group objects on a finite disjoint decomposition. `termComponentIso` and `layerComponentIso` recover every original group, including its group law. The assembled `termInclusion` maps to the actual pullback of the original ambient group; `ambientComponentIso` is the canonical direct-pullback comparison. `termInclusion_component`, `termStep_component` and `layerProjection_component` prove exact recovery of the prescribed original maps. The assembled successive inclusion and ambient inclusion compose to the next original ambient inclusion. Both assembled term and layer schemes are proved affine.

The component index is lifted into the universe `u` of the base schemes to apply the published disjoint-group assembly interface at arbitrary universe `u`. `groupsSpace` is the actual finite coproduct on these indices, and `groupsBaseMap` is proved etale and surjective. The construction uses the same finite chart collection as `D` and retains all original chart projection maps. It imposes no restriction to universe zero.

The generic `DisjointGroupAssembly.homOfFamily` constructs the actual map between assembled groups from a family of actual component maps, and its component equation is proved by the fully faithful restriction functor. This is used for both consecutive-term and vector-layer projections.

This module establishes the objects, maps, affine geometry and exact component equations over the cover source. It does not yet assert that the assembled inclusions are closed, that the assembled projections have the full fppf quotient property, that the terms have invariant overlap descent data, or that a global filtration has descended to the original base. Those properties follow in subsequent descent work from these component equations and the existing local geometric results. The local quotient maps themselves are the already proved actual full fppf quotient maps.

The provenance is derived internal infrastructure using actual finite face charts, finite disjoint group-object assembly, fully faithful component restrictions and canonical pullback comparisons. It adds no independent literature claim.
