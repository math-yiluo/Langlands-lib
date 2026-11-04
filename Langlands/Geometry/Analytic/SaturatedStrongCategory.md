# The category of saturated affinoid atlas presentations

This internal construction packages the actual saturated atlases and strong
morphisms already constructed in the imported modules. The coefficient field is
complete, normed and ultrametric. All chart algebras are the existing presented
affinoid algebras, and all pullbacks are bounded algebra homomorphisms.

`StrongHom.ext_of_saturated` proves that strong morphisms with the same
continuous base map are equal if their bounded pullbacks agree at one admissible
target for each original source chart. Its sole atlas hypothesis is
`HasAllLocalDomains` on the source. The previously established
`pullback_eq_changeTargetPullback` recovers every other supplied pullback by the
same canonical bounded chart change. Equality of the selected bounded maps
therefore gives equality of the complete dependent pullback families.

The two identity laws for `saturatedComp` follow by computing on an admissible
chain with an identity chart restriction and applying the identity laws for
bounded homomorphisms. The left identity requires source saturation; the right
identity also requires intermediate saturation, as does the composition itself.
Associativity requires saturation of the source and the two intermediate
atlases; the final target remains arbitrary. For each source chart, choose a
chain through the three morphisms. Exact chain recovery expresses both iterated
composites as the corresponding triple bounded composite. Associativity of
bounded homomorphisms proves equality there, and source-saturated extensionality
gives equality at all admissible targets. No equality of algebra maps is inferred
from their actions on spectrum points.

`saturatedComp_eq_compOfDirected` compares the complete strong composites where
the earlier directed construction also applies. It retains both original
directedness hypotheses and the source and intermediate saturation hypotheses.
The comparison follows from exact recovery on one admissible chain and the same
extensionality theorem.

`SaturatedAtlasPresentation` consists of an actual `AffinoidAtlasPresentation`
and its `HasAllLocalDomains` property. Its category has the original complete
`StrongHom` families as morphisms, the actual atlas restrictions as identities,
and `saturatedComp` as composition. The proved full-map laws supply the category
laws. `spaceFunctor` retains the literal spaces and continuous base maps.
`ofSaturation` constructs an object from any actual presentation using
`saturatedPresentation` and the proved `saturatedAtlas_hasAllLocalDomains`.
It preserves the ambient space exactly. Its index universe is the ambient-space
universe, as in the existing saturation construction; no identification with the
original index type is claimed.

The provenance is internal: full chart-change recovery and exact chain recovery
from the imported constructions imply the laws by bounded-map algebra. The object
property is discharged by the already constructed saturation, rather than assumed
as an existence output. Localization, extension of maps between arbitrary
unsaturated atlases, comparison with the full analytic-space category, and analytic
étale and equivariant sites remain subsequent work.
