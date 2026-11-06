# Actual root-system inheritance in cocharacter centralizers

This internal construction works over an arbitrary field in universe `u` with
the published actual character lattice, intrinsic Lie-weight relative roots,
normalizer/centralizer quotient, and rational root span. It supplies rational
reflection data for a represented cocharacter centralizer and proves the full
published `HasRelativeRootSystem` predicate for the intrinsic torus factor.

`HasRelativeRootSystem.nonempty_rationalReflectionData` chooses, for every
actual ambient root, an index of the ambient root pairing with that root vector.
The exact root-image equality supplies the index, and the exact Weyl-image
equality supplies an actual quotient element realizing its reflection. Its
rational coroot functional has self-evaluation two and integral evaluations on
all roots by the ambient crystallographic condition.
`rationalReflectionDataOfRootSystem` chooses these data.

`IsRelativeReflection.mem_dynamicCentralizer` proves that every normalizer
representative of an actual root reflection centralizes any cocharacter pairing
to zero with that root. The published `RelativeReflectionPairing` theorem gives
pairing invariance on the whole character lattice. The inverse Weyl-action
formula and character separation for the split torus identify the transformed
cocharacter with the original one. The published centralizer criterion then
gives membership in the actual subgroup functor on base-field points.

For `iL : T.toGrp ⟶ L`, `j : L ⟶ G`, and `iL ≫ j = i`, assume that `j`
represents the centralizer of `ζ ≫ i`. The intrinsic-root subset theorem defines
`centralizerRootSpanInclusion` as the ordinary inclusion into the ambient
rational root span; it sends each intrinsic root vector to the same ambient
root vector. Intrinsic roots pair to zero with `ζ`. Thus
`exists_centralizer_reflection_lift` lifts an ambient reflection representative
through the represented centralizer. Monomorphism reflects normalization, and
the published normalizer transport identifies its entire character action.
This lift and zero-pairing step require the locally finite type structure on
`L`; in the inheritance theorem smoothness of the connected reductive `L`
supplies it.

`centralizerRootSpanInclusion_relativeWeylAction` shows compatibility on every
vector in the intrinsic span by the equality of the rationalized character
actions. `nonempty_centralizerRationalReflectionData` composes each ambient
rational coroot functional with the span inclusion and uses the class of the
lifted normalizer as its reflection representative. Self-evaluation,
integrality, and the reflection formula on the entire intrinsic span are
inherited from the ambient data. `centralizerRationalReflectionData` chooses
these restricted data.

`HasRelativeRootSystem.of_cocharacterCentralizer` assumes ambient and
intrinsic connected reductivity, ambient `HasRelativeRootSystem`, and that the
same torus is maximal split in both groups. It chooses a generic intrinsic
cocharacter, obtains finiteness from the split-torus Lie-weight theorem, and
uses `hasTrivialPositiveRootStabilizer` for the actual intrinsic quotient.
`RationalReflectionAssembly` then supplies all clauses of the unchanged
root-system predicate, including equality of Weyl images and faithfulness.
There is no assumption identifying the intrinsic roots with every ambient
zero-pairing root.

`HasRelativeRootSystem.of_standardLeviTorusFactor` specializes this result to
the canonical torus factor in any closed connected reductive representative of
`standardLevi i ν J`. It retains `StandardCocharacterStatement`, ambient genericity
of `ν`, and `J ⊆ simpleRelativeRoots i ν`. The standard-cocharacter witness
identifies this Levi with a cocharacter centralizer; maximality transfers
through the closed subgroup. No dynamic Lie theorem or additional reflection
existence premise is required.

The provenance is internal and derived from the published modules named above,
`RootFactorPairTransport`, `StandardLeviStandardFamiliesProof`,
`PositiveRootStabilizerAveraging`, `DominantChamberMove`, and
`GenericCocharacter`. No new translation from original literature is claimed.
This construction supplies the intrinsic-root prerequisite for the finite
induced-cuspidal embedding argument. It does not prove the separate
representation-theoretic cuspidal splitting theorem or the host embedding target.
