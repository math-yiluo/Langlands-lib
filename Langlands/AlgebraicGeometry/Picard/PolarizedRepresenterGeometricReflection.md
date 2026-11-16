# Geometric reflection for a supplied global polarized representer

Let a presheaf on schemes over an affine base have a supplied global scheme
representer. Suppose that, after a flat surjective change to an affine base,
its restriction has a supplied smooth proper scheme representer and that a
coherent actual presheaf line bundle has ample universal bundle there. Then
the supplied global representer is smooth and proper and its universal line
bundle is ample. The scheme universe and presheaf-value universe remain
independent. No sheaf hypothesis is needed once global representability is
supplied.

`localRepresenterComparison` constructs the canonical slice isomorphism
between the base change of the global representer and the supplied local
representer, by uniqueness of representing objects. The accompanying theorem
`geometricReflection_of_representable` first transports smoothness and
properness along the underlying scheme isomorphism. These properties descend
by the published fpqc descent instances, since a morphism between affine
schemes is quasi-compact. Ampleness transfers to the base-changed global
universal bundle by independence of the supplied representer and the actual
universal-bundle base-change comparison. The arbitrary-affine flat-surjective
ampleness reflection theorem then applies to the original universal bundle.

The provenance is internal: all geometric properties are deduced from the
published descent instances, actual line-bundle comparisons, and the new
flat affine-base ampleness reflection proof. The theorem retains global
representability as an explicit premise and does not construct the global
representer or prove the whole polarized representability descent statement.
