# Smooth scheme representatives of total Picard automorphisms

This internal construction retains the complete actual relative automorphism
data used in the smooth-automorphism hypothesis. The total presheaf
`atlasAutomorphismPresheaf` has on every `T : Over S` a map `a : T → U`
and an actual isomorphism from the pullback of `L` along `a` to itself.
`atlasAutomorphismProjection` records `a` as a full natural transformation.

`relativeAutomorphismIsoComparison` applies the generic groupoid
endomorphism-to-isomorphism comparison to the actual Picard pseudofunctor,
then precomposes with the same iterated-slice functor and restores the same
universe lift as the published relative automorphism presheaf. It thus
compares the whole presheaves with their actual restrictions.

`atlasAutomorphismRepresentation` uses a scheme representing that relative
presheaf. It lowers the lift, transports the representation across the
iterated-slice equivalence, represents the total presheaf by the domain,
and lifts back. The resulting `atlasAutomorphismSchemeIso` is on all
schemes over `S`. The projection comparison identifies its structure map
with the original representative's map to `U.left`.

Consequently `exists_atlasAutomorphismScheme` applies the given smooth
relative automorphism hypothesis at `U,L` to obtain a smooth actual scheme
over `U` representing the entire total automorphism presheaf. This step
asserts no surjectivity, quotient construction, or representation of the
Picard class sheaf. The identification with the kernel of the two arrow
endpoints remains a separate obligation.
