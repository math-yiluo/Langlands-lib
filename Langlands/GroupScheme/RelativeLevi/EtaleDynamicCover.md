# Etale dynamic covers from pointwise presentations

This internal construction turns supplied pointwise etale dynamic presentations
of a group-scheme homomorphism into an actual etale cover. It also applies the
conditional cover uniqueness construction to two supplied relative radicals.
The base scheme and universe are arbitrary.

`etaleDynamicCoverOfPointwise` takes `iP : P → G` and, for each point `s` of the
base, the existence of a scheme `T`, an etale map `f : T → S`, a point above `s`,
and a cocharacter of the pulled-back ambient group whose dynamic parabolic is
represented by the actual pullback of `iP`. These presentations concern every
relative test scheme through `IsRepresentedBy`.

Classical choice selects one such neighbourhood and cocharacter for each base
point. The family is indexed by the points of `S`, so its index type remains in
the same universe. Each selected map is etale, and the selected point above `s`
proves that the family covers `s`. `Scheme.Cover.mkOfCovers` packages the family
as an etale cover. The construction returns the cover together with an
existential dynamic presentation of each member. This also handles the empty
base: the family is then empty and is vacuously a cover.

`radical_range_eq_of_pointwise_dynamic` additionally assumes reductivity of `G`,
affineness of `P` over the base, `DynamicRelativeLeviStatement`, and full relative
radical certificates for two supplied inclusions into `P`. It applies
`radical_range_eq_of_etale_dynamicCover` to the selected cover and proves equality
of the two ranges on every test scheme.

`radicalIsoOfPointwiseDynamic` uses the same inputs and returns an actual
isomorphism `e : N ≅ U` with `e.hom ≫ r = n`. It applies
`radicalIsoOfEtaleDynamicCover` to the selected cover. Monicity of the closed
inclusion `r` implies uniqueness of a compatible homomorphism.

The provenance is internal: the construction uses classical choice, the
published scheme-cover interface, and the conditional relative-radical
comparison. It supplies neither the pointwise dynamic presentations nor a proof
of the dynamic relative Levi theorem. Radical existence remains a separate
obligation.
