# Gluing finitely presented closed representatives

Workers 3483 and 286. Internal helper for arbitrary-base dynamic representability.

`exists_closed_finitelyPresented_of_openCover` applies to an arbitrary subgroup
functor of an actual group scheme. It assumes locality on every test scheme
and finitely presented closed representatives after base change to an open
cover of the base. Its conclusion gives a global closed representative whose
inclusion into the ambient group is locally of finite presentation.

The proof expresses subgroup membership as the published `schemeCondition`
on absolute scheme maps. Base change and the local all-test representations
give closed charts over the pullback cover of the ambient scheme. The published
closed-subscheme gluing theorem constructs a global closed scheme. Its pullback
to each chart is isomorphic to that chart by the published generic
`SmoothNormalizer.exists_iso_pullback_chart`. Local finite presentation of the
inclusion therefore descends on the ambient target cover.

Finally the published `representingHom` transfers the group structure from the
subgroup's point functor to this scheme. Its underlying map is the same closed
inclusion, so the geometric conclusions survive the transfer.

This is a derived internal lemma, generalizing the construction used in the
published smooth-normalizer and torus-subgroup gluing proofs. It introduces no
mathematical hypothesis beyond those in its Lean statement.
