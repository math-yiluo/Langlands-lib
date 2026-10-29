# Pullback preservation of actual smooth-family witnesses

`Langlands.AbelianScheme.smoothFamilyPullback` proves the published
`Langlands.AbelianScheme.SmoothFamilyPullbackStatement.{u}`.
It quantifies over arbitrary `S : Scheme.{u}`, `A : AbelianScheme S`,
`T U : Over S`, `h : T ⟶ U`, and `L : RigidifiedFamily A U`.

The proof keeps the original smooth parameter, its geometric properties and
both marked points. It pulls the witness bundle back along the identity on
the parameter and the canonical comparison of geometric fibres. The
endpoint restrictions commute with that map, by the two pullback projection
identities. The proof uses `LineBundle.pullbackComp` to obtain the resulting
restriction isomorphisms, pulls back both old endpoint isomorphisms, and
uses `LineBundle.pullbackTrivialIso` at the trivial endpoint.
The product map is constructed by `pullback.lift`; its first projection is
the old parameter projection, and its second is the abelian-scheme
projection followed by the given morphism over the base. Equality of the
two composites from an endpoint follows by `pullback.hom_ext`. These
constructions and the fixed-field pullback lemma are private helpers in
this module.

For each algebraically closed field and each point of the new test scheme,
the hypothesis supplies the original witness at the composite point of the
old test scheme. `GroupScheme.fibreComparison` supplies the fibre map.
`fibreComparison_lineBundleIso`, with `fibreComparison_fst`, identifies the
pullback of the old fibre bundle with the new fibre bundle of the actual
`RigidifiedLineBundle.relativePullback`. Isomorphism invariance of the
smooth-family predicate finishes the proof.

The same parameter retains smoothness, separatedness, local finite type,
quasi-compactness and geometric integrality. No inverse of the fibre
comparison is used. The conclusion concerns the existing relative
pullback functor with its existing rigidification, which is forgotten only
as prescribed by the unchanged smooth-family predicate.
There is no quasi-separatedness, reducedness or noetherianity assumption
on the base or tests, and no hypothesis on `h` beyond being a slice
morphism. The proof adds no comparison, representability, normalization,
descent, openness or gluing result.

This is derived internal functoriality of the existing explicit
smooth-family predicate. Its provenance is the published
`SmoothFamilyPullbackStatement` and `SmoothFamilyAlgebraicTriviality`
interfaces; it requires no further literature assertion.
