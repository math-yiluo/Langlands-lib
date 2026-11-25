# The scheme of Borel subgroups of a reductive group scheme

`Langlands.GroupScheme.relativeBorelScheme` proves the published
`RelativeBorelSchemeStatement.{u}` for every universe `u`. For an arbitrary
scheme `S` and reductive group scheme `G` over `S`, it gives a smooth proper
`S`-scheme `M` with a universal relative Borel subgroup of `G_M`. Every
relative Borel subgroup `i` of `G_T`, for any `S`-scheme `T`, has a unique
classifying morphism `a : T ⟶ M` over `S` such that evaluation of the
universal subgroup along `a` equals `SubgroupFunctor.range i`.
[Statement and source comparison](BorelSchemeStatement.md)

The Lean proof applies `relativeBorelScheme_of_parabolicScheme` to
`relativeParabolicScheme.{u}`. The latter supplies the smooth proper scheme
of parabolic subgroups and its universal family. The reduction uses
`relativeBorelLocusClopen` to restrict this family to the open and closed
locus where the residue fibres are Borel subgroups.
[Parabolic representability](ParabolicSchemeProof.md)
[Borel reduction](BorelSchemeReduction.md)
[Clopen locus](BorelLocusProof.md)

A relative Borel subgroup gives a unique classifying morphism to the parabolic
scheme. The evaluation equality implies that the image of this morphism lies
in the Borel locus, so it factors uniquely through the open subscheme and
retains the evaluation equality there. The open immersion gives smoothness
over `S` by composition, and closedness makes the immersion proper, giving
properness over `S` by composition. This is the construction used in Conrad,
*Reductive group schemes* (2014), proof of Theorem 5.2.11(3), p. 158
(`conrad-2014-reductive-group-schemes`).
[Universal family construction](BorelRepresentation.md)
