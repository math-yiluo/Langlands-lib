# Fibrewise centrality from central rigidity

This internal reduction retains the published
`MultiplicativeTypeCentralRigidityStatement` as an explicit premise.
It proves the arbitrary-base detection clause of SGA 3, Exposé IX, Théorème
5.6(b) from that premise, and constructs an open centralizing neighbourhood
above one central residue fibre.

`hom_eq_of_central_fibres` applies the local equality clause of central
rigidity at every base point, to two homomorphisms with equal central residue
fibres. The resulting open immersions form pointwise fppf neighbourhoods.
The published `hom_ext_of_pointwise_fppf_baseChange` glues these equalities.

`baseChange_eq_of_evaluate_eq` cancels the actual direct/iterated pullback
comparison isomorphisms in `HomScheme.evaluate`. It translates equality of
relative evaluations into equality of their iterated base changes.

For a homomorphism `i : H → G`, `conjugationFamily_fibre_eq` assumes centrality
of every residue fibre of `i`. A map from the spectrum of a field factors
through the residue field of its image, so the corresponding field-valued
pullback is central. The published evaluation law for the actual
`HomScheme.conjugationFamily` then reduces fibre equality to the fact that
inner automorphisms fix a central homomorphism.

`conjugationFamily_eq_of_fibres` applies `hom_eq_of_central_fibres` over an
arbitrary parameter scheme to the constant family and its conjugation by a
group-valued parameter. The hypotheses on the source and ambient group
persist under pullback. Thus the two families agree globally.

`commute_of_conjugationFamily_eq` evaluates this equality on the actual
pullback of an `H`-point. The inner automorphism acts by conjugation. The
base-point comparison transfers the resulting group equation back to the
original test scheme, giving commutation of the image point and the
conjugator. `isCentral_of_fibres_of_centralRigidity` applies this after every
restriction of every test scheme, giving exactly `IsCentral i`.

The last part needs just one central residue fibre.
`isCentral_constantFamily_fibre` uses naturality of scheme residue fields to
identify the iterated fibre at a parameter point with a further base change
of the original fibre at its image.
`conjugationFamily_fibre_eq_of_isCentral` then compares the constant and
conjugation families at that point. Central rigidity gives
`exists_centralizingOpenAt`: for every point `t` of the underlying scheme of
`G` whose image fibre is central, there is an open neighbourhood of `t`
where universal conjugation equals the constant family.

`centralizingOpenAt` chooses such an open neighbourhood.
`mem_centralizingOpenAt` records that it contains `t`, and
`centralizingOpenAt_eq` gives equality of the two actual families after
base change along its inclusion. This construction does not assert that
the open is canonical or equals the full centralizer.

Throughout, `H` is of multiplicative type and `G → S` is locally of finite
presentation, quasi-compact and quasi-separated. There is no noetherian
hypothesis on the base or universal product, and no connectedness,
separatedness, or monomorphism assumption. The central-rigidity statement
remains an explicit premise. The module does not prove that premise, the
connected-fibre propagation needed for 5.6(a), or the normal-subgroup clause
5.5. Its proof is an internal derivation from the named Library constructions.
