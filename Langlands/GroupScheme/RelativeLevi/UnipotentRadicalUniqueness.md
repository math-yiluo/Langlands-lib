# Uniqueness of relative radicals from etale-local dynamics

This internal construction proves uniqueness of two supplied relative unipotent
radicals whenever the ambient parabolic has dynamic presentations on an arbitrary
etale cover of the base. It retains `DynamicRelativeLeviStatement` as an explicit
hypothesis. The cover and its presentations are also supplied; this module does
not construct them or prove general radical existence.

`radical_range_eq_of_dynamic_parabolic` first treats a supplied representative
`iP : P → G` of `Dynamic.parabolic χ` in a reductive group. The ambient composites
of the two radicals represent `Dynamic.unipotent χ` by
`isRepresentedBy_unipotent_of_relativeRadical`. Uniqueness of representatives gives
an isomorphism of their source groups commuting with their ambient composites.
Monicity of `iP` cancels it from that identity, giving compatibility inside `P`.
Invariance of the image under a source isomorphism proves equality of the two
subgroup functors on every relative test scheme.

`radical_range_eq_of_etale_dynamicCover` assumes an affine structure morphism for
`P`, a reductive `G`, a homomorphism `iP : P → G`, an etale cover, and for every
cover member a cocharacter dynamically representing the actual base change of
`iP`. Reductivity pulls back along every cover map. The full relative radical
certificates pull back along the etale maps by `baseChange_etale`, retaining
closedness, smoothness, all-test normality and the geometric-fibre radical
condition. The preceding local result identifies the two actual pulled-back
ranges. `SubgroupFunctor.range_eq_of_baseChange_etaleCover` descends their
equality. Closedness of the original radical inclusions supplies the required
monomorphisms. No quasi-compactness of the cover, reducedness or noetherianity of
the base, or restriction to geometric points is used.

`radicalIsoOfEtaleDynamicCover` packages that equality as an actual isomorphism
`e : N ≅ U`, together with `e.hom ≫ r = n` for the two inclusions. Monicity of `r`
makes any compatible homomorphism unique.

The result is derived internally from the published meanings of the relative
radical, reductivity, represented subgroup functors and etale base change, and
the supporting dynamic identification and cover comparison constructions. The
explicit dynamic theorem and local presentations still need to be discharged in
a proof of the unchanged global existence and uniqueness statement.
