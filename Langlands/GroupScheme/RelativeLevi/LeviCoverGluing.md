# Gluing local Levi decompositions over an étale cover

This derived construction combines
`RelativeLevi.radicalRepresentativeEtale` from
`RelativeLevi.UnipotentRadicalGluing` with
`RelativeLevi.leviRepresentativeOfEtaleCover` from
`RelativeLevi.LeviCoverDescent`. Its provenance is these internal constructions
and the existing relative Levi predicate; it introduces no external
mathematical assertion.

`leviRepresentativeEtale` works in every universe, over an arbitrary base
scheme `S`, for an ambient group scheme `P` affine over `S`. It takes an
arbitrary étale covering family and, on each member, actual maps
`lᵢ : Lᵢ → Pᵢ` and `rᵢ : Uᵢ → Pᵢ`. The inputs assert closedness of
`lᵢ`, smoothness of `Lᵢ`, the full existing relative unipotent radical
property for `rᵢ`, and isomorphy of the actual Levi-first multiplication
`Lᵢ × Uᵢ → Pᵢ`. The local Levi ranges must form a matching family, and
the local radical ranges must form a matching family, in the all-test
sense of `SubgroupFunctor.CoverDescent.IsMatching`.

The result is an actual `LeviRepresentative` of
`SubgroupFunctor.CoverDescent.subgroup` applied to the local ranges of
`lᵢ`. It includes a global group scheme `L`, an inclusion `l : L → P`,
closedness, representation of that descended subgroup on every test
scheme, and `IsRelativeLeviSubgroup l`.

The proof first glues the matching radicals to an actual global closed
representative with the full relative radical certificate. Representation
of the descended radical functor and its recovery on each cover member
give equality between the pulled global radical range and each local
radical range. Closedness makes each `lᵢ` a representative of its own
range. These data feed `leviRepresentativeOfEtaleCover`, which constructs
the actual global Levi representative and descends its smoothness and
multiplication property.

There is no assumed global radical in this construction. Its remaining
inputs include both matching conditions and the specified local
factorizations. It does not construct prescribed-torus local
factorizations, prove their compatibility, establish torus containment,
or prove uniqueness. The unchanged `RelativeTorusLeviStatement` remains a
separate proof obligation.
