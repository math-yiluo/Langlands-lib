# Prescribed-torus Levi descent from local dynamic presentations

This module adapts the descent and composition constructions of
`TorusLeviDynamicLocal`, `TorusLeviGluing` and `LeviCoverDescent`.

This internal derived construction combines the published dynamic structure
theorem, effective radical and Levi descent, and the prescribed-torus local
witness and gluing APIs. It introduces no external assertion. Its final
implication retains exactly one structure premise,
`RelativeTorusDynamicPresentationStatement`. It does not prove that premise
or claim an unconditional proof of `RelativeTorusLeviStatement`.

For any `EtaleTorusLeviData i t` in a reductive group scheme `G` over an
arbitrary scheme `S`, with the structure morphism of `P` affine,
`EtaleTorusLeviData.leviRepresentativeFromDynamic` constructs an actual
`LeviRepresentative` of the all-test subgroup descended from its local Levi
ranges. No global radical, universal radical statement, or dynamic structure
statement is an input.

The proof composes each local cocharacter of the prescribed commutative group
with its maps into `P` and `G`. These cocharacters present the given local
parabolics. Applying `radicalOfEtaleDynamicCover` to this same cover and the
proved `dynamicRelativeLevi` constructs an actual global relative unipotent
radical. Each local Levi supplies a local radical with an actual multiplication
isomorphism. The pullback of the constructed global radical is again a relative
radical because the cover maps are étale and `P` is affine over `S`.
`radical_range_eq_of_dynamic_parabolic` compares that pullback with the local
Levi's radical on every test scheme. Thus only radical comparison for the
displayed dynamic parabolics is used.

The local Levi inclusions represent their ranges, are closed and smooth, and
form a matching family by `isMatchingFromDynamic`. The construction
`leviRepresentativeOfEtaleCover` descends them using these properties, their
multiplication isomorphisms, and the radical range equalities just established.
The result has an actual group scheme, closed inclusion representing the
descended subgroup, and the full relative Levi predicate.

`torusLeviEtaleDataFromPresentation` assumes
`RelativeTorusDynamicPresentationStatement` and takes the original target's
data: a reductive `G`, a relative parabolic `i : P ⟶ G`, a commutative group
scheme `T` satisfying `RelativeTorus.IsTorus T.toGrp`, and a closed inclusion
`t : T.toGrp ⟶ P` satisfying `IsFibrewiseMaximalTorus t`. It chooses the
statement's étale cover and local cocharacters, then uses `witnessFromDynamic`
to construct the actual unique local Levis.

`torusLeviWitnessFromPresentation` uses affineness of the given parabolic,
the preceding data and descended representative, and
`witnessOfLeviRepresentative` to produce an actual `TorusLeviWitness t`.
The gluing API supplies all-test torus containment and equality of ranges for
every competing relative Levi containing the torus. Extracting the group,
inclusion, Levi property, containment and uniqueness proves
`relativeTorusLevi_of_dynamicPresentation`:

```text
RelativeTorusDynamicPresentationStatement.{u} →
  RelativeTorusLeviStatement.{u}.
```

All constructions are universe polymorphic. The base scheme and all target
hypotheses are unchanged; the implication's sole additional premise is stated
explicitly. That premise is proved in `TorusDynamicPresentationProof`
(`relativeTorusDynamicPresentation`), and the unconditional target is
`relativeTorusLevi` in `TorusLeviProof`.
