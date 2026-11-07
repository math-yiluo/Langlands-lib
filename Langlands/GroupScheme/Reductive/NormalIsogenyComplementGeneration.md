# Normal-isogeny complements from almost-simple generation

This internal construction removes the separate perfectness premise from
`NormalIsogenyComplementReduction` using the full-derived argument in
`Derived/AlmostSimplePerfect`. The only structural premise retained is
`SemisimpleAlmostSimpleGenerationStatement`, at the same arbitrary universe
as the conclusion.

`semisimpleNormalIsogenyComplement_of_generation` concludes the exact existing
`SemisimpleNormalIsogenyComplementStatement`. It supplies the preceding
two-premise assembly with the stated generation input and with
`algebraicallyClosedSemisimplePerfect_of_almostSimpleGeneration` applied to that
same input. Thus it covers every field and characteristic. The original-field
full-derived-centralizer construction, comparison after algebraic closure,
descent, and finite-full-centre multiplication are those implemented in
`NormalIsogenyComplementReduction`.

`semisimpleNormalIsogenyComplementOfGeneration` returns actual complement data.
Given a semisimple actual group scheme over any field and a smooth connected
closed normal inclusion, it chooses a commuting closed normal complement over
that original field. The returned properties include semisimplicity of the
given subgroup, chosen complement, and their actual product, and
`IsCentralIsogeny` for their actual commuting multiplication. Normality and
commutation retain every test scheme, and central isogeny uses the full
scheme-theoretic kernel. The constructor applies the existing two-premise data
constructor with the same derived perfectness proof.

The generation premise remains unproved here. This supporting construction
does not complete the unconditional normal-complement proof task. Its
provenance is the internal composition of the named results, with no new
literature assertion.
