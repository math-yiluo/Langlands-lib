# Separated algebraic spaces with an etale structural atlas are schemes

`Langlands.AlgebraicGeometry.AlgebraicSpace.SeparatedEtaleSchemeStatement.{u}`
states that an algebraic space `X` over an arbitrary scheme `S` is
represented by an actual scheme over `S` if its diagonal is a closed
immersion and it has an actual etale surjective scheme atlas
`U → X` for which `U → S` is etale.

The atlas condition is exactly
`HasAtlasProperty (@AlgebraicGeometry.Etale) X`. In particular, it does
not assume that `X → S` is representable. The existing presheaf predicate
`IsEtale` includes representability after every scheme base change and
would assume the missing conclusion if used for the structural map.
All presheaves, atlases and representing schemes retain the existing
universe conventions and all scheme tests, including nonreduced tests.
There is no Noetherian, affine, quasi-compact or group hypothesis.

This is the etale specialization of the schemehood theorem for separated
locally quasi-finite algebraic spaces over a scheme, Stacks Project,
Proposition 67.50.2, Tag 03XX. An etale structural atlas makes the
structural morphism locally quasi-finite by the etale chart criterion;
the conclusion of that proposition is scheme representability. The
specialized atlas formulation is internal packaging for the clopen
relative identity-component quotient. This module states the
proposition only and supplies no proof of schemehood.

Source read in full, including the single displayed comment: registered
source `stacks-mono-lft-schemehood-2026-11-02`, SHA-256
`dcc9a958ea2cec87994a4191d6e3969d1c0f4836266a827082cf9ce42c249df3`,
retained HTML and text page `03XX`, Proposition 67.50.2. Comment 688
corrects the wording of the ambient base and does not change the
mathematical assertion. No source-specific errata note was present in
the checked Library errata directory.
