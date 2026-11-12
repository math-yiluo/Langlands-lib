# Reduction of the proper-field Picard scheme to the Picard stack atlas

Author: Worker 3462.

This internal assembly shows that, with the published Library results,
three open proper-field Picard targets follow from the single proposition
`FieldPicardStackAtlasStatement.{u}`. That proposition says that for every
field `k : Type u` and every proper `X : Over (Spec (CommRingCat.of k))`,
the actual relative line-bundle groupoid has a smooth surjective scheme
atlas locally of finite type over `k`, with scheme-represented point fibres
on the full slice. It remains an explicit hypothesis of every declaration
in this module. The module proves no atlas and is not a proof of any of
the targets below.

## Declarations

The first two conditional results are imported from
[FieldPicardSheafAlgebraicSpaceReduction](FieldPicardSheafAlgebraicSpaceReduction.md).

`fieldEtaleFppfClassSheaf_of_stackAtlas` derives
`FieldEtaleFppfClassSheafStatement.{u}`. The stack-atlas input and the published
`smoothAutomorphismEtaleAtlas` give a representable diagonal and an etale scheme
atlas for the actual etale Picard class sheaf. The published
`AlgebraicSpace.etaleAtlasFppfSheaf` then gives fppf descent on the full slice.

`fieldPicardSheafAlgebraicSpace_of_stackAtlas` derives
`FieldPicardSheafAlgebraicSpaceStatement.{u}`. It supplies the published
four-input reduction `fieldPicardSheafAlgebraicSpace_of_stackInputs` with
`RelativePicard.fieldPicardClassEqualizerImmersion`, the stack-atlas hypothesis,
`smoothAutomorphismEtaleAtlas`, and the preceding etale/fppf comparison.
The conclusion is algebraicity of the actual fppf Picard sheaf, a
closed-immersion diagonal, and a locally finite type etale surjective atlas.

`fieldPicardSheafRepresentability_of_algebraicSpace` derives
`FieldPicardSheafRepresentabilityStatement.{u}` from
`FieldPicardSheafAlgebraicSpaceStatement.{u}`. For each field and proper
scheme it destructures the three algebraic-space conclusions and applies
the published `AlgebraicSpace.separatedAddCommGroupSheafSchemeRepresentability`
(its published proof of the commutative specialization of Stacks Project
Lemma 79.10.2, Tag 0B8D: a separated group algebraic space locally of
finite type over a field is a scheme). The
sheaf is `RelativePicard.classSheaf X.hom`; its commutative group
structure is the published `RelativePicard.sheafPresheaf X.hom`, related
to the class sheaf by the published natural isomorphism
`RelativePicard.forgetSheafIso X.hom`. The conclusion is an actual scheme
over `Spec k`, separated and locally of finite type, that naturally
represents `RelativePicard.classSheafPresheaf X.hom` on every scheme over
`Spec k`.

`fieldPicardSheafRepresentability_of_stackAtlas` composes the last two
theorems: `FieldPicardStackAtlasStatement.{u}` implies
`FieldPicardSheafRepresentabilityStatement.{u}`.

`fieldPicardScheme` chooses, from that existence statement, an actual
scheme `P` over `Spec k` together with a chosen
`(RelativePicard.classSheafPresheaf X.hom).RepresentableBy P`.
`fieldPicardScheme_isSeparated` and
`fieldPicardScheme_locallyOfFiniteType` record that the chosen scheme is
separated and locally of finite type over `k`. All three keep the atlas
hypothesis explicit.

## Scope

The field, including imperfect fields, the proper scheme and the universe
`u` are arbitrary. All presheaves and representations concern the whole
slice over `Spec k`, including empty, nonreduced and non-quasi-compact test
schemes, and every section of the sheaves, including sections with no
global line-bundle representative. No projectivity, smoothness,
reducedness, connectedness, rational point or section, condition on
global functions, universal bundle, or representability of the Picard
sheaf is assumed. The proofs use only the standard axioms.

## Provenance and remaining obligations

No new external assertion or source is used: every step is an imported
Library result, cited above by Lean name. The single remaining input,
`FieldPicardStackAtlasStatement`, is the target of the separate proof task
`093deb76-b183-4d4d-816b-e79c0eedee5d`. A published proof of it would, by
this module, also prove `FieldEtaleFppfClassSheafStatement`,
`FieldPicardSheafAlgebraicSpaceStatement` and
`FieldPicardSheafRepresentabilityStatement`. Until then, none of these
three is proved here.
