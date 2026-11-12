# The actual Picard-zero restriction of an ambient universal family

Worker 603.

This derived construction takes an actual rigidified family on an abelian
scheme and constructs an open parameter scheme and its actual restricted
rigidified family. If the original family is universal for all rigidified
line-bundle classes, the restriction satisfies the existing
`IsUniversalPicardZero` predicate. The construction works over an arbitrary
base scheme in universe `u`.

The final lemma
`Langlands.AbelianScheme.fieldDualSchemeExistence_of_rigidifiedRepresentability`
has the explicit hypothesis
`FieldRigidifiedPicardRepresentabilityStatement.{u}` and concludes the exact
published `FieldDualSchemeExistenceStatement.{u}`. This module does not
prove ambient representability or unconditional field dual existence.

## Construction of the open parameter

For `A : AbelianScheme S`, `P : Over S`, and
`L : RigidifiedFamily A P`,
`exists_geometricPicardZeroOpenLocus` obtains an open subset of `P.left`
with the geometric-point criterion from the published theorem
`exists_isPicardZeroFamily_relativePullback_iff_of_fibreCriterion`.
Its fibrewise input is supplied, for every abelian scheme `G` and line
bundle `M`, by the actual open set `mumfordTrivialLocus G M` and
`isTranslationInvariant_fibreLineBundle_iff G M K t`. These declarations
are imported from `Langlands.AbelianScheme.MumfordTrivialLocus`.

The theorem `isPicardZeroOpenLocus_of_geometricPoints`, applied with the
published `picardZeroGeometricDetection`, converts that geometric-point
criterion into `IsPicardZeroOpenLocus A L U`. Consequently, for every
test scheme `T : Over S` and every morphism `h : T ⟶ P`, the actual
pullback class of `L` is Picard-zero if and only if the range of `h.left`
is contained in `U`. No restriction on reducedness, quasi-compactness,
or quasi-separatedness of the test scheme is introduced.

`geometricPicardZeroOpenLocus A L` chooses one such open subset using
classical choice. Its specification is
`geometricPicardZeroOpenLocus_spec`. This is a chosen locus; the module
does not assert equality with a particular connected component.

`geometricPicardZeroParameter A L` is the existing
`openLocusParameter P U`: its underlying scheme is `U.toScheme`, and
its structure morphism is the open inclusion followed by `P.hom`.
`geometricPicardZeroFamily A L` is
`restrictedRigidifiedFamily A L U`, the actual relative rigidified
pullback along that open inclusion.

## Universality and the field reduction

`geometricPicardZeroFamily_universal` applies the published
`restrictedRigidifiedFamily_universal` to ambient universality and the
proved open-locus specification. This retains unique classification
on every test scheme. In that imported argument, ambient universality
classifies a Picard-zero class by a unique map into `P`; the locus
criterion forces its image into `U`. The universal property of the
open immersion gives a unique lift, and the actual rigidified
pullback composition law proves that this lift classifies the original
class. This applies to nonreduced test schemes as well.

`hasDualScheme_of_rigidifiedUniversal` packages the actual open
parameter, restricted family, and universal-property proof into the
existing `HasDualScheme A`.

Finally, `fieldDualSchemeExistence_of_rigidifiedRepresentability`
introduces an arbitrary field `k : Type u` and abelian scheme over
`Spec k`. The explicit representability hypothesis supplies `P`, `L`,
local finite type, and ambient universality. The proof uses the
constructed restriction and ambient universality; local finite type
is unnecessary for this construction. No perfectness,
algebraic-closedness, projectivity, or extra theorem hypothesis is
added to the published field target.

## Provenance and remaining obligation

This is an internal composition and choice construction from published
Library results, following the proof route already implemented in
`FiniteTypePicardZeroOpenLocusProof` without its unused restriction on
the base. No unreviewed draft is used. The parameter and universal
bundle are obtained by actual open restriction, rather than by a
replacement class functor or a bijection only on geometric points.

The source motivation is Edixhoven, van der Geer and Moonen,
*Abelian Varieties*, preliminary draft, registered as
`edixhoven-vandergeer-moonen-abelian-varieties-draft`, SHA-256
`81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`.
Paragraph (6.2), printed pp.88–89/PDF pp.92–93, describes the actual
rigidified universal property. Chapter VI §3, printed p.95/PDF p.99,
invokes ambient Picard representability. Definition (6.19), printed
p.96/PDF p.100, restricts the Poincare bundle to the dual variety, and
Corollary (7.22), printed p.106/PDF p.110, motivates the geometric
translation-invariance criterion. The implemented locus argument uses
the Library's published Mumford criterion and geometric detection;
it does not reconstruct the source's identity-component proof.

The remaining hypothesis is the exact full rigidified representability
statement. Its separate proof must provide a scheme and actual universal
rigidified bundle over arbitrary fields, on all test schemes, without
assuming dual existence. This conditional construction is a prerequisite
for the parent proof and does not satisfy its unconditional acceptance
condition by itself. It supplies no group structure, properness,
smoothness, projectivity, or dimension assertion for the new parameter.
