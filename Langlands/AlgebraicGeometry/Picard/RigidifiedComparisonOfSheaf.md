# The canonical Picard comparison from the rigidified sheaf condition

For any morphism of schemes with a section, this internal result assumes that
the actual relative rigidified line-bundle class presheaf is an fppf sheaf.
It proves that the specified canonical natural transformation
`toPicardSheaf` is an isomorphism to the underlying set presheaf of the actual
abelian-group relative Picard sheaf.

The proof uses the published local comparison of actual classes.
`forgetClassNatTrans_isLocallyInjective` applies componentwise injectivity of
forgetting rigidification. The published local surjectivity theorem supplies
the other direction locally in the fppf topology. The ordinary class
sheafification unit is locally injective and locally surjective by Mathlib's
general sheafification results. Both properties are preserved by composition,
so they hold for the specified `toClassPicardSheaf`.

The sheaf hypothesis makes its source a sheaf, and its target is the actual
set-valued Picard sheaf by construction. Mathlib's theorem that a locally
bijective morphism between sheaves of types is an isomorphism proves
`toClassPicardSheaf_isIso_of_isSheaf`. Composing `toPicardSheaf` with the
forward map of the canonical comparison `RelativePicard.forgetSheafIso`
gives `toClassPicardSheaf`. Cancelling this isomorphism proves
`toPicardSheaf_isIso_of_isSheaf`.

`picardSheafIsoOfSheaf` packages that very natural transformation as an
isomorphism. Its forward map equals the specified `toPicardSheaf` by
definition, as recorded by `picardSheafIsoOfSheaf_hom`. Thus the construction
preserves the published component formulas and pullback naturality.

This is a derived consequence of the Library's actual forgetful comparison
and canonical group/set sheaf comparison, together with Mathlib's local
bijectivity results. It imposes no quasi-compactness, quasi-separatedness or
structure-sheaf condition, but retains sheafness of the rigidified presheaf
as an explicit hypothesis. It does not establish that hypothesis or prove
`RigidifiedFppfComparisonStatement` without it.
