# Extending Picard-zero classification from quasi-separated tests

`Langlands.AbelianScheme.picardZeroQuasiSeparatedExtension` proves exactly
`Langlands.AbelianScheme.PicardZeroQuasiSeparatedExtensionStatement.{u}`,
imported unchanged from
[`PicardZeroQuasiSeparatedExtensionStatement`](PicardZeroQuasiSeparatedExtensionStatement.md).
For every quasi-separated `S : Scheme.{u}`, abelian scheme `A` over `S`,
parameter `P : Over S`, and actual rigidified family `L : RigidifiedFamily A P`,
`IsUniversalPicardZeroOnQuasiSeparatedTests A L` implies the existing
`IsUniversalPicardZero A L`. The conclusion classifies every test scheme in
universe `u`, including nonreduced and non-quasi-separated tests. The parameter
scheme is arbitrary.

## Pullback and comparison of local parameter maps

The proof uses the published actual rigidified relative pullback and class
quotient. The private lemma `classesPullback_comp` obtains the composition
identity from `RigidifiedLineBundle.classPresheaf` and
`RigidifiedModule.pullbackCoherence`. The private `classifyingMap_comp`
specializes the published classification-map composition identity to the same
coherence.

`local_parameter_maps_agree` compares two locally classifying parameter maps
on a quasi-separated common test. The published theorem
`Langlands.AbelianScheme.picardZeroPullback` supplies a Picard-zero class on
that common test. Pullback composition and the classification-map identity
show that both parameter maps classify this same class. Restricted uniqueness
identifies them. The geometric Picard-zero predicate is the existing
translation-invariance condition; its pullback stability is supplied by the
imported proof.

## Gluing a parameter map

`existsUnique_parameter_map_on_cover` works with any
`T.left.OpenCover.{u}` whose members are quasi-separated. Restricted
universality supplies a parameter map on each member. Each pairwise scheme
pullback is quasi-separated, because its first projection is an open immersion
into a quasi-separated member. The comparison lemma on this overlap proves
the compatibility equation for Mathlib's `Scheme.Cover.glueMorphisms`.

The resulting morphism of schemes lies over `S`: the required equation holds
after composition with every cover map, so `Scheme.Cover.hom_ext` proves it
globally. The glued map therefore defines `h : T ⟶ P`. Its restrictions are
the chosen local parameter maps, and pullback coherence gives equality of its
classified class with the prescribed class on every cover member. Any second
parameter map satisfying these local equations has the same restrictions by
restricted uniqueness. Coverwise morphism extensionality then identifies the
two global parameter maps.

## Equality of global classes and the exact target

The final theorem keeps `IsPicardZeroFamily A L` from the premise and applies
the gluing lemma to the affine cover of an arbitrary test `T`. Its members
are quasi-separated. The published unconditional theorem
`Langlands.AbelianScheme.rigidifiedClassesZariskiSeparated` identifies the
global class classified by the glued map with the given class, using the local
equations just proved. This imported theorem establishes compatibility and
gluing of actual rigidified isomorphisms; the present proof applies its exact
class-separatedness conclusion. Any globally classifying parameter map
satisfies the same local equations, so the uniqueness from the gluing lemma
proves global uniqueness.

This is an internal proof of the derived local-to-global interface described
in the statement's paired Markdown. It makes no additional literature claim.
The proof adds no premise concerning gluing, global functions, dual schemes,
or all-test universality. It retains the base hypothesis of the named target,
although the internal gluing argument does not use that hypothesis. No
quasi-compactness, reducedness, noetherianity, projectivity, or
quasi-separatedness condition is imposed on `P`. The argument extends a
supplied universal family and constructs no dual scheme or universal family.
