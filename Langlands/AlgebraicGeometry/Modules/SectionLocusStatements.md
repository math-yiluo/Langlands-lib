# Comparison statements for a section's trivialization locus

This module states three comparisons for every scheme `X`, every actual module
`M : X.Modules`, and every global section `s`. The declarations return `Prop`;
this module does not prove them or add them as assumptions.

- `LocalStalkCriterion` says that the restriction of `sectionHom M s` to an
  open subscheme `U` is an isomorphism if and only if its map on the underlying
  abelian-group stalk is an isomorphism at every point of `U`.
- `TrivializationOpenInterior` identifies the underlying set of
  `trivializationOpen M s` with the interior of the stalk-frame locus
  `{x | IsStalkFrame M s x}`.
- `MaximalTrivialization` says that the section trivializes on `U` if and only
  if `U` is contained in `trivializationOpen M s`. In particular, taking `U`
  to be that open asserts trivialization on the whole union used to define it.

`SectionLocusComparison` is the conjunction of these three universally
quantified propositions. All schemes, modules and section values use the same
universe `u`, as in the definition module.

## Provenance and mathematical scope

These are derived sheaf-theoretic statements about the actual construction in
`Langlands.AlgebraicGeometry.Modules.SectionLocus`. Their mathematical basis is
that a morphism of sheaves of abelian groups is an isomorphism exactly when it
is an isomorphism on every stalk, and that restriction to an open subscheme
preserves those stalks. The pinned Mathlib supplies these facts as
`TopCat.Presheaf.isIso_iff_stalkFunctor_map_iso` and
`AlgebraicGeometry.Scheme.Modules.restrictStalkNatIso`, respectively. The
forgetful functor from scheme modules to abelian presheaves reflects
isomorphisms. The interior description and maximality then follow by the
complete lattice of opens. This is internal infrastructure; the source does
not separately state these three general-module formulations.

The motivation remains Stacks Project Lemma 17.25.10 (tag
[01CY](https://stacks.math.columbia.edu/tag/01CY)) and Definition 28.27.1 (tag
[01PS](https://stacks.math.columbia.edu/tag/01PS)), in the registered source
`stacks-invertible-picard-ampleness-2026-10-21`, directory SHA256
`2a0bbd01484fc7cef97110a88cf4b3e472574fbbb9469d037170744a1462f835`,
files `01CY.html` and `01PS.html`.

For an arbitrary module the stalk-frame locus need not itself be open, which
is why the statement uses its interior. No local freeness, invertibility,
residue-field nonvanishing comparison, tensor power or ampleness assertion is
included here. The identification with the source's line-bundle open `X_s`
still requires the additional line-bundle comparison.
