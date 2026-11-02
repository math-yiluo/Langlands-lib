# Renard II.2.3: intrinsic module-sheaf gluing and all opens

This unit is derived from the actual module-sheaf category in
`Langlands.Sheaf.Renard.RingedBasisModules`, the published intrinsic
`SheafCondition.family` in `BasisSheaf`, and the published `allOpenBasis`
and `allOpen` in `GermSectionSheaf`. Its original context is David Renard,
*Représentations des groupes réductifs p-adiques*, French version dated
9 July 2026, II.2.3 “Faisceau de modules”, printed p.38 / PDF p.44;
the category is used in II.2.5, printed pp.38–39 / PDF pp.44–45.
The registered source is `renard-2026-representations-groupes-reductifs-padiques`,
SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The core unit records the source and older-edition corrections audit.

`BasisModuleSheaf.unique_gluing` applies `SheafCondition.family` to the
original additive presheaf and its stored sheaf proof. Its compatibility
hypothesis compares the original restrictions on every smaller common
basis open. Its conclusion is an actual unique section of the original
module on the covered open, with a restriction equation for each original
cover index. The space universe `u`, ring universe `r`, section universe
`v`, and cover-index universe `w` remain independent. In particular, the
theorem accepts repeated opens and index types larger than the basis.
The underlying published proof deduplicates to a set cover and recovers
every original cover member.

`restrict_self` and `restrict_comp` reuse the original additive-presheaf
restriction laws on the same module elements. `sections_ext` obtains the
compatible family of restrictions of one section using `restrict_comp`,
then applies uniqueness of gluing to both sections.

`AllOpenModuleSheaf S` is a transparent abbreviation for the very same
`BasisModuleSheaf S` with basis `allOpenBasis X`.
`AllOpenModuleSheaf.sections`, `restrict` and `app` evaluate the original
module presheaf and its actual linear morphisms at `allOpen U`.
Their recovery formulas are definitional equalities. `restrict_smul` is
the original semilinearity equation along the actual ring restriction.
`AllOpenModuleSheaf.unique_gluing` applies the basis theorem to an arbitrary
family of actual opens, using the literal inclusion and point-covering
conditions. Each smaller basis open is its underlying actual open, so the
supplied compatibility proves precisely the required condition.
`allOpenModuleSheafEvaluation` is the existing evaluation functor at
`allOpen U`, with definitional object and morphism formulas.
For a genuine ring sheaf, take `S : RingedBasis (allOpenBasis X)` and use
`AllOpenModuleSheaf S.ring`, equivalently `S.ModuleSheaf`; the ring-sheaf
proof remains in that explicit ringed-basis parameter.

These are internal formal interfaces and the arbitrary-topological-space
generalization of Renard's definition in a chapter on totally disconnected
spaces. No separation, intersection-closure, compactness, size,
countability, dimension or nonemptiness assumption is used. Empty covers,
empty opens and empty spaces are included. The all-open category is an
instantiation of the supplied basis construction.

Worker 633 implemented this unit, reusing the published basis framework
and the core interface designed with Worker 6's source audit. The
module-structure adapter is a separate unit by Worker 1203. Locally
constant scalar constructions and actions, scalar restriction,
basis-change equivalences and all II.2.5 equivalences remain separate
successors.
