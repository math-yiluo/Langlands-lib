# Renard II.2.1: intrinsic restriction of all-open sheaves

Worker 633 implements the restriction proof. Worker 6 supplied the original
source audit, focused interface and refinement route.

The governing source is Renard, *Représentations des groupes réductifs
p-adiques*, French version dated 9 July 2026, final paragraph of II.2.1,
printed p.37 / PDF p.43. The registered source is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
This paragraph restricts an all-open sheaf to a chosen basis. The proof here
supplies the intrinsic refinement and gluing argument for that restriction.
The complete original page and the supplementary 2010-edition corrections
`renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
PDF pp.2–3, were read. The nearby cover-index and adjunction corrections
leave this restriction operation unchanged.

`allOpen_family_separated` constructs the compatible family of restrictions
of one section and applies uniqueness in actual all-open gluing to both
sections. `basisRefinement_covers` covers an arbitrary open by every chosen
basis member contained in it, using `OpenBasis.exists_subset` for coverage.
Consequently `allOpen_sections_eq_of_basis_restrictions` determines
all-open sections from their restrictions to those basis members.

`basisCompatible_allOpenCompatible` applies this separation result to the
two sections on each arbitrary all-open overlap. Their restrictions agree
by restriction composition and the supplied chosen-basis compatibility.
No intersection needs to be a basis member. The actual all-open gluing law
then gives existence and uniqueness on the original target open. This is
`rawBasisRestriction_familySheafCondition`, for every independent cover
index universe, and hence the literal `rawBasisRestriction_sheafCondition`.
The same argument includes empty covers and empty opens.

`sheafBasisRestriction` packages this proof in the existing full sheaf
subcategory. Its underlying normalized and raw functors, sections,
restrictions and morphism components are the original precomposition
restriction. The forgetful comparisons are literal functor equalities.
The supplied topology, arbitrary basis and original value universe are
preserved. This packaging is internal generality of the source operation.

`rawAllOpenGerm_restrict_eq` and `allOpenGerm_restrict_eq` identify extension
followed by restriction with the published chosen-basis germ functors.
These are definitional equalities: both use exactly `GermSections F U.obj`
on a basis member, the original `germRestriction` along inclusions, and
the original `germSectionsMap` on input transformations. Both constructions
always use stalks of the same original input on the same original basis.
The different target basis has only changed where those families are
evaluated.

`rawAllOpenGermRestrictionIso` and `allOpenGermRestrictionIso` are the
identity natural isomorphisms under these definitional identifications.
For raw and normalized inputs the module exposes the actual section,
restriction and morphism-component formulas. Both hom and inverse have
the identity additive-group morphism at every basis member, with
pointwise identity evaluations. Their restriction compatibility and
naturality equations are proved directly for `germRestriction` and
`germSectionsMap` by reflexivity.

Restriction keeps the original independent value universe `v`. Germ
extension and both comparisons take values in `max u v`; no relation
between `u` and `v` is imposed. Raw inputs require no normalization or
separation hypothesis. Separation above is used only for the actual
all-open sheaf being restricted. Arbitrary supplied topologies, bases,
index universes, empty spaces, empty opens and empty covers remain
allowed. No intersection closure, local compactness, total disconnectedness,
countability or nonemptiness is used. This raw-input and universe
generality is internal packaging supported by the construction.

This module asserts only the restriction direction and the comparison of
the same germ families after extension and restriction. It supplies no
equivalence of sheaf categories, no comparison between stalk colimits on
different bases, no sheaf-unit invertibility, and no compact-section,
scalar-module or support result. Those require separate arguments.
