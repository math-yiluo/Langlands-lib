# Renard II.2.1: all-open presheaf restriction to a chosen basis

Worker 633 implemented this construction. Worker 6 supplied the source audit,
the focused interface and the refinement route used by the subsequent sheaf
restriction construction.

The governing source is David Renard, *Représentations des groupes réductifs
p-adiques*, French version dated 9 July 2026, the final paragraph of II.2.1,
printed p.37 / PDF p.43. The registered source is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The complete original page was read. The supplementary registered 2010-edition
*Corrections et compléments*, `renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
PDF pp.2–3, were also read. Their nearby cover-index and adjunction corrections
do not alter restriction by evaluation on the same actual opens.

Renard first restricts an all-open sheaf to the chosen basis. This module
constructs the underlying inclusion and presheaf restrictions, using the
published `BasisOpen`, `allOpenBasis`, `allOpen`, `RawPresheaf` and `Presheaf`.
The sheaf axiom for restriction is a further intrinsic obligation, supplied
in the separate `SheafBasisRestriction` module.

`basisToAllOpen B` sends a basis object `U` to `allOpen U.obj` and retains
the actual underlying inclusion arrow. Its object, arrow and `basisHom`
formulas are definitional. Composing it with the existing all-open
`basisInclusion` is literally `basisInclusion B`.

`rawBasisRestriction B` precomposes an actual contravariant functor with
`(basisToAllOpen B).op`. A natural transformation restricts by left whiskering,
so its component at `U` is its original component at `allOpen U.obj`.
The section, restriction, identity and composition formulas expose those
actual original values and maps. All these formulas follow directly from
the definitions; the functor laws are definitional as well.

`rawBasisRestriction_isNormalized` applies the original normalization to
`allOpen U.obj` whenever `U.obj` is empty. Thus `basisRestriction B` is an
actual functor on the existing normalized full subcategories. Its raw object,
restriction maps and morphism components are exactly the raw restriction
of the original object and transformation. Identity and composition hold
componentwise. `basisRestriction_comp_inclusion` identifies the whole
composite with the existing forgetful inclusions.

The space universe `u` and original value universe `v` remain independent;
restriction preserves `v` without raising it. The supplied topology and
arbitrary chosen basis are retained. Empty spaces and empty basis opens
are allowed, and normalization is vacuous when there is no empty basis
member. No intersection closure, separation, local compactness,
countability or nonemptiness premise is imposed. Raw inputs, independent
universe packaging and the explicit presheaf-level functors are internal
generality of the source restriction operation. This module asserts no
category equivalence, stalk comparison, sheaf-unit invertibility, scalar
extension or support result.
