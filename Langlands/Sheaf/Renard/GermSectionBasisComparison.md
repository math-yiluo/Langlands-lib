# Renard II.2.1: germ sections before and after restriction to a chosen basis

The governing source is Renard, *Représentations des groupes réductifs
p-adiques*, French version dated 9 July 2026. The registered source is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The final paragraph of II.2.1, printed p.37 / PDF p.43, restricts a sheaf
`G` of base `T` to the basis `T0`. It forms `(G_T0)+` and states "Il est
clair que ce faisceau est égal à G+". Here `(·)+` assigns to an arbitrary
open `U` the sections `s : U → ∐_{x ∈ U} F_x` of (II.2.1.2), printed p.34 /
PDF p.40. Such a section admits a cover of `U` by basis opens `U_i` and
sections `f_i ∈ F(U_i)` with `s(x) = ρ_{U_i,x}(f_i)` for `x ∈ U_i ∩ U`. The
published `GermSections` uses the equivalent form `LocallyRepresented`, with
whole basis neighborhoods contained in `U`. The equivalence of the two forms
is the published `locallyRepresented_iff_cover`. This module makes the
claimed equality explicit as a natural isomorphism on the actual published
constructions. It is built on the stalk comparison of
`Langlands.Sheaf.Renard.BasisStalkComparison`. The supplementary corrections
`renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
PDF pp.2–3, were read; none of them changes this comparison.

Throughout, `X : Type u` has its supplied topology, `B : OpenBasis X` is
arbitrary, `F : RawPresheaf.{u,v} (allOpenBasis X)` is an arbitrary all-open
raw presheaf and `U : Opens X` is an arbitrary actual open. Write `R F` for
the published restriction `(rawBasisRestriction B).obj F`, and `c_x` for the
stalk comparison `rawStalkRestrictionEquiv B F x` of the companion module.

## Pointwise transport of germ families

`germFamilyRestrictionEquiv B F U` is the additive equivalence
`GermFamily (R F) U ≃+ GermFamily F U` given by Mathlib's
`AddEquiv.piCongrRight`. Its evaluation formulas
`germFamilyRestrictionEquiv_apply` and `_symm_apply` state that an arbitrary
family `s` goes to `x ↦ c_x (s x)`, and the inverse to `x ↦ c_x⁻¹ (s x)`.

`LocallyRepresented.restrictionTransport` proves the forward direction of
local representation. A restricted witness at a point is a chosen basis open
`V`, contained in `U` and containing the point, with an original section
`t : Sections F (allOpen V.obj)` whose restricted germs agree with `s` on all
of `V`. The same actual open `allOpen V.obj` and the same section `t` then
represent the transported family on all of `V`, by the germ formula
`rawStalkRestrictionEquiv_germ`.

`LocallyRepresented.restrictionTransportSymm` proves the inverse direction.
An original witness is an actual open `W ≤ U` containing the point, with a
section of `F` on `W` whose germs agree with the family on all of `W`.
Basis refinement (`OpenBasis.exists_subset`) chooses a basis open `V ≤ W`
containing the point. The original restriction of the section to `V`
represents the inversely transported family on all of `V`, by
`rawStalkRestrictionEquiv_symm_germ_of_le`. Every witness is a whole
contained neighborhood with one original section. No separatedness of an
arbitrary presheaf is used.

`locallyRepresented_restriction_iff` states that `s` is locally represented
for `R F` if and only if its transport is locally represented for `F`.
`locallyRepresented_restriction_symm_iff` is the same statement for the
inverse transport. Each reverse implication applies the opposite direction
to the transported family and uses that the two transports are inverse.

## The germ-section isomorphism

`germSectionsRestrictionEquiv B F U :
GermSections (R F) U ≃+ GermSections F U` restricts the pointwise transport
to the published subgroups of locally represented families. The section
carriers are unchanged. Its point evaluations are
`germSectionsRestrictionEquiv_apply` and `_symm_apply`, both by definition.

`germSectionsRestrictionEquiv_representative` sends a restricted
representative on a basis open `V` to the original germs
`rawGerm F (allOpen V.obj) y hy t` of the same original section.
`germSectionsRestrictionEquiv_symm_representative` is the inverse statement
on a basis open. `germSectionsRestrictionEquiv_symm_representative_of_le`
treats an original representative on an arbitrary actual open `W`. On any
basis open `V ≤ W` the inverse gives the restricted germs of the original
restriction of the representing section.

`germSectionsRestrictionEquiv_restriction` and `_symm_restriction` prove
compatibility with the published `germRestriction` along every inclusion
`U ≤ V` of actual opens; both hold by definition. For every original natural
transformation `φ : F ⟶ G`, `germSectionsRestrictionEquiv_naturality` proves
naturality with the published `germSectionsMap ((rawBasisRestriction B).map φ)`
and `germSectionsMap φ`. `_symm_naturality` proves it for the inverse. Both
follow pointwise from the stalk naturality `rawStalkRestrictionEquiv_naturality`
and its inverse.

## Germ-sheaf packaging

`germPresheafRestrictionIso B F` assembles the section isomorphisms into an
isomorphism of the published all-open germ presheaves
`germPresheafOn (allOpenBasis X) (R F) ≅ germPresheafOn (allOpenBasis X) F`.
Its components are `AddEquiv.toAddCommGrpIso`, and naturality is the
restriction compatibility. `germSheafRestrictionIso B F` is the same
isomorphism in the existing full sheaf subcategory. It applies
`ObjectProperty.isoMk` twice: first in the full subcategory of normalized
presheaves, then in the full subcategory of sheaves. Its source is `germSheafOn (allOpenBasis X) (R F)`
and its target is `germSheafOn (allOpenBasis X) F`.

`rawRestrictedGermSheafIso B` is the natural isomorphism
`rawBasisRestriction B ⋙ rawAllOpenGermSheafFunctor B ≅
rawAllOpenGermSheafFunctor (allOpenBasis X)`. Its naturality square is checked
on sections by `germSectionsRestrictionEquiv_naturality`. At `allOpen U`, the
hom and inverse section components are exactly
`germSectionsRestrictionEquiv B F U` and its inverse. These are
`rawRestrictedGermSheafIso_hom_app` and `_inv_app`, with the pointwise forms
`_hom_apply` and `_inv_apply`. `rawRestrictedGermSheafIso_hom_restriction`
and `_inv_restriction` restate the `germRestriction` compatibility for these
components. `_hom_naturality` and `_inv_naturality` restate the
`germSectionsMap` compatibility.

The normalized specialization `restrictedGermSheafIso B` is
`basisRestriction B ⋙ allOpenGermSheafFunctor B ≅
allOpenGermSheafFunctor (allOpenBasis X)`. It is obtained by whiskering the
raw isomorphism with the existing `presheafInclusion (allOpenBasis X)`. Its
components are the same sheaf isomorphisms (`restrictedGermSheafIso_app`),
with section evaluations `restrictedGermSheafIso_hom_apply` and `_inv_apply`.
No new presheaf or sheaf category is introduced.

## Scope and generality

The space universe `u` and original section universe `v` are independent.
Stalks, germ families, germ sections and both germ sheaves take values in
`Type (max u v)`, and no lowering to `v` is asserted. The input is an
arbitrary raw presheaf, with no normalization, sheaf or separation hypothesis.
Arbitrary supplied topologies and arbitrary chosen bases without intersection
closure are allowed. Empty spaces and empty opens are allowed; on an empty
open all statements hold vacuously pointwise. No compactness, total
disconnectedness, Hausdorff, countability, nonemptiness or cardinality
hypothesis is used. The raw-input, arbitrary-topology and categorical
formulation is an internal generalization. It supports the source's comparison
of `(G_T0)+` with `G+` for sheaves.

This comparison changes the original input basis and its stalk colimits. It
is different from the published `rawAllOpenGermRestrictionIso` of
`Langlands.Sheaf.Renard.SheafBasisRestriction`. That isomorphism has identity
components: it evaluates the same original stalk family on different target
bases. It gives no comparison between `rawStalk F x` and `rawStalk (R F) x`.
This module does not prove the equivalence of the sheaf categories at the
original value universe, universe lowering, compact-section comparisons or
any scalar or module structure; those remain separate obligations.
