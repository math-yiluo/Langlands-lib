# Actual chosen-basis and all-open sheaf equivalence

This module constructs the equivalence asserted in the final paragraph of David
Renard, *Représentations des groupes réductifs p-adiques*, French version dated
9 July 2026, II.2.1, printed p.37 / one-based PDF43. Its namespace is
`Langlands.Sheaf.Renard.BasisAllOpen`. It uses the published actual categories and
the existing restriction functor, with compatible families of original sections
as the extension.

## Source and scope

The governing source is registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The definitions of basis presheaves, morphisms and the sheaf condition are in
II.2.1, printed pp.33–34 / PDF39–40. The equivalence assertion is on printed
p.37 / PDF43; Renard describes germ extension and restriction. The sheaf example
in A.VI.1 is on printed p.261 / PDF267. The original PDF39–40 and PDF43 were read
for this construction. The public source note
`notes/renard/basis-sheafification-source.md` explains the separate repair of the
printed separation argument; this construction uses separation only for actual
sheaves, through the published restriction interfaces.

Here `X : Type u` carries its supplied topology, `B : OpenBasis X` is arbitrary,
and `u` and `v` are independent. The actual equivalence is

```lean
BasisAllOpen.equivalence.{u,v} (B : OpenBasis X) :
  BasisSheaf.{u,max u v} B ≌
    BasisSheaf.{u,max u v} (allOpenBasis X)
```

Both categories use section carriers in `Type (max u v)`. Products indexed by
chosen-basis opens therefore fit in that universe. This sufficient size is an
internal implementation convention; the source does not discuss Lean universe
parameters, and this module makes no arbitrary original-`v` extension claim.
The explicit functors, additive component isomorphisms and coherence equations
are internal elaborations of the cited equivalence assertion. The compatible
family construction is an alternative implementation of its canonical extension.

There is no intersection-closure, nonemptiness, separation, compactness,
countability, metrizability or cover-cardinality hypothesis. The cover-index
universe `w` is arbitrary. No equivalence, sheaf-unit invertibility, `HasSheafify`,
abelian-category instance or closure certificate is an input. This module does
not prove abelianness or construct scalar/module or compact-section enhancements.

## Actual groups and functors

The following definitions use the actual published `RawPresheaf`, `BasisSheaf`,
`Sections` and `restriction` interfaces.

| Name | Data and hypotheses |
| --- | --- |
| `Inside B V` | All original basis members whose actual open is contained in the actual open `V`. |
| `familySubgroup F V`, `Families F V` | The additive subgroup of the product of the original groups `F(U)`, over `Inside B V`, satisfying every original restriction compatibility equation. Only a raw presheaf is needed. |
| `familyRestriction F h` | Discard the components outside the smaller open in `h : U ≤ V`. |
| `familyMap φ V` | Apply the original natural transformation `φ` at every basis component. |
| `extensionRaw F` | The actual all-open presheaf with these groups and restrictions. |
| `extensionRawMap φ` | The actual natural transformation with components `familyMap φ V`. |
| `rawExtension B` | The functor on raw presheaves, with identity and composition laws proved componentwise. |
| `extension B` | The functor on the actual sheaf categories, using the proved normalization and literal sheaf condition. It acts on the original morphisms through `extensionRawMap`. |
| `allOpenToFamily B G V` | For a raw all-open presheaf `G`, the additive map sending an original section on `V` to all its original chosen-basis restrictions. |
| `basisSectionIso F U` | An additive equivalence from the original group `F(U)` to `Families F U.obj`, for every original basis member `U`; no sheaf hypothesis is needed. |
| `counitSectionIso B G V` | For an actual all-open sheaf `G`, an additive equivalence from compatible families for its restriction to the original group `G(V)`. Its forward map is unique gluing; its inverse is `allOpenToFamily`. |
| `unitRawIso F` | The actual natural isomorphism from `F` to the raw restriction of its extension, with components `basisSectionIso`. |
| `unitIso B` | The unit on the actual sheaf categories, lifted through both existing full-subcategory layers. |
| `counitRawIso B G` | The actual raw natural isomorphism from the extension of the restriction to `G`, with components `counitSectionIso`. |
| `counitIso B` | The counit natural isomorphism on actual all-open sheaves. |
| `equivalence B` | The actual `CategoryTheory.Equivalence`, with forward functor `extension B`, inverse exactly `sheafBasisRestriction B`, and the displayed unit and counit. |

`families_ext` gives equality by all original components.
`familyRestriction_apply`, `familyMap_apply` and `extensionRaw_restriction`
expose the raw formulas. The functor laws are fields of `extensionRaw`,
`extensionRawMap`, `rawExtension` and `extension`, and their proofs use the actual
original component maps. `extension_sections`, `extension_restriction` and
`extension_map_app` expose these same formulas after bundling as sheaves.
`extension_forget` identifies the composite with the published sheaf and
presheaf forgetful functors with `rawExtension B` after forgetting the input.

## Implemented gluing and normalization

`LocallyMatches F O s U t` means that the original section `t` on `U` restricts
to each given family component on every basis member contained in both `U` and
one of the opens `O i`. This is an internal proposition used in the gluing proof.

`unique_basis_glue` refines the cover of a basis member `U` by all pairs consisting
of a cover index `i` and a basis member contained in both `U` and `O i`. The basis
existence property applied to the actual open intersection shows that these
members cover `U`; the intersection itself need not belong to the basis.
Compatibility follows from the compatibility inside each family and agreement
on all smaller basis overlaps. The original sheaf's arbitrary-index gluing law
then gives a unique original section satisfying `LocallyMatches`.

`extension_familySheafCondition` applies this construction at every original
basis member inside the open being glued. Uniqueness shows that the resulting
original sections form a compatible family. Local matching gives amalgamation,
and the same original uniqueness proves uniqueness of the family. Its conclusion
is the published `FamilySheafCondition.{u,max u v,w}` for arbitrary `w`.
`extension_sheafCondition` then gives the exact published literal set-cover
`SheafCondition`, including empty covers.

`extension_isNormalized` derives empty-open normalization from this genuine
sheaf condition. `extension_empty_zero` exposes that every extended section of
the empty open is zero. Empty spaces and bases omitting the empty open are
included: the family product and the refinement construction remain defined,
and normalization follows from the empty cover without an extra assumption.

## Original-section comparisons

For `basisSectionIso F U`, the forward map sends `t` to the family
`W ↦ restriction F W.property t`; the inverse evaluates a compatible family at
`⟨U, le_rfl⟩`. The original restriction identity proves the first inverse law,
and family compatibility proves the second. The following names expose these
facts and their relation to the original maps:

- `basisSectionIso_apply` and `basisSectionIso_symm_apply` are the component and
  evaluation formulas.
- `basisSectionIso_symm_apply_apply` and `basisSectionIso_apply_symm_apply` give
  both inverse laws.
- `basisSectionIso_restriction` and `basisSectionIso_symm_restriction` identify
  both directions with original restriction maps.
- `basisSectionIso_naturality` and `basisSectionIso_symm_naturality` identify
  both directions with every actual input natural transformation.

For an actual all-open sheaf `G`, `allOpenToFamily_bijective` proves injectivity
by the published separation-by-basis-restrictions lemma and surjectivity by
actual gluing in `G` on the basis refinement of `V`. The compatibility-promotion
lemma is used only with this actual sheaf. `counitSectionIso` is the inverse
additive equivalence of this bijective additive map, so its choice of section
is precisely the section characterized by original unique gluing.

- `allOpenToFamily_apply` and `counitSectionIso_symm_apply` expose the inverse
  as the original restrictions.
- `counitSectionIso_amalgamation` says that the glued section restricts to
  every given original basis component; `counitSectionIso_unique` proves that
  these exact restrictions uniquely characterize it.
- `counitSectionIso_symm_apply_apply` and
  `counitSectionIso_apply_symm_apply` give both inverse laws.
- `counitSectionIso_restriction` and `counitSectionIso_symm_restriction`
  identify both directions with original all-open restrictions.
- `counitSectionIso_naturality` and `counitSectionIso_symm_naturality`
  identify both directions with every actual all-open sheaf morphism.

The original groups are thus preserved by explicit additive isomorphisms. Family
carriers are not asserted to be literally the original carriers.

## Categorical comparison and coherence

`unit_hom_app`, `unit_inv_app`, `unit_hom_apply` and `unit_inv_apply` identify the
actual categorical unit components with `basisSectionIso` and evaluation.
`counit_hom_app`, `counit_inv_app`, `counit_hom_apply` and `counit_inv_apply`
identify the actual categorical counit components with unique gluing and
`allOpenToFamily`. Naturality of these actual categorical maps is supplied by
the corresponding natural-isomorphism fields, proved from the evaluated
naturality lemmas above.

`unit_hom_inv_id`, `unit_inv_hom_id`, `counit_hom_inv_id` and
`counit_inv_hom_id` expose both categorical inverse laws. The forward triangle
`extension_unit_counit` is proved by applying the inverse counit and evaluating
twice: both sides are exactly the original compatibility equation of the input
family. This is the coherence field of `equivalence`. `inverse_triangle` gives
the reverse coherence equation for the specified restriction functor using the
standard consequence of that field. No replacement of the specified unit or
counit is used.

The imported `AllOpenMathlibSheaf` supplies the independently published all-open
comparison with actual Mathlib sheaves. The forgetful and evaluated extension
formulas above expose the data for composing with it. The direct composition
and its further evaluated comparisons are a separate reviewable companion unit.
