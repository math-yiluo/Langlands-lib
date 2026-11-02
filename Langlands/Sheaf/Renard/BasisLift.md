# Universe lifts of Renard basis presheaves and basis sheaves

This module builds Lean size-transport functors. They move the values of the
published basis presheaves `RawPresheaf B` and `Presheaf B`, and of the basis
sheaves `BasisSheaf B`, from value universe `v` to `max v w`. Renard prints no
such statement. The construction is internal Lean bookkeeping, needed later to
state Renard's canonical sheafification maps without identifying two different
value universes.

## Motivation and provenance

David Renard, *Représentations des groupes réductifs p-adiques*, French version
dated 9 July 2026, II.2.1, printed pp.34–37 / PDF pp.40–43 (registered source
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`). These
pages build the sheaf `F⁺` of sections into the étalé space from a presheaf `F`
on a basis `T₀`. They define the canonical map `ι_F : F → F⁺`, `f ↦ s_f`, and
prove that `F ↦ F⁺` is left adjoint to the forgetful functor `Sh(X) → pSh(X)`.
The concluding remark says `ι_F` is an isomorphism when `F` is a sheaf. In Lean
the stalks of a `v`-valued presheaf on a space `X : Type u` are lifted colimits
in `Type (max u v)` (`Langlands.Sheaf.Renard.BasisStalk`). A germ-section
presheaf built from them is therefore `max u v`-valued, while `F` itself is
`v`-valued. A map such as `ι_F`, or an adjunction inside a single category,
needs both ends in the same category. This module supplies the actual
`v → max v w` lift, and with `w = u` the `v → max u v` lift, with no
value-lowering assumption. The Renard passage itself works with sets and
groups and has no universes, so no statement here is attributed to Renard.
Every declaration is derived internal packaging of Mathlib's
`AddCommGrpCat.uliftFunctor`. The 2010-edition corrections (PDF pp.2–3) and
the public note `notes/renard/basis-sheafification-source.md` concern later
descent and adjunction arguments and do not bear on this module.

## What does not change

The lifts change only the universe of the section groups. The space `X`, its
topology, the chosen `B : OpenBasis X`, the category `BasisOpen B` and every
basis open stay the same, so no space or basis is changed. The universes are
independent: the space universe `u`, value universe `v` and lift universe `w`,
together with the cover-index universe `w'` in the family results. No
inequality among them is assumed. Spaces, bases and covers are arbitrary, and
empty spaces, empty basis opens and empty covers are allowed. No separation,
intersection-closure, cardinality or smallness hypothesis appears.

## The raw lift

`rawLift B` is `(Functor.whiskeringRight (BasisOpen B)ᵒᵖ AddCommGrpCat.{v}
AddCommGrpCat.{max v w}).obj AddCommGrpCat.uliftFunctor.{w,v}`, i.e. actual
postcomposition (`rawLift_obj`, `rawLift_map`). Its full type, with universe
parameters `rawLift.{u,v,w}`, is

```
rawLift : {X : Type u} → [TopologicalSpace X] → (B : OpenBasis X) →
  RawPresheaf.{u,v} B ⥤ RawPresheaf.{u,max v w} B
```

At each basis open the lifted sections are literally the `ULift` group
(`sections_rawLift`), and the carrier is `ULift.{w,v} (Sections F U)`
(`sections_rawLift_carrier`), both by `rfl`. The component formulas are
definitional:

- `restriction_rawLift_up`: restricting `ULift.up s` gives
  `ULift.up (restriction F h s)`;
- `restriction_rawLift_down`: `ULift.down` of a lifted restriction is the
  original restriction of `ULift.down t`;
- `rawLift_map_app_up` and `rawLift_map_app_down`: the same formulas for the
  components of lifted natural transformations.

`rawLift_map_id` and `rawLift_map_comp` record the functor laws.

## Normalization

`subsingleton_sections_rawLift_iff` transports `Subsingleton` along
`Equiv.ulift`. Applying this at each basis open `U` with `U.obj = ⊥` gives
`isNormalized_rawLift_iff : IsNormalized ((rawLift B).obj F) ↔ IsNormalized F`
for every `F : RawPresheaf.{u,v} B`. The two directions are
`isNormalized_rawLift` and `isNormalized_of_rawLift`. The equivalence holds at
every empty basis open, and holds trivially when the basis has none.

`presheafLift B : Presheaf.{u,v} B ⥤ Presheaf.{u,max v w} B` is
`ObjectProperty.lift` of `presheafInclusion B ⋙ rawLift B` along that
preservation. Its erasure is an equality,
`presheafLift_comp_inclusion : presheafLift B ⋙ presheafInclusion B =
presheafInclusion B ⋙ rawLift B`. The same fact is also stated as
`presheafLiftCompInclusionIso` with identity components
(`presheafLiftCompInclusionIso_hom_app`, `_inv_app`).
`presheafLift_obj_obj` and `presheafLift_map_hom` give the underlying
objects and morphisms.

## Gluing and the sheaf condition

The results below use the published literal predicates `Compatible`,
`IsAmalgamation`, `FamilySheafCondition` and `SheafCondition`, for any index
type `ι : Type w'` and any `U : ι → BasisOpen B`. Compatibility still tests
equality on every smaller basis open inside an overlap. Each proof applies
`congrArg ULift.down` or `congrArg ULift.up` to the given equalities:

- `compatible_rawLift_up_iff`: a family `fun i => ULift.up (s i)` is compatible
  in the lift iff `s` is compatible in `F`;
- `compatible_rawLift_iff`: a lifted family `s` is compatible iff
  `fun i => ULift.down (s i)` is compatible in `F`;
- `isAmalgamation_rawLift_iff` and `isAmalgamation_rawLift_up_iff`: likewise for
  gluing sections, i.e. the restriction equalities `restriction … t = s i`;
- `existsUnique_isAmalgamation_rawLift_iff`: unique gluing of a lifted family is
  equivalent to unique gluing of its lowering. The witness is moved by
  `ULift.down`/`ULift.up`. Uniqueness is moved by lifting, resp. lowering, the
  competitor and applying the other side's uniqueness clause.

`familySheafCondition_rawLift_iff :
FamilySheafCondition.{u,max v w,w'} ((rawLift B).obj F) ↔
FamilySheafCondition.{u,v,w'} F` holds in every index universe `w'`. Forward: an
original compatible family is lifted by `ULift.up` and glued in the lift, and
the unique gluing is lowered. Backward: a lifted compatible family is lowered by
`ULift.down` and glued in `F`, and the gluing section is lifted. The published
`sheafCondition_iff_family` turns this into
`sheafCondition_rawLift_iff : SheafCondition ((rawLift B).obj F) ↔
SheafCondition F`, with directions `sheafCondition_rawLift` and
`sheafCondition_of_rawLift`.

`sheafLift B : BasisSheaf.{u,v} B ⥤ BasisSheaf.{u,max v w} B` is
`ObjectProperty.lift` of `sheafForget B ⋙ presheafLift B`. Its erasures are
equalities by `rfl`: `sheafLift_comp_forget` gives the normalized lift, and
`sheafLift_comp_forget_comp_inclusion` gives the raw lift. They are also
stated as identity-component isomorphisms `sheafLiftCompForgetIso` and
`sheafLiftCompRawIso`, with `_hom_app`/`_inv_app` lemmas, and
`sheafLift_obj_obj(_obj)`, `sheafLift_map_hom(_hom)` give the underlying data.
`sheafLift_unique_gluing` combines the published arbitrary-index
`BasisSheaf.unique_gluing` with the transport lemmas. For a lifted basis sheaf
and a compatible lifted family indexed by any `ι : Type w'`, there is a unique
lifted section whose lowering amalgamates the lowered family in the original
sheaf.

## Full faithfulness and lowering of morphisms

`rawLiftFullyFaithful B : (rawLift B).FullyFaithful` is
`AddCommGrpCat.uliftFunctorFullyFaithful.{v,w}.whiskeringRight (BasisOpen B)ᵒᵖ`
(Mathlib's witness lists the value universe before the lift universe).
`rawLower φ` is its preimage of a morphism `φ` between lifted objects.
`rawLower_app_apply` shows by `rfl` that its component is
`s ↦ ULift.down (φ.app (op U) (ULift.up s))`. The two inverse identities are
`rawLift_map_rawLower : (rawLift B).map (rawLower φ) = φ` and
`rawLower_rawLift_map : rawLower ((rawLift B).map ψ) = ψ`.

The full subcategory morphisms are wrapped natural transformations.
`presheafLower` and `sheafLower` therefore wrap `rawLower` with
`ObjectProperty.homMk`. They have the same evaluated formulas
(`presheafLower_app_apply`, `sheafLower_app_apply`). The inverse identities
(`presheafLift_map_presheafLower`, `presheafLower_presheafLift_map`,
`sheafLift_map_sheafLower`, `sheafLower_sheafLift_map`) follow from
`ObjectProperty.hom_ext` and the raw identities. They give
`presheafLiftFullyFaithful B : (presheafLift B).FullyFaithful` and
`sheafLiftFullyFaithful B : (sheafLift B).FullyFaithful`, together with
`Full` and `Faithful` instances for all three lifts. Lowering is defined only
on morphisms between lifted objects. The module defines no functor lowering
the values of arbitrary `max v w`-valued objects.

## Lifting again at an already lifted universe

At input value universe `max v w`, lifting again at level `w` does not change
the universe, since `max (max v w) w = max v w`. The module gives natural
isomorphisms to the identity:

```
rawRelift.{u,v,w}     (B) : rawLift.{u,max v w,w} B     ≅ 𝟭 (RawPresheaf.{u,max v w} B)
presheafRelift.{u,v,w} (B) : presheafLift.{u,max v w,w} B ≅ 𝟭 (Presheaf.{u,max v w} B)
sheafRelift.{u,v,w}   (B) : sheafLift.{u,max v w,w} B   ≅ 𝟭 (BasisSheaf.{u,max v w} B)
```

Each `rawRelift` component is `AddEquiv.toAddCommGrpIso AddEquiv.ulift` at each
basis open, so its hom is pointwise `ULift.down` and its inverse is
`ULift.up` (`rawRelift_hom_app_app`, `rawRelift_inv_app_app`). The evaluated
forms are `rawRelift_hom_app_app_apply` (`t ↦ ULift.down t`) and
`rawRelift_inv_app_app_apply` (`s ↦ ULift.up s`). The naturality proofs
are `rfl`; `rawRelift_hom_naturality` and its evaluated form
`rawRelift_hom_naturality_apply` state them. `presheafRelift` and `sheafRelift` have the
wrapped components `ObjectProperty.isoMk` of the previous level
(`presheafRelift_hom_app_hom`, `sheafRelift_hom_app_hom(_hom)` and the `inv`
versions). Their evaluated formulas are `presheafRelift_hom_app_hom_app_apply`,
`presheafRelift_inv_app_hom_app_apply`,
`sheafRelift_hom_app_hom_hom_app_apply` and
`sheafRelift_inv_app_hom_hom_app_apply`. Each `*_hom_naturality` lemma
restates naturality. The erasures agree by `rfl`:
`presheafRelift_erasure` (normalized to raw), `sheafRelift_erasure` (sheaf to
normalized) and `sheafRelift_erasure_raw` (sheaf to raw). Each says that
`Functor.isoWhiskerRight` of the higher-level isomorphism by the inclusion
equals `Functor.isoWhiskerLeft` of the inclusion with the lower-level
isomorphism.

## The joint value universe `max u v`

`rawLiftJoint`, `presheafLiftJoint` and `sheafLiftJoint` are the lifts with
`w = u`, taking `v`-valued objects to the joint value universe `max u v` of the
actual stalk families. `stalkDiagram_eq_rawLiftJoint` shows by `rfl` that the
published lifted stalk diagram `stalkDiagram F x` is
`neighborhoodInclusion B x ⋙ (rawLiftJoint B).obj F`. `rawReliftJoint`,
`presheafReliftJoint` and `sheafReliftJoint` are the re-lift isomorphisms at
`max u v` with lift level `u`.

## Scope

This module constructs no value-lowering functor on arbitrary larger-valued
objects and no adjoint to a lift. It also constructs no germ-section functor,
canonical sheafification unit, descent, sheafification adjunction, unit
isomorphism on sheaves, or equivalence between chosen-basis and all-open sheaf
categories. The kernel axioms used are `propext`, `Classical.choice` and
`Quot.sound` only.

Worker 947 implemented the module. The task context, published by Worker 6,
suggested the whiskering construction, the reuse of
`uliftFunctorFullyFaithful.whiskeringRight` and the lower–glue–lift gluing
route.
