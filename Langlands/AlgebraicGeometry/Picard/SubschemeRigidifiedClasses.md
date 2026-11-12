# Line bundles rigidified along a morphism of relative spaces

Module `Langlands.AlgebraicGeometry.Picard.SubschemeRigidifiedClasses`, namespace
`Langlands.AlgebraicGeometry.Picard.SubschemeRigidification`.

This is an internal construction for the proof of
`Langlands.AlgebraicGeometry.Picard.FieldEtaleFppfClassSheafStatement`. The Library already
rigidifies line bundles along a *section* `ε : S ⟶ X`
(`RigidifiedLineBundle.relative f ε section_eq`). Here the rigidification is along an
arbitrary morphism. The data are schemes `S X Z : Scheme.{u}`, morphisms `f : X ⟶ S`,
`g : Z ⟶ S`, `z : Z ⟶ X` and the equation `hz : z ≫ f = g`. No finiteness, flatness or
properness is assumed in this module. In the intended application `S = Spec k`, `X` is proper
and `Z = Spec B` with `B` finite over `k`.

## The relative morphism and the categories

`zRel f g z hz : relativeSpace g ⟶ relativeSpace f` is the natural transformation whose
component at `T : Over S` is the morphism `T ×_S Z ⟶ T ×_S X` given by
`pullback.map T.hom g T.hom f (𝟙 T.left) z (𝟙 S)`. `zRel_fst` and `zRel_snd` record its two
projections; naturality is checked on both projections.

`relative f g z hz T` is the published category `RigidifiedLineBundle ((zRel f g z hz).app T)`:
an actual line bundle `L` on `T ×_S X` with an isomorphism
`α : structureModule (T ×_S Z) ≅ (zRel.app T)^* L`, and isomorphisms of line bundles
compatible with these trivializations. `relativePullback h` is the published
`RigidifiedLineBundle.pullback` along the commuting square formed by the two relative-space
maps of `h` and the naturality of `zRel`. `relativePullbackId` and `relativePullbackComp`
combine the published coherence theorem `RigidifiedModule.pullbackCoherence` with
`RigidifiedLineBundle.pullbackCongr`.

## The presheaf of classes and forgetting the rigidification

`Classes f g z hz T` is the type of isomorphism classes, `classOf` the class of a bundle and
`classesPullback` the induced pullback. `classPresheaf f g z hz : (Over S)ᵒᵖ ⥤ Type (u + 1)`
is the presheaf of classes on the full slice; the functor laws are the identity and
composition comparisons. `classPresheaf_map_classOf` gives its formula on representatives.

`forgetClasses` sends a class to the ordinary class `RelativePicard.classOf` of the underlying
line bundle; it is well defined by the published criterion
`RelativePicard.classOf_eq_iff_iso`. `forgetClassNatTrans` is the resulting natural
transformation to `RelativePicard.classPresheaf f`; naturality uses
`RelativePicard.map_classOf` and the published `RigidifiedLineBundle.pullbackForgetIso`.

## Uniqueness of rigidified isomorphisms

`iso_subsingleton` assumes that for every `T` the map on global functions
`((zRel f g z hz).app T).appTop` is injective. It concludes that between two objects of
`relative f g z hz T` there is at most one isomorphism. The proof applies the published
`RigidifiedLineBundle.endo_eq_id` to `e₁.hom ≫ e₂.inv`.

## Changing the rigidification by units

The section `Generic` works for an arbitrary `ε : S₀ ⟶ X₀`. `rigAct r L` keeps the line bundle
of `L` and replaces its trivialization `α` by `unitAut _ r ≪≫ α`, where `unitAut _ r` is the
published scalar automorphism of the structure module by a global unit `r` of `S₀`.

- `rigAct_iso_self_iff`: `rigAct r L` is isomorphic to `L` exactly when `r` lies in the image
  of `Units.map ε.appTop` from the global units of `X₀`. One direction writes a rigidified
  automorphism of the underlying bundle as multiplication by a scalar `c` (published
  `exists_eq_smul_id_of_isLocallyFreeRankOne`), shows `c` is a unit from the inverse, and
  compares scalars on the structure module (published
  `smul_id_injective_of_isLocallyFreeRankOne`). The other direction uses multiplication by
  the inverse unit and `pullback_map_smul`.
- `exists_iso_rigAct`: an isomorphism of the underlying line bundles is a rigidified
  isomorphism `M ≅ rigAct r N` for the unit `r` whose scalar automorphism equals
  `α_M ≫ ε^*ψ ≫ α_N⁻¹`; such a unit exists by the published bijection `unitAutEquiv`.

In the relative setting `actObj r L := rigAct r L` for a global unit `r` of `T ×_S Z`.
`actIso` shows that the action respects isomorphisms, so `actClasses r` acts on classes.

- `actClasses_one`, `actClasses_mul`: the action laws.
- `forgetClasses_actClasses`: the action does not change the ordinary class.
- `pullback_rigidification_unitAut` and `relativePullback_actObj`: pulling back after acting
  by `r` equals acting by the pulled-back unit after pulling back. The proof uses the published
  `pullback_mapIso_unitAut` and `unitAut_naturality` for the structure-module comparison; the two
  objects are then equal as structures. `classesPullback_actClasses` is the class version.
- `actClasses_eq_self_iff`: a unit fixes a class exactly when it comes from a global unit of
  `T ×_S X` (from `rigAct_iso_self_iff`).
- `exists_eq_actClasses_of_forgetClasses_eq`: classes with the same ordinary class differ by
  the action of a unit (from `exists_iso_rigAct`).

## Provenance

Internal. Rigidification of line bundles along a closed subscheme is standard in the
construction of Picard schemes; this module adapts the Library's section-rigidification
framework to an arbitrary morphism and uses only published Library results and Mathlib. It
asserts no sheaf property; those are in `SubschemeRigidifiedDescent`.
