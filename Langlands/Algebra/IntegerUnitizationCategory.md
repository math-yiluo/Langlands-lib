# Integer unitization of additive nonunital module categories

This module constructs an actual categorical equivalence

`NonUnitalModuleCat.{u, v} A ≌ ModuleCat.{v} (Unitization ℤ A)`

for every `A : Type u` with `[NonUnitalRing A]`, with the carrier universe `v`
independent of `u`. The forward functor extends a given additive action to a
unital action of the integer unitization. The inverse functor restricts a unital
action along `Unitization.inr`. Both functors keep the carrier, its additive
group and the underlying additive maps. The unit and counit of the equivalence
are identity maps.

## Provenance

This is derived, internal content. The governing source is David Renard,
*Représentations des groupes réductifs p-adiques*, French version dated
9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

- The "Notations et conventions" paragraphs at the start of Chapter I, printed
  pp.5–6 / PDF11–12, which end where I.1.1 begins, set the convention used here.
  Rings need not be unital. Modules over a unital ring need not be unital: the
  unit is not assumed to act as the identity. So the original action may have no
  unit law, even when the ring `A` has a unit.
- I.2.1, printed p.14 / PDF20, introduces, for a complex algebra `A` without
  unit, the unital algebra `Ã = A ⊕ C·1_A`. It states that `A`-modules which are
  also complex vector spaces naturally become unital `Ã`-modules. I.2.2, printed
  p.15 / PDF21, repeats that `R`-modules naturally become unital `R̃`-modules and
  uses such modules in its Hom–tensor and associativity isomorphisms.

This module uses the canonical integer scalars of an additive commutative group
instead of complex scalars. It therefore realizes, for arbitrary additive
actions, the same unitization method over `ℤ`. Renard does not state this integer
categorical equivalence. It is not identified here with a complex-linear
category, and none of its constructions assumes complex scalars, a unit law for
the original action, nondegeneracy, finite generation or dimension hypotheses.

The registered supplement `renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`, was
checked. PDF1–3 lists corrections to the early chapters of the old printing;
none of them changes the module convention or the unitization used here. PDF18–19
corrects the old printed p.314: there `M` must in addition be assumed to be a
complex vector space, because `A` has no unit. It reduces to the unital case
through `Ã = A ⊕ C·1_A` as in I.2.1. This confirms that a complex structure is
extra data on a general nonunital module. The 2026 edition governs. The current
Library's Renard notes under `notes/renard/` record no correction to these
Chapter I passages; their `appendix-a-corrections.md` concerns Appendix A only.

## Full types

All names below are in the namespace `Langlands.Algebra.IntegerUnitization`.
The ring universe `u` and the carrier universe `v` are independent. The file
checks the following complete unapplied types with `example`s:

```lean
extendObj : (A : Type u) → [NonUnitalRing A] →
  NonUnitalModuleCat.{u, v} A → ModuleCat.{v} (Unitization ℤ A)
extendMap : (A : Type u) → [NonUnitalRing A] → {M N : NonUnitalModuleCat.{u, v} A} →
  NonUnitalModuleHom A M N → (extendObj A M ⟶ extendObj A N)
extendFunctor : (A : Type u) → [NonUnitalRing A] →
  NonUnitalModuleCat.{u, v} A ⥤ ModuleCat.{v} (Unitization ℤ A)
restrictAction : (A : Type u) → [NonUnitalRing A] →
  (M : ModuleCat.{v} (Unitization ℤ A)) → NonUnitalModule A M
restrictObj : (A : Type u) → [NonUnitalRing A] →
  ModuleCat.{v} (Unitization ℤ A) → NonUnitalModuleCat.{u, v} A
restrictMap : (A : Type u) → [NonUnitalRing A] → {M N : ModuleCat.{v} (Unitization ℤ A)} →
  (M ⟶ N) → NonUnitalModuleHom A (restrictObj A M) (restrictObj A N)
restrictFunctor : (A : Type u) → [NonUnitalRing A] →
  ModuleCat.{v} (Unitization ℤ A) ⥤ NonUnitalModuleCat.{u, v} A
equivalence : (A : Type u) → [NonUnitalRing A] →
  NonUnitalModuleCat.{u, v} A ≌ ModuleCat.{v} (Unitization ℤ A)
```

Two further `example`s instantiate `equivalence` at the unequal universe pairs
`u = 0, v = 1` and `u = 1, v = 0`. Further `example`s check that both
categories have morphisms in `Type v` (`Category.{v}`) and that both types of
bundled objects live in `Type (max u (v + 1))`; the carriers stay in `Type v`.

## Extension

`extendObj A M` is `ModuleCat.of (Unitization ℤ A) M`, with the module structure
`CompatibleUnitization.module (NonUnitalModule.toIntLinearEndHom (A := A) (V := M))`
built from the published constructions. This structure is introduced only
locally, so it never overwrites another action on the same carrier.

- `extendObj_carrier`: the carrier is `M`, by definition.
- `extendObj_smul`: `x • m = x.fst • m + x.snd • m`. The first term is the
  canonical integer action of the additive group and the second is the stored
  action of `M`. For `x = (n, a)` this is `n • m + a • m`.
- `extendObj_inr_smul`: `Unitization.inr a` acts as the original `a`.

`extendMap A f` is `ModuleCat.ofHom` of
`CompatibleUnitization.ofLinearIntertwiner f.toIntLinearIntertwiner`. It makes
the same additive intertwiner unitization-linear through the published
integer-compatible and unitized Hom adapters. `extendMap_apply` says that its
underlying function is `f`. `extendFunctor` has object map `extendObj A` and
morphism map `extendMap A`; its functor laws hold pointwise by `rfl`.
`extendFunctor_obj` and `extendFunctor_map` unfold the functor.
`extendMap_id` and `extendMap_comp` state the identity and composition laws.

## Restriction

`restrictAction A M` is the original-ring action on a unital
`Unitization ℤ A`-module `M`. It is `NonUnitalModule.ofEndHom` of the
endomorphism representation `Module.toAddMonoidEnd`, composed with the nonunital
ring map `Unitization.inrNonUnitalAlgHom ℤ A`. It is a definition, not a global
instance. `restrictObj A M` bundles the carrier of `M` with this action. Nothing
here requires the original unit of `A`, if `A` has one, to act as the identity.
The target is the whole category `NonUnitalModuleCat A`, not a full subcategory.

- `restrictObj_carrier`: the carrier is `M`, by definition.
- `restrictObj_smul`: `a` acts as `Unitization.inr a`.

`restrictMap A f` keeps `f.hom.toAddMonoidHom`. Its intertwining law is the
linearity of `f` at `Unitization.inr a`. `restrictMap_apply` says that the
underlying function is `f`. `restrictFunctor` has object map `restrictObj A` and
morphism map `restrictMap A`. `restrictFunctor_obj` and `restrictFunctor_map`
unfold it. `restrictMap_id` and `restrictMap_comp` state the functor laws, proved
by extensionality of additive intertwiners.

## Round trips and the equivalence

- `restrict_extend_smul`: after extension then restriction, `a` acts as in the
  original module `M`. This holds for every action, including the zero action.
- `inl_smul`: in every unital `Unitization ℤ A`-module, `Unitization.inl n`
  acts as the canonical integer multiple `n • m`. The proof uses that
  `Unitization.inlRingHom` preserves integer casts (`map_intCast`) and
  `Int.cast_smul_eq_zsmul`.
- `extend_restrict_smul`: after restriction then extension, every
  `x : Unitization ℤ A` acts as in the original unital module. This includes the
  integer coordinate. The proof writes `x = inl x.fst + inr x.snd`
  (`Unitization.inl_fst_add_inr_snd_eq`), then uses `add_smul` and `inl_smul`.

`unitComponent A M : M ≅ restrictObj A (extendObj A M)` and
`counitComponent A M : extendObj A (restrictObj A M) ≅ M` use the identity
additive map in both directions; their intertwining laws are
`restrict_extend_smul` and `extend_restrict_smul`. The lemmas
`unitComponent_hom_apply`, `unitComponent_inv_apply`,
`counitComponent_hom_apply` and `counitComponent_inv_apply` state that each map
sends `m` to `m`.

`unitIso : 𝟭 _ ≅ extendFunctor A ⋙ restrictFunctor A` and
`counitIso : restrictFunctor A ⋙ extendFunctor A ≅ 𝟭 _` are built from these
components with `NatIso.ofComponents`. Naturality holds pointwise by `rfl`.
`equivalence A` is the `CategoryTheory.Equivalence` with functor `extendFunctor A`,
inverse `restrictFunctor A`, unit isomorphism `unitIso A` and counit isomorphism
`counitIso A`. Its coherence field `functor_unitIso_comp` holds pointwise by `rfl`,
because every map involved is the identity on carriers.

## Compatibility of the equivalence

Consumers can use these lemmas about this specific equivalence:

- `equivalence_functor`, `equivalence_inverse`, `equivalence_unitIso` and
  `equivalence_counitIso` identify its four fields with `extendFunctor A`,
  `restrictFunctor A`, `unitIso A` and `counitIso A`.
- `equivalence_functor_obj_carrier` and `equivalence_inverse_obj_carrier`: both
  functors keep the carrier.
- `equivalence_functor_map_apply` and `equivalence_inverse_map_apply`: both
  functors keep the underlying function of a morphism. Morphisms of
  `NonUnitalModuleCat` are applied through the projection
  `NonUnitalModuleHom.toAddMonoidHom`, so the lemmas about the inverse functor
  and the unit are stated with it.
- `equivalence_unitIso_hom_app_apply`, `equivalence_unitIso_inv_app_apply`,
  `equivalence_counitIso_hom_app_apply` and
  `equivalence_counitIso_inv_app_apply`: each component of the unit and counit,
  in both directions, sends `m` to `m`.
- The instances `extendFunctor_isEquivalence` and
  `restrictFunctor_isEquivalence` record that both named functors are
  equivalences, taken from `equivalence A`.

## Zero-action check

`zeroIntObj : NonUnitalModuleCat ℤ` is the additive group `ℤ` with the zero
action `NonUnitalModule.zero` of the unital ring `ℤ`. This action is introduced
locally. `zeroIntObj_one_ne_zero` shows that the carrier is nonzero, and
`zeroIntObj_smul` that every `a` acts as zero, including the unit `1 : ℤ`.

- `zeroIntObj_restrict_extend_smul`: after extension then restriction, the action
  is still zero.
- `zeroIntObj_old_one_smul`: in the extension, the original unit
  `Unitization.inr (1 : ℤ)` acts as zero.
- `zeroIntObj_new_one_smul`: the unit `1 : Unitization ℤ ℤ` acts as the identity.

The explicit `Unitization.inr` matters: an integer cast into `Unitization ℤ ℤ`
lands in the scalar coordinate, so it denotes a multiple of the new unit, not
the original one.

## Scope

This unit constructs the equivalence of additive module categories and its
intrinsic laws. It asserts nothing about abelianness, exactness, coproducts,
categorical subobjects versus `NonUnitalSubmodule`, finiteness or Noetherian
transport, canonical complex scalars on nondegenerate modules, tensor products,
or the source's functors and adjunctions. Those are separate units of the
parent program.
