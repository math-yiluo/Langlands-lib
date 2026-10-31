# Categorical subobjects of additive nonunital modules

This module constructs an actual order isomorphism

`subobjectOrderIso M : CategoryTheory.Subobject M ≃o NonUnitalSubmodule A M`

for every `A : Type u` with `[NonUnitalRing A]` and every
`M : NonUnitalModuleCat.{u, v} A`. The ring universe `u` and the carrier universe
`v` are independent. The left-hand side is Mathlib's type of subobjects of `M` in
the existing category `NonUnitalModuleCat A`: monomorphisms into `M` up to
isomorphism over `M`, ordered by factorization. The right-hand side consists of
the additive subgroups of `M` that are stable under the action stored in `M`
(`M.isModule`), ordered by inclusion of subsets of `M`. The original action is
never replaced. It need not satisfy a unit law, nondegeneracy or a finiteness
condition, even when `A` has a unit.

The forward map sends the class of a monomorphism `f : N ⟶ M` to the range of
`f`. The inverse sends `S` to the class of the existing subtype inclusion
`S.subtype`, with domain `NonUnitalModuleCat.of A S`.

## Provenance

This is derived, internal content. Renard does not state this adapter. The
governing source is David Renard, *Représentations des groupes réductifs
p-adiques*, French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

- "Notations et conventions", at the start of Chapter I, printed pp.5–6 /
  PDF11–12. Rings need not be unital. Modules over a unital ring need not be
  unital: if the unit acts as the identity, the module is said to be unital.
  `NonUnitalModuleCat A` and `NonUnitalSubmodule A M` implement this convention
  in the Library. The construction here uses only the stored action, with no
  unit law.
- A.I.2, printed p.248 / PDF254. Monomorphisms `f : Y → X` are preordered by
  `f₁ ≤ f₂` when some `i : Y₁ → Y₂` satisfies `f₂ ∘ i = f₁`. A subobject of `X`
  is an equivalence class for mutual comparability, and `≤` induces the order on
  the collection `S_X` of subobjects. Mathlib's `Subobject M` is this quotient:
  it is the thin skeleton of `MonoOver M`, and `Subobject.mk f ≤ Subobject.mk g`
  holds exactly when `f` factors through `g`. Renard's abuse of notation
  "`Y ⊆ X`" for a subobject is the inclusion that the order isomorphism makes
  literal for modules.
- I.2.1, printed p.14 / PDF20, introduces the unital complex algebra
  `Ã = A ⊕ C·1_A` for a complex algebra `A` without unit. `A`-modules that are
  also complex vector spaces become unital `Ã`-modules. This is a different
  construction. The route below uses the integer unitization `Unitization ℤ A`
  of an arbitrary ring, with the canonical integer scalars of the additive group.
  It needs no complex structure. Nothing here is a complex-linear comparison.

The registered supplement `renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`, was
checked at PDF18–19. It corrects the old printed p.314: there `M` must also be
assumed to be a complex vector space, because `A` has no unit, and the proof
reduces to `Ã = A ⊕ C·1_A` as in I.2.1. This confirms that a complex structure is
extra data on a nonunital module. The supplement does not change the module
conventions or A.I.2. The 2026 edition governs.

## Route

The order isomorphism is the composite

```lean
((Subobject.lowerEquivalence
    (MonoOver.congr M (IntegerUnitization.equivalence A))).toOrderIso.trans
  (ModuleCat.subobjectModule (IntegerUnitization.extendObj A M))).trans
  (NonUnitalSubmodule.intUnitizedOrderIso (A := A) (M := M)).symm
```

1. The published `IntegerUnitization.equivalence A` is the equivalence
   `NonUnitalModuleCat.{u, v} A ≌ ModuleCat.{v} (Unitization ℤ A)`. Its functor
   `extendFunctor A` keeps the carrier and the underlying additive maps.
   Mathlib's `MonoOver.congr M` transports monomorphisms over `M` along it.
   `Subobject.lowerEquivalence` descends the result to an equivalence
   `Subobject M ≌ Subobject (extendObj A M)`, and `Equivalence.toOrderIso` reads
   it as an order isomorphism.
2. Mathlib's `ModuleCat.subobjectModule` identifies the subobjects of the
   unital `Unitization ℤ A`-module `extendObj A M` with its submodules. It sends
   a subobject `P` to `LinearMap.range P.arrow.hom`.
3. The published `NonUnitalSubmodule.intUnitizedOrderIso`, inverted, identifies
   these submodules with `NonUnitalSubmodule A M` for the stored action on the
   same carrier. It keeps the underlying subset.

The integer-unitized module structure on the carrier of `M` is only the one
selected locally inside `extendObj A M` and `intUnitizedOrderIso`. No instance
on `M` is replaced. The published equivalence and submodule correspondence are
used unchanged.

## Full types

All names are in the namespace `Langlands.Algebra.NonUnitalModuleCat`. Morphisms
of `NonUnitalModuleCat` are applied through the projection
`NonUnitalModuleHom.toAddMonoidHom`. The display below writes `f n` for
`NonUnitalModuleHom.toAddMonoidHom (A := A) (M := N) (N := M) f n`. The file
checks these complete unapplied types with `example`s:

```lean
mono_iff_injective : (A : Type u) → [NonUnitalRing A] →
  {M N : NonUnitalModuleCat.{u, v} A} → (f : M ⟶ N) →
    (Mono f ↔ Function.Injective (NonUnitalModuleHom.toAddMonoidHom f))
subtypeHom : (A : Type u) → [NonUnitalRing A] → {M : NonUnitalModuleCat.{u, v} A} →
  (S : NonUnitalSubmodule A M) → (NonUnitalModuleCat.of A S ⟶ M)
subobjectOrderIso : (A : Type u) → [NonUnitalRing A] →
  (M : NonUnitalModuleCat.{u, v} A) → Subobject M ≃o NonUnitalSubmodule A M
mem_subobjectOrderIso_mk : (A : Type u) → [NonUnitalRing A] →
  {M N : NonUnitalModuleCat.{u, v} A} → (f : N ⟶ M) → [Mono f] → (m : M) →
    (m ∈ subobjectOrderIso M (Subobject.mk f) ↔ ∃ n : N, f n = m)
subobjectOrderIso_symm_apply : (A : Type u) → [NonUnitalRing A] →
  {M : NonUnitalModuleCat.{u, v} A} → (S : NonUnitalSubmodule A M) →
    (subobjectOrderIso M).symm S = Subobject.mk (subtypeHom S)
```

A further `example` writes the target of `subobjectOrderIso` as
`@NonUnitalSubmodule A M _ M.isAddCommGroup M.isModule`. This shows that the
right-hand side uses the stored additive group and the stored action of `M`. Two
more `example`s instantiate `subobjectOrderIso` at the unequal universe pairs
`u = 0, v = 1` and `u = 1, v = 0`.

## Monomorphisms

- `mono_iff_injective`: a morphism `f : M ⟶ N` of `NonUnitalModuleCat A` is a
  monomorphism if and only if its underlying additive map is injective. The
  forward direction maps `f` along the equivalence functor, which preserves
  monomorphisms, and uses Mathlib's `ModuleCat.mono_iff_injective`. The
  underlying function does not change. The backward direction cancels pointwise
  and uses extensionality of additive intertwiners. No new concrete-category
  instance is introduced.
- `subtypeHom S` is the existing inclusion `S.subtype`, typed as a morphism
  `NonUnitalModuleCat.of A S ⟶ M`. `subtypeHom_eq_subtype` records this by
  `rfl`. `subtypeHom_apply` says that it sends `x` to `(x : M)`. It is a `def`
  rather than an `abbrev`, so that the instance below is also found for concrete
  objects such as `zeroIntObj`.
- `mono_subtype`: the existing `S.subtype` is a monomorphism from
  `NonUnitalModuleCat.of A S` to `M`, by `mono_iff_injective` and injectivity of
  `Subtype.val`. The instance `mono_subtypeHom` packages it for `subtypeHom S`.

## Construction laws and representatives

- `lowerEquivalence_congr_mk`: the transported class of `Subobject.mk f` is
  `Subobject.mk ((IntegerUnitization.equivalence A).functor.map f)`, by `rfl`.
- `subobjectOrderIso_apply`: unfolds `subobjectOrderIso M P` to the inverse of
  `intUnitizedOrderIso` applied to `ModuleCat.subobjectModule` of the
  transported subobject, by `rfl`.
- `mem_subobjectOrderIso_mk`: for a monomorphism `f : N ⟶ M` and `m : M`,
  `m ∈ subobjectOrderIso M (Subobject.mk f)` if and only if `f n = m` for some
  `n : N`. The proof unfolds membership to `LinearMap.range` of the arrow of
  `Subobject.mk g`, where `g` is the extended monomorphism. That arrow is
  `(Subobject.underlyingIso g).hom ≫ g` (Mathlib's
  `Subobject.underlyingIso_hom_comp_eq_mk`), and
  `(Subobject.underlyingIso g).inv ≫ (Subobject.mk g).arrow = g`
  (`Subobject.underlyingIso_arrow`). So the arrow and `g` have the same range,
  and `g` has the underlying function of `f`.
- `coe_subobjectOrderIso_mk`: the same statement as an equality of subsets,
  `(subobjectOrderIso M (Subobject.mk f) : Set M) = Set.range f`.
- `mem_subobjectOrderIso`: for an arbitrary subobject `P`, membership is
  membership in the range of `P.arrow`, by `Subobject.mk_arrow`.
- `subobjectOrderIso_mk_subtypeHom`: the class of `subtypeHom S` is sent to
  `S`, because the range of `Subtype.val` is `S`.
- `subobjectOrderIso_symm_apply`: the inverse sends `S` to
  `Subobject.mk (subtypeHom S)`. This is the equality of actual subobjects for
  the representative `S.subtype`.
- Round trips: `subobjectOrderIso_mk_subtypeHom` is one round trip on
  submodules. `mk_subtypeHom_subobjectOrderIso` gives the other on subobjects:
  `Subobject.mk (subtypeHom (subobjectOrderIso M P)) = P`. So every subobject is
  represented by the subtype inclusion of its image. The general laws are the
  fields of the order isomorphism.

## Order

- `subobjectOrderIso_le_iff`: `subobjectOrderIso M P ≤ subobjectOrderIso M Q`
  if and only if `P ≤ Q`.
- `mk_subtypeHom_le_mk_subtypeHom_iff`:
  `Subobject.mk (subtypeHom S) ≤ Subobject.mk (subtypeHom T)` if and only if
  `S ≤ T`. This is preservation and reflection of inclusion by the inverse.
- `subobject_mk_le_mk_iff`: for monomorphisms `f₁ : N₁ ⟶ M` and `f₂ : N₂ ⟶ M`,
  the factorization order `Subobject.mk f₁ ≤ Subobject.mk f₂` holds if and only
  if `Set.range f₁ ⊆ Set.range f₂`.

The name `subobjectOrderIso` here is distinct from Mathlib's
`CategoryTheory.Subobject.subobjectOrderIso`, which concerns subobjects of a
subobject.

## Zero-action check

The section uses the published `IntegerUnitization.zeroIntObj`: the additive
group `ℤ` with the zero action of the unital ring `ℤ`, introduced locally.

- `evenZeroSubmodule` is the even subgroup `AddSubgroup.even ℤ`, as a
  `NonUnitalSubmodule` for the stored zero action `zeroIntObj.isModule`. It is
  stable because every product is `0`, which is even.
- `mem_evenZeroSubmodule`: membership means `Even m`.
  `two_mem_evenZeroSubmodule`: it contains `2`, so it is nonzero.
- `mk_subtypeHom_evenZeroSubmodule_ne_top`: the class of its subtype inclusion
  is not `⊤`. By `Subobject.top_eq_id`, `⊤` is the class of the identity, whose
  image contains `1`, and `1` is not even.
- `evenZeroSubmodule_one_smul`: the original unit `1 : ℤ` acts as zero on the
  even subobject.
- `extend_evenZeroSubmodule_inr_one_smul`: after integer unitization, the old
  unit `Unitization.inr (1 : ℤ)` still acts as zero.
- `extend_evenZeroSubmodule_one_smul`: the new unit `1 : Unitization ℤ ℤ` acts
  as the identity.

These statements use the explicit `.isModule.smul` fields of the bundled
objects, so no other scalar action on `ℤ` is involved.

## Scope

This unit identifies the subobjects of every object of `NonUnitalModuleCat A`
with its stable additive subgroups, together with the representative formulas
above. It asserts nothing about categorical Noetherian or finite-type transport,
the source's finite-type conventions, unions or intersections of subobjects,
abelian or exact functors, tensor products, complex scalars on nondegenerate
modules, or the rest of Renard's book. Those are separate obligations of the
parent program.
