# The actual eA-annihilator quotient

This file constructs the quotient by the stable annihilator of a right ideal,
its original additive intertwiners, and its additive functors. Its namespace is
`Langlands.Algebra.IdempotentAnnihilator`; its module is
`Langlands.Algebra.IdempotentAnnihilatorQuotient.ExplicitAction`.

## Original source and scope

The governing original is David Renard, *Représentations des groupes réductifs
p-adiques*, French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The definition in I.3.2, printed page 20 / PDF page 26, gives the nondegenerate
module `M_e` as `M/F(eA,M)`, where `F(eA,M)` consists of the vectors annihilated
by every element of the right ideal `eA`. The standing context of I.3.1–2,
printed page 19 / PDF page 25, is a complex idempotented algebra. The original
nonunital conventions are at printed pages 5–6 / PDF pages 11–12. Worker 633
read these four PDF pages and verified the registered source hash.

The ambient arbitrary-ring construction and the categorical packaging below
are derived implementation content. They use only an associative
`NonUnitalRing A`, an actual `Idempotent A`, and a specified original additive
`NonUnitalModule A M`. The ring may be noncommutative, may lack a unit, and may
be zero. There is no unit-action law, local-unit hypothesis, nondegeneracy
hypothesis, or common-universe restriction on the ambient construction.
Nondegeneracy is used only to restrict the functor. That restriction has exactly
the source's underlying original additive quotient, projection, and induced
maps. This is the scalar-free generalization of the source construction.

The file does not construct a new complex-linear category comparison. Integer
linearity here is the canonical linearity of additive group homomorphisms,
not an assertion of complex linearity for every original additive intertwiner.
Any further comparison with a category of complex-linear morphisms must retain
its separately supplied scalar compatibility. The later quotient-idempotence
lemma, comparison on e-fixed parts, tensor induction, generated subcategories,
simple-class bijection, and equivalence criterion remain separate statement
and proof obligations. This file does not assume them or claim completion of
I.3.2.

## The stable annihilator

`submodule e M : NonUnitalSubmodule A M` has precisely the membership condition

```text
m ∈ submodule e M  ↔  ∀ a : A, ((e : A) * a) • m = 0.
```

`mem_submodule` records this definition. The defining proofs use `smul_add`,
`smul_neg`, and `smul_zero` for additive closure. Stability is the associativity
calculation `(e*a) • (b • m) = (e*(a*b)) • m = 0`. The hypothesis ranges over the
whole right ideal; no inference from `e • m = 0` for an arbitrary vector is made.

`smul_eq_zero_of_mem` specializes the condition to `a=e` and uses `e*e=e`.
`le_submodule_iff` says, for every original stable additive subgroup `S`,

```text
S ≤ submodule e M  ↔  ∀ m ∈ S, (e : A) • m = 0.
```

For the reverse implication, stability places `a • m` in `S`, where `e` kills it.
Thus the annihilator is the largest original stable subgroup killed by `e`.
These are intrinsic laws of the construction, valid without nondegeneracy.

## The actual quotient and chosen actions

`quotient e M` is the existing Mathlib quotient
`M ⧸ (submodule e M).toIntCompatible.toSubmodule`.
The published `NonUnitalSubmodule.toIntCompatible` retains the original additive
subgroup and action. In fact `quotient_eq_addSubgroupQuotient` proves equality
of this carrier with `M ⧸ (submodule e M).toAddSubgroup` by reflexivity.
`quotientAddCommGroup` names its inherited additive group;
`quotientAddCommGroup_eq` identifies it with the additive-subgroup quotient group.
This is a constructed quotient carrier, with no quotient properties assumed.

`quotientNonUnitalModule` names the published
`CompatibleSubmodule.quotientNonUnitalModule` for this subgroup and the canonical
integer-linearization of the specified original action. It is a local instance
only inside this file. The public definitions contain that selected structure;
no global competing quotient action is installed.
`quotient_smul_mk` explicitly names this structure and gives
`a • [m] = [a • m]`, with the right-hand action the original one.

`projection` is the published `mkQNonUnitalModuleHom` on the same original action.
`projection_apply` gives `m ↦ [m]`; `projection_toAddMonoidHom` identifies the
entire additive map with the existing `mkQ`.
`projection_surjective` uses the actual representative-surjectivity theorem.
`projection_eq_zero_iff` proves `[m]=0` exactly when `m` belongs to the constructed
annihilator, by the existing quotient zero criterion.

## Induced maps and universal descent

For an original additive intertwiner `f : NonUnitalModuleHom A M N`,
`map_mem` proves `f(F(eA,M)) ⊆ F(eA,N)` by applying `f` to the annihilation
equations. `le_comap` is this very containment in the compatible-submodule API.
`map e f` converts `f` by `toIntLinearIntertwiner`, applies the published
`LinearIntertwiner.mapQ`, and returns its original additive intertwiner.
`map_apply_mk` is `[m] ↦ [f m]`; `map_toAddMonoidHom` identifies the whole map
with the existing submodule quotient map of the canonical integer-linear map.
No source or target action is replaced by an unrelated action on its carrier.

`map_id`, `map_comp`, `map_zero`, `map_add`, and `map_neg` are equalities of
complete original intertwiners. Their proofs use quotient representatives and
the corresponding original additive-map laws. `mapAddHom` bundles this Hom map
as an actual additive homomorphism. `map_comp_projection` is the full naturality
equation, not only a representative equation. The ring, source, target, and
third carrier universes are independent in the composition law.

`desc e f h` constructs the actual descent of an original intertwiner `f`
whose value is zero on every vector of `F(eA,M)`. It uses the published
`LinearIntertwiner.liftQ`. `desc_apply_mk` gives `[m] ↦ f m`, and
`desc_toAddMonoidHom` identifies the full map with the existing linear quotient
lift. `desc_comp_projection` proves whole-map factorization. `desc_unique`
uses the surjectivity of the actual projection to prove uniqueness;
`existsUnique_desc` bundles this intrinsic universal property. The target
carrier universe remains independent of the source and ring universes.

## Additive functors and the nondegenerate restriction

`obj e M` explicitly stores `quotientAddCommGroup e M` and
`quotientNonUnitalModule e M` in `NonUnitalModuleCat A`.
`obj_carrier` and `obj_isModule` give these choices. `functor e` has this object
map and `map e` as its morphism map, with actual identity and composition
proofs. `functor_obj` and `functor_map` give its complete formulas, and
`functor_additive` proves additivity for the published pointwise Hom groups.
`projectionNatTrans` is an actual natural transformation from the identity
functor; `projectionNatTrans_app` gives its original quotient projection.

`isNondegenerate` proves that this quotient of a specified nondegenerate module
is nondegenerate. It lifts a coset to `m`, takes an actual idempotent fixing `m`,
and applies the quotient intertwining law. It does not require the ring to be
idempotented. `nondegenerateObj` stores this proof together with the very same
ambient quotient object. `nondegenerateFunctor` uses `map e f.hom` on morphisms
of the published full subcategory, and `nondegenerateFunctor_additive` uses its
inherited additive structure. The object and underlying-map formulas are
`nondegenerateFunctor_obj` and `nondegenerateFunctor_map_hom`.
`nondegenerateProjectionNatTrans` gives the actual restricted natural projection,
with component formula `nondegenerateProjectionNatTrans_app_hom`.

The equality `nondegenerateFunctor_comp_inclusion` identifies the restricted
functor followed by the published `nondegenerateInclusion` with that inclusion
followed by the ambient quotient functor. The equality is reflexive: these
constructions store the same objects and original maps.
`nondegenerateProjection_app_inclusion` similarly identifies each included
restricted projection with the corresponding ambient component.

## Zero cases and declaration checks

`submodule_eq_univ_of_idempotent_eq_zero` and
`submodule_eq_univ_of_zero_action` prove that the annihilator contains every
original vector in these respective cases. Their quotient subsingleton laws
are `quotient_subsingleton_of_idempotent_eq_zero` and
`quotient_subsingleton_of_zero_action`; these establish triviality of the actual
quotient. More generally `quotient_eq_zero_of_forall_mem` makes every coset zero.
`quotient_subsingleton_of_subsingleton` covers the zero carrier under every
specified original action.

The file ends with unapplied, fully quantified declaration checks for the core
subgroup, quotient, projections, induced maps, descents, additive Hom map,
functors, and natural transformations. Separate checks use distinct universes
`(0,1,2)` for maps and `(2,1,0)` for descent. Explicit `NonUnitalModuleHom`
structure arguments verify that projections, maps, and descents retain their
named quotient actions even when other quotient actions are local instances.
The named action formula is checked under the same competition. Concrete
checks cover the zero idempotent, the specified zero original action of ℤ on ℤ
(despite its usual scalar action), and the zero `PUnit` carrier. All proofs
compile without proof holes or new axioms.

Integration placement: this reviewed implementation is preserved in the ExplicitAction submodule; the parent `Langlands.Algebra.IdempotentAnnihilatorQuotient` imports both reviewed interfaces.
