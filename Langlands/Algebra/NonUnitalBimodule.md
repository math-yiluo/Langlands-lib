# Commuting original nonunital bimodules and their additive category

Author: Worker 1174. This is the focused definition unit for task
`1490cf73-f76f-469c-b407-e7bcae6db5ca`. It is a prerequisite of the
whole-book task `f5d1f399-a1f8-4ab5-a981-90b92abd4857`.

## Source and provenance

The governing source is David Renard, *Représentations des groupes réductifs
p-adiques*, French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The Chapter I conventions and I.1.2 (printed pp.5–8/PDF11–14) fix the
original actions. These are the published `NonUnitalModule`, with right
modules taken as left modules over the opposite ring. I.2.2 (printed
pp.15–16/PDF21–22) introduces the notation `_S Y_R` for a bimodule, left
over `S` and right over `R`. I.2.3 (printed pp.16–18/PDF22–24) builds the
forgetful and induction functors from a left action and a right action on
the same group. It notes that the construction uses "seulement" these two
structures "et le fait que les actions à gauche et à droite commutent". It
then assumes separately that `B` is a *nondegenerate* `A−B`- or
`B−A`-bimodule. It also observes that this can fail when the bimodule
structure comes from a ring morphism. PDF21–24 were read in full for this
unit.

The source works with `ℂ`-algebras. This module works over arbitrary
nonunital rings, with the additive actions of the published
`NonUnitalModule`. No `ℂ`-linear structure is formalized here. The
predicate, the subgroup, the category and the bundled Hom interfaces are
internal general prerequisites. Specialized to the source's algebras with
idempotents, they give the commuting-bimodule data used in those passages.
`NonUnitalBimoduleCat A B` is the source's `A−B`-bimodule `_A M_B`, left
over `A` and right over `B`.

## Commutation and nondegeneracy

Fix `A : Type uA`, `B : Type uB` and `M : Type uM`, all in independent
universes, with `[NonUnitalRing A]`, `[NonUnitalRing B]`, `[AddCommGroup M]`,
the specified left action `[NonUnitalModule A M]` and the specified right
action `[NonUnitalModule Bᵐᵒᵖ M]`. No unit law is assumed.

- `ActionsCommute A B M : Prop` is
  `∀ a b m, a • (op b • m) = op b • (a • m)`.
- `IsNondegenerateBimodule A B M : Prop` is
  `IsNondegenerate A M ∧ IsRightNondegenerate B M`, the conjunction of the
  two published one-sided predicates. It is a separate definition and is
  not a field of the commutation predicate or of the category.
- `actionsCommute_iff_smulCommClass` states
  `ActionsCommute A B M ↔ SMulCommClass A Bᵐᵒᵖ M`.
  `actionsCommute_iff_smulCommClass'` is the same with the scalar order
  `SMulCommClass Bᵐᵒᵖ A M`. Both proofs evaluate the class field at
  `op b`, or unwrap an opposite scalar with `unop`. The named adapters
  `ActionsCommute.smulCommClass`, `smulCommClass'`, `of_smulCommClass` and
  `of_smulCommClass'` are the four directions. `ActionsCommute.smul_comm`
  is the equation for an opposite scalar `b : Bᵐᵒᵖ`. The existing Mathlib
  class is reused; no second set of commutation laws is introduced.

Degenerate and trivial cases:

- `actionsCommute_zero_left` and `actionsCommute_zero_right`: the published
  original zero action `NonUnitalModule.zero` on either side commutes with
  every action on the other side. The proofs are `smul_zero`.
- `actionsCommute_of_subsingleton` and
  `isNondegenerateBimodule_of_subsingleton`: on a subsingleton carrier any
  two actions commute and are nondegenerate on both sides. The idempotent
  `0` (`IsIdempotentElem.zero`) fixes each vector.
- `not_isNondegenerate_zero`: on a nontrivial group the zero action of any
  ring is not nondegenerate. A nonzero `m` would satisfy `e • m = 0 = m`.
- `exists_actionsCommute_not_isNondegenerateBimodule`: for every pair of
  rings and every nontrivial `M`, the two zero actions commute but are not
  two-sided nondegenerate. So the commutation equation alone does not imply
  nondegeneracy.

## Scalars as original Homs

Given `h : ActionsCommute A B M`:

- `h.leftActionHom a : NonUnitalModuleHom Bᵐᵒᵖ M M` is the action of
  `a : A` as an original right `B`-linear endomorphism. Its additive map is
  exactly the published `NonUnitalModule.toEndHom _ a`, and its linearity
  is `h.smul_comm`.
- `h.rightActionHom b : NonUnitalModuleHom A M M`, for `b : Bᵐᵒᵖ`, is the
  action of `b` as an original left `A`-linear endomorphism, with additive
  map `NonUnitalModule.toEndHom _ b`.
- Evaluation: `leftActionHom_apply` gives `h.leftActionHom a m = a • m`.
  `rightActionHom_apply` gives `h.rightActionHom b m = b • m`.
- Whole additive maps: `leftActionHom_toAddMonoidHom` and
  `rightActionHom_toAddMonoidHom` hold definitionally.
- Scalar zero and addition: `leftActionHom_zero`, `leftActionHom_add` and
  their right versions. The proofs are the original `zero_smul` and
  `add_smul` laws, using the published pointwise group on
  `NonUnitalModuleHom`.
- Scalar multiplication becomes composition in the published Hom interface:
  `leftActionHom_mul` gives `h.leftActionHom (a * a') =
  (h.leftActionHom a).comp (h.leftActionHom a')`. `rightActionHom_mul`
  gives the same for `Bᵐᵒᵖ`. In right-action notation,
  `rightActionHom_op_mul` gives
  `h.rightActionHom (op (b * b')) =
  (h.rightActionHom (op b')).comp (h.rightActionHom (op b))`, by the
  published `right_mul_smul`. Only the published `NonUnitalModuleHom.comp`
  is used. No ring or monoid instance on endomorphisms is assumed.
- Additive scalar-to-Hom maps: `h.leftActionAddHom :
  A →+ NonUnitalModuleHom Bᵐᵒᵖ M M` and `h.rightActionAddHom :
  Bᵐᵒᵖ →+ NonUnitalModuleHom A M M`, with `_apply` lemmas. Composed with
  the published `NonUnitalModuleHom.toAddMonoidHomAddHom`, they are exactly
  the additive maps underlying the published `NonUnitalModule.toEndHom`
  (`toAddMonoidHomAddHom_comp_leftActionAddHom` and its right version, by
  `rfl`).

## The intertwiner subgroup

For a second carrier `N : Type uN` in its own universe, with its own
specified actions, `bimoduleHomGroup A B M N : AddSubgroup (M →+ N)` is the
set of additive maps `f` with `f (a • m) = a • f m` for all `a : A` and
`f (b • m) = b • f m` for all `b : Bᵐᵒᵖ` (`mem_bimoduleHomGroup`, by
`Iff.rfl`). Zero, sums and negatives are closed under these equations by
`smul_zero`, `smul_add` and `smul_neg`.

`NonUnitalBimoduleHom A B M N` is the subtype of this subgroup. It carries
the group inherited from `M →+ N`, so `zero_apply`, `add_apply`,
`neg_apply` and `sub_apply` are pointwise and definitional. The API
provides a function coercion, `ext`, `map_zero`, `map_add`,
`map_smul_left`, `map_smul_right`, `map_op_smul` (right-action notation),
the constructor `mk'`, and the additive inclusion
`toAddMonoidHom = (bimoduleHomGroup A B M N).subtype`.

- `NonUnitalBimoduleHom.id` and `comp` use `AddMonoidHom.id` and
  `AddMonoidHom.comp`. Composition preserves both equations by rewriting
  twice. `id_val`, `comp_val`, `id_apply`, `comp_apply`, `id_comp`,
  `comp_id` and `comp_assoc` hold definitionally. `comp_add` uses
  additivity of the postcomposed map, and `add_comp` holds by evaluation.
- Projections to the published original Homs: `toLeftHom f :
  NonUnitalModuleHom A M N` and `toRightHom f :
  NonUnitalModuleHom Bᵐᵒᵖ M N` keep the whole additive map
  (`toLeftHom_toAddMonoidHom`, `toRightHom_toAddMonoidHom`). Both are
  injective. `ofHoms` combines a left Hom and a right Hom with equal
  additive maps, and `toLeftHom_ofHoms` and `toRightHom_ofHoms` recover
  each one.
- `toLeftHomAddHom` and `toRightHomAddHom` are these projections as
  additive homomorphisms. Followed by the published `toAddMonoidHomAddHom`,
  each is the inclusion `toAddMonoidHom` (two `rfl` lemmas).
- `toLeftHom_id`, `toRightHom_id`, `toLeftHom_comp` and `toRightHom_comp`
  identify the projections of identities and composites with the published
  `NonUnitalModuleHom.id` and `NonUnitalModuleHom.comp`.

## Right-regular action and the regular bimodule

`NonUnitalModule.rightRegular A : NonUnitalModule Aᵐᵒᵖ A` is the specified
action `op b • m = m * b` on any `NonUnitalRing A`. Its laws are
`zero_mul`, `add_mul`, `mul_add`, `mul_zero` and associativity:
`m * (c * b) = (m * c) * b` gives `(b * c) • m = b • (c • m)` in `Aᵐᵒᵖ`.
Like the published `NonUnitalModule.regular`, it is an `abbrev`, not a
global instance. `rightRegular_smul` and `regular_smul` record the exact
formulas for the explicitly selected actions. `regular_actionsCommute`
proves that the published left-regular action `NonUnitalModule.regular A`,
which is reused here, commutes with `rightRegular A`, by
`a * (m * b) = (a * m) * b`. `NonUnitalBimoduleCat.regular A` bundles these
two actions on `A`.

## The category and its forgetful functors

`NonUnitalBimoduleCat.{uA, uB, uM} A B` has fields `carrier : Type uM`,
the instance fields `isAddCommGroup`, `isLeftModule : NonUnitalModule A
carrier` and `isRightModule : NonUnitalModule Bᵐᵒᵖ carrier`, and the
proof field `actionsCommute`. The carrier universe `uM` is independent of
both ring universes. `of` bundles two specified commuting actions. The
instances `smulCommClass` and `smulCommClass'` are derived from the stored
proof, which is the only commutation datum.

- `category`: Homs are `NonUnitalBimoduleHom A B M N`, identities are
  `NonUnitalBimoduleHom.id`, and `f ≫ g = NonUnitalBimoduleHom.comp g f`.
  The laws hold definitionally (`hom_def`, `id_def`, `comp_def`).
- `preadditive`: the Hom groups are the inherited subgroup groups
  (`homGroup_eq`, by `rfl`), with `comp_add` and `add_comp` above.
- `forgetToLeft A B : NonUnitalBimoduleCat A B ⥤ NonUnitalModuleCat A`
  sends `M` to `NonUnitalModuleCat.of A M` and `f` to `f.toLeftHom`.
  `forgetToRight A B : NonUnitalBimoduleCat A B ⥤ RightNonUnitalModuleCat B`
  sends `M` to `NonUnitalModuleCat.of Bᵐᵒᵖ M` and `f` to `f.toRightHom`.
  The exact formulas are `forgetTo*_obj`, `forgetTo*_obj_carrier`,
  `forgetTo*_obj_isAddCommGroup` (the same additive group),
  `forgetTo*_obj_isModule` (exactly the specified left action, resp. right
  action), `forgetTo*_map` and `forgetTo*_map_toAddMonoidHom` (the whole
  additive map). `forgetTo*_mapAddHom` identifies the functor on Hom groups
  with `toLeftHomAddHom`, resp. `toRightHomAddHom`.
- `forgetToLeft_additive` and `forgetToRight_additive` hold by `rfl`, since
  addition is pointwise on both sides. `forgetToLeft_faithful` and
  `forgetToRight_faithful` follow from injectivity of the projections.

## Interface checks

The final section of the Lean file checks the following:

- Every main declaration is checked in fully unapplied form at arbitrary
  universes `uA, uB, uM, uN, uP`. The preadditive structure and both
  additive functors are also found by `inferInstance`.
- The category and both additive functors are checked at universes
  `{0,0,1}`, `{1,1,0}`, `{0,1,0}` and `{1,0,1}`, which includes both
  unequal ring/carrier directions. The subgroup is checked with source and
  target carriers in different universes, in both directions.
- On `A = B = M`, the forgetful functors applied to the regular bimodule
  return exactly `NonUnitalModule.regular A` and `rightRegular A`, and the
  selected right action is `op b • m = m * b`. The zero bimodule and the
  two mixed regular/zero bimodules on the same carrier keep their selected
  actions.
- For an arbitrary `G : AddCommGroup A`, unrelated to the ring addition, or
  `G : AddCommGroup M`, the bundled object keeps `G`. The intertwiner
  subgroup elaborates for explicitly selected `G` and actions.
- Zero actions on `ℤ` commute but are degenerate, over arbitrary rings.
  Zero actions of the unital ring `ℤ` form an object of
  `NonUnitalBimoduleCat ℤ ℤ` without any unit law.
- The zero rings `PUnit` have a preadditive bimodule category, and a
  bimodule on the nonzero group `ℤ`.
- On the trivial carrier `PUnit`, any actions commute and are
  nondegenerate, and give an object of the category.

No field, unit, commutativity, nontriviality, dimension, finiteness or
idempotented-ring hypothesis is used anywhere.

## Limits

This unit does not formalize I.2.2, I.2.3 or the whole book. Out of scope:
tensor products and Hom modules of bimodules and their actions or functors;
original/unitized tensor comparisons; the source's forgetful functor
`F^B_A`, the pseudo-forgetful functor, and the induction functors `I^B_A`
and `P^B_A`; adjunctions; exactness; nondegenerate-part comparisons; and
scalar-hom bimodule comparisons. These remain separate successors. No
`ℂ`-linear structure, no scalar restriction along a ring morphism, and no
endomorphism-ring instance is introduced.
