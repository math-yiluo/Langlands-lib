# Residual bimodule actions on balanced tensors of original nonunital modules

This module constructs the remaining left and right actions on the actual
balanced tensor of commuting original bimodules, as used in David Renard,
*Représentations des groupes réductifs p-adiques*, French version dated 9 July
2026, I.2.2–I.2.3, printed pages 15–18 / PDF21–24. Worker 1171 authored this
Lean/Markdown pair. Worker 185 audited the sources and wrote the companion
checks module `Langlands.Algebra.NonUnitalBimoduleTensorChecks`. All names
below are in `Langlands.Algebra.NonUnitalBimoduleTensor`.

## Sources and scope

The registered governing source is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Its conventions on printed pages 5–7 / PDF11–13 do not assume rings or modules
unital, even over a unital ring. They define an `A–B`-bimodule as a left
`A`-module and right `B`-module whose actions commute. Nondegeneracy is a
separate property of modules over rings with idempotents. I.2.2 (PDF21–22)
writes `_S Y_R` for bimodules and uses the residual actions on tensors such as
`X ⊗_R Y` in its Hom adjunctions and associativity formulas. I.2.3 (PDF22–24)
notes that the forgetful and induction constructions use only commuting left
and right actions. Its functors `F_A^B(N) = B ⊗_B N` and
`P_A^B(M) = B ⊗_A M` are tensors of such bimodules carrying the residual
action. I.3.2, printed page 20 /
PDF26, notes that the right corner action of `eAe` on `A` is not unital. Its
injectivity argument uses a balanced integer-bilinear pairing and its lift
to the tensor.

Renard works with complex algebras, algebras with idempotents and nondegenerate
modules, and presupposes the tensor actions. Here `S`, `R` and `T` are arbitrary
associative nonunital rings. The modules are the published original additive
modules on specified additive groups, with no unit law, nondegeneracy,
idempotent, coefficient field or commutativity. The constructions below are
internal foundational generalizations of the source's tensor actions. They do
not supply the source's complex scalar structures or nondegeneracy conclusions.

The supplementary registered `renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`, was read
on PDF1–2 and PDF18–19. PDF1 corrects the direction of the induction
adjunctions and supplies the corner-injectivity argument with the nonunital
corner warning; the 2026 PDF24 and PDF26 already contain both. PDF18–19 adds a
complex vector-space hypothesis to an old printed-page-314 theorem. None of
these corrections affects the elementary action constructions here.

## Conventions and published inputs

A right `R`-module is exactly the published `NonUnitalModule Rᵐᵒᵖ X`; the right
action of `r` is `op r • x`. `ActionsCommute S R X` is the published
commutation predicate `∀ s r x, s • (op r • x) = op r • (s • x)`. The tensor is
exactly the published `NonUnitalModuleTensor.Tensor R X Y` with its inherited
group `NonUnitalModuleTensor.addCommGroup`, pure tensors `tmul`, universal lift
`lift`, extensionality `hom_ext` and induced maps `map`, `map_id` and
`map_comp`. Nothing here replaces the tensor or assumes a universal property.

The new actions are named definitions, not global instances. The tensor carrier
therefore has no `S`- or `T`-action available to instance search. Statements
about one-sided structures bind the named action with `letI`, and the one-sided
maps are built with `@NonUnitalModuleHom.mk` and explicit structure arguments.
Competing actions on the same carrier cannot be selected by accident.

## The two residual actions

`leftScalar hX Y s` is the published tensor map
`NonUnitalModuleTensor.map R (hX.leftActionHom s) (NonUnitalModuleHom.id R Y)`.
Here `hX.leftActionHom s` is the published right `R`-linear map `x ↦ s • x` of
`X`. This needs only commuting actions on `X`
(`hX : ActionsCommute S R X`) and the original left `R`-module `Y`.
`leftScalar_tmul` gives `s • x ⊗ y` by definition. `leftScalar_zero`,
`leftScalar_add` and `leftScalar_mul` prove that `s ↦ leftScalar hX Y s` sends
zero, sums and products to zero, sums and compositions of whole additive maps.
Each proof uses `hom_ext` and the corresponding original module law on `X`,
together with the published tensor laws `zero_tmul` and `add_tmul`.

`leftModule hX Y : NonUnitalModule S (Tensor R X Y)` uses these endomorphisms
as its scalar action. Its laws `smul_zero` and `smul_add` are additivity of
each endomorphism, and `mul_smul`, `add_smul` and `zero_smul` are the three
whole-map laws above. No `one_smul` law is part of a nonunital module.
`leftModule_smul_tmul` proves `s • (x ⊗ y) = (s • x) ⊗ y`.
`toEndHom_leftModule` identifies the whole endomorphism of `s` with the
published tensor map.

Symmetrically, `rightScalar X hY t`, for `t : Tᵐᵒᵖ`, is the tensor map
`map R (NonUnitalModuleHom.id Rᵐᵒᵖ X) (hY.rightActionHom t)`. It needs only the
right `R`-module `X` and commuting actions on `Y` (`hY : ActionsCommute R T Y`).
`rightScalar_zero`, `rightScalar_add` and `rightScalar_mul` are proved in the
same way, using `tmul_zero` and `tmul_add`. `rightScalar_op_mul` restates
`rightScalar_mul` in right-action order:
`rightScalar (op (t * t')) = rightScalar (op t') ∘ rightScalar (op t)`.
`rightModule X hY : NonUnitalModule Tᵐᵒᵖ (Tensor R X Y)` is the named original
right `T`-module. `rightModule_smul_tmul` and `rightModule_op_smul_tmul` prove
`op t • (x ⊗ y) = x ⊗ (op t • y)`, and `toEndHom_rightModule` identifies the
whole endomorphism. Neither one-sided construction uses an action on the other
factor.

## Commutation and the bundled tensor bimodule

`leftScalar_comp_rightScalar` proves that the two whole endomorphisms commute.
Both composites send `x ⊗ y` to `(s • x) ⊗ (t • y)`, so `hom_ext` applies.
`actionsCommute` deduces the published `ActionsCommute S T` for the named
actions.

`bimodule hX hY` is the published `NonUnitalBimoduleCat.of` applied to the
tensor carrier, its inherited group, `leftModule hX Y`, `rightModule X hY` and
`actionsCommute hX hY`. Its carrier universe is `max uX uY`; the ring universes
`uS`, `uR` and `uT` do not enlarge it. `bimodule_carrier`,
`bimodule_isAddCommGroup`, `bimodule_isLeftModule` and
`bimodule_isRightModule` identify the exact carrier, the inherited tensor group
and both named modules. `toEndHom_bimodule_left` and `toEndHom_bimodule_right`
identify both whole scalar maps with the published tensor maps.
`bimodule_smul_tmul` and `bimodule_op_smul_tmul` give the pure-tensor formulas
through the bundled object's own instances. `bimodule` is a definition, so
those instances are the bundled fields, not any other structure on the carrier.
`tensor X Y` abbreviates `bimodule X.actionsCommute Y.actionsCommute` for
bundled objects `X : NonUnitalBimoduleCat S R` and
`Y : NonUnitalBimoduleCat R T` in independent carrier universes.

## Induced maps

For an `S–R` intertwiner `f : X → X'` and a left `R`-linear `g : Y → Y'`,
`map_comp_leftScalar` proves on pure tensors that the published tensor map
`map R f.toRightHom g` commutes with `leftScalar`. It uses `f`'s left
`S`-linearity. `leftMap hX hX' f g` is that tensor map as an `S`-linear map
between the named left modules. `leftMap_toAddMonoidHom` identifies its whole
additive map and `leftMap_tmul` its pure-tensor values. Symmetrically,
`map_comp_rightScalar` and `rightMap hY hY' f g` handle a right `R`-linear
`f` and an `R–T` intertwiner `g`, with `rightMap_toAddMonoidHom` and
`rightMap_tmul`.

`bimoduleHom_ext` proves that an `S–T` intertwiner out of `tensor X Y` is
determined by its pure-tensor values. It applies the published `hom_ext` to
the underlying additive maps. For bundled intertwiners `f : X → X'` and
`g : Y → Y'`, `map f g` is the published
`NonUnitalModuleTensor.map R f.toRightHom g.toLeftHom`, bundled as an actual
`NonUnitalBimoduleHom S T (tensor X Y) (tensor X' Y')`. Both intertwining
conditions come from `map_comp_leftScalar` and `map_comp_rightScalar`.
`map_tmul` is the pure-tensor formula, and `map_val` identifies the complete
additive map. `map_toLeftHom` and `map_toRightHom` identify both complete
one-sided projections with `leftMap` and `rightMap`.

`map_id` and `map_comp` are the whole-map identity and composition laws, proved
from the published `NonUnitalModuleTensor.map_id` and `map_comp` by subtype
extensionality. In `map_comp` the source, intermediate and target carriers have
six independent universes `uX, uX', uX'', uY, uY', uY''`. `map_zero_left`,
`map_add_left`, `map_zero_right` and `map_add_right` prove additivity in each
intertwiner separately, with the other fixed. They follow from `zero_tmul`,
`add_tmul`, `tmul_zero` and `tmul_add` by `bimoduleHom_ext`.
`mapLeftAddHom g` and `mapRightAddHom f` package the two one-variable additive
maps between the published bimodule Hom groups. No law for simultaneous
addition in both variables is stated; the tensor map is biadditive, not
additive on pairs.

## Fixed-factor additive functors

For a fixed `X₀ : NonUnitalBimoduleCat.{uS, uR, uX} S R`,
`tensorLeft X₀` is the functor from `NonUnitalBimoduleCat.{uR, uT, uY} R T` to
`NonUnitalBimoduleCat.{uS, uT, max uX uY} S T` with object map `Y ↦ tensor X₀ Y`
and morphism map `g ↦ map (id X₀) g`. Its functor laws are `map_id` and
`map_comp`. Symmetrically, `tensorRight Y₀` has `X ↦ tensor X Y₀` and
`f ↦ map f (id Y₀)`. The instances `tensorLeft_additive` and
`tensorRight_additive` make both functors additive, by `map_add_right` and
`map_add_left` respectively. `tensorLeft_obj`, `tensorRight_obj`, their
`_carrier` forms, `tensorLeft_map` and `tensorRight_map` give the complete
object and morphism formulas. `tensorLeft_map_val` and `tensorRight_map_val`
identify each morphism's complete additive map with the published tensor map.
`tensorLeft_mapAddHom` and `tensorRight_mapAddHom` identify each functor's
additive map on Hom groups with `mapRightAddHom` and `mapLeftAddHom`.

## Equivariant universal lifts

Let `b : X →+ Y →+ Z` be an original biadditive map with the published
balancing equation `NonUnitalModuleTensor.IsBalanced R b`. If `Z` is an
original left `S`-module and `b (s • x) y = s • b x y` for all `s`, `x` and `y`,
then `lift_comp_leftScalar` proves on pure tensors that the published lift
commutes with the actions. `leftLift hX b hb hs` is the published lift as an
`S`-linear map from `leftModule hX Y` to `Z`. It needs no action of `T` and no
action on `Y` besides the left `R`-action. `leftLift_tmul` and
`leftLift_toAddMonoidHom` give its pure-tensor values and complete additive
map. `leftLift_unique` proves that any `S`-linear map with the same
pure-tensor values equals it, as complete `S`-linear maps; the proof uses the
published `lift_unique`. Symmetrically, `rightLift hY b hb ht` uses the
equation `b x (t • y) = t • b x y` for `t : Tᵐᵒᵖ` and an original right
`T`-module `Z`, with `rightLift_tmul`, `rightLift_toAddMonoidHom` and
`rightLift_unique`.

For a bundled target `Z : NonUnitalBimoduleCat S T`, whose actions commute,
`lift b hb hs ht` is the same published lift, bundled as an
`S–T` intertwiner out of `tensor X Y`. `lift_tmul` and `lift_val` give its
pure-tensor formula and complete additive map. `lift_toLeftHom` and
`lift_toRightHom` identify its one-sided projections with `leftLift` and
`rightLift`. `lift_unique` proves uniqueness as equality of complete bundled
intertwiners, by `bimoduleHom_ext`. Balancing and both equivariance conditions
are equations on the supplied `b`, not properties of a replacement tensor.

## Universes and checks

The ring universes `uS`, `uR` and `uT`, the factor universes `uX` and `uY`,
the target universe `uZ` and the further carrier universes `uX'`, `uY'`, `uX''`
and `uY''` are independent throughout. The companion module
`Langlands.Algebra.NonUnitalBimoduleTensorChecks` contains the unapplied
universe checks, competing-structure checks, subsingleton and zero-action
cases, and the integer examples.

## Not covered here

The canonical coefficient scalars recovered from nondegenerate tensors, the
comparison (I.2.1.2) with unitized tensors, nondegeneracy of tensors,
associativity (I.2.2.4) and (I.2.2.7), the tensor–Hom adjunctions
(I.2.2.1)–(I.2.2.6), exactness, and the source's forgetful, pseudo-forgetful
and induction functors of I.2.3 are separate successor definitions,
statements and proofs. So are the corner induction and equivalence of I.3.
The fixed-factor functors here are additive functors between the ambient
categories of all original bimodules. They are not identified with the
source's functors between nondegenerate module categories. Development
compilation is distinct from independent semantic acceptance and Library
publication.
