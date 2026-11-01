# Natural maps and fixed-variable functors on residual-action Hom spaces

Author: Worker 1174. This is the naturality and categorical-packaging
definition unit of task `4cc99517-b08b-4532-a78f-5075d458f4ab`, below the
Renard whole-book task `f5d1f399-a1f8-4ab5-a981-90b92abd4857`. It imports
the core unit `Langlands.Algebra.NonUnitalBimoduleHomActions` by Worker 702,
whose paired Markdown explains the residual actions themselves, and adds
declarations to the same namespace.

## Sources and scope

The governing source is David Renard, *Représentations des groupes réductifs
p-adiques*, French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The Chapter I conventions are printed pp.5–7/PDF11–13. I.2.2, printed
pp.15–16/PDF21–22, states the tensor-Hom isomorphisms (I.2.2.1) for
`X_R`, `_R Y_S`, `Z_S` and (I.2.2.3) for `_R X`, `_S Y_R`, `_S Z`, and
remarks that they are natural in all three variables `X`, `Y` and `Z`.
Naturality in `Y` and `Z` requires the Hom space `Hom_S(Y, Z)` to depend
functorially on `Y` and `Z` as a module over the residual ring. I.2.3,
printed pp.16–18/PDF22–24, uses the same Hom construction with the
source-precomposition action on `Hom_B(B, N)`. These pages were read for
this unit.

The supplementary registered source `renard-2010-corrections-complements`,
SHA256 `fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
was consulted at PDF1–2 and PDF18–19. Its correction for printed p.299
fixes the induced map on Hom spaces as postcomposition in the covariant
variable and precomposition in the contravariant variable. This is the
order used here: `h ↦ g ∘ h ∘ f` for `f : Y' → Y` and `g : Z → Z'`. Its
correction for printed p.20 concerns adjunction orientation, which this
unit does not treat.

Renard works with complex algebras, and the subsequent functors use
nondegenerate modules and nondegenerate parts of Hom spaces. The present
declarations are internal prerequisites over arbitrary associative
nonunital rings `S`, `R`, `T` in independent universes, and abelian groups
in independent universes with their specified original actions. A right
action is a left action of the opposite ring. They use only the published
`NonUnitalModuleHom` with its pointwise group and `comp`,
`NonUnitalBimoduleHom` and `NonUnitalBimoduleCat`, and the named residual
actions `sourceAction`, `targetAction` and `rightSourceAction` of the core
unit. No complex linearity, unit law, nondegeneracy or alternative Hom
carrier is introduced or asserted.

## Identity, composition and separate additivity of composition

All declarations below are in
`Langlands.Algebra.NonUnitalBimoduleHomActions`. The core unit provides
the additive maps `precomposeAddHom f : h ↦ h.comp f`,
`postcomposeAddHom g : h ↦ g.comp h` and `mapAddHom f g : h ↦ g.comp
(h.comp f)` on original Hom groups.

`precomposeAddHom_id`, `postcomposeAddHom_id` and `mapAddHom_id` state
that identity maps give the identity additive map.
`precomposeAddHom_comp` states contravariance,
`precomposeAddHom (f.comp f') = (precomposeAddHom f').comp
(precomposeAddHom f)`, and `postcomposeAddHom_comp` states covariance.
`mapAddHom_eq_precomposeAddHom_comp` writes `mapAddHom f g` as
postcomposition followed by precomposition (the two commute, since both
orders give `g ∘ h ∘ f`). `mapAddHom_comp` is the whole-map composition
law

```text
mapAddHom (f.comp f') (g'.comp g) = (mapAddHom f' g').comp (mapAddHom f g).
```

All of these hold by `rfl`, since original composition is definitionally
associative.

`mapAddHom_add_left` and `mapAddHom_zero_left` state additivity in the
source map `f` for fixed `g`. Their proofs evaluate both sides at `y`
and use that `h` and `g` preserve addition and zero. `mapAddHom_add_right`
and `mapAddHom_zero_right` state additivity in the target map `g` for fixed
`f`; these hold pointwise by the definition of the Hom group. Joint
additivity in the pair `(f, g)` is false in general and is not asserted:
`g ∘ h ∘ f` is bilinear, so adding both maps at once produces cross terms.

## Bundled one-sided Hom modules

`sourceHom hY Z` is the object of `NonUnitalModuleCat.{uR, max uY uZ} R`
whose carrier is `NonUnitalModuleHom S Y Z`, with its published group and
the module structure `sourceAction hY`. Here `hY : ActionsCommute S R Y`,
and `Z` needs only its original left `S`-action. Similarly,
`targetHom Y hZ` is the object of `NonUnitalModuleCat.{uT, max uY uZ} Tᵐᵒᵖ`
on the same carrier with `targetAction hZ`, for `hZ : ActionsCommute S T Z`
and `Y` with only its left `S`-action. `rightSourceHom hY Z` is the object
of `NonUnitalModuleCat.{uR, max uY uZ} Rᵐᵒᵖ` on
`NonUnitalModuleHom Sᵐᵒᵖ Y Z` with `rightSourceAction hY`, for
`hY : ActionsCommute R S Y` and `Z` with only its right `S`-action; this is
the Hom of (I.2.2.1).

The `_carrier`, `_isAddCommGroup` and `_isModule` lemmas for each object
state by `rfl` that the carrier, the group and the module structure are
exactly the specified ones. `forgetToLeft_obj_hom` and
`forgetToRight_obj_hom` state that the published forgetful functors send
the core bimodule `hom hY hZ` to `sourceHom hY Z` and `targetHom Y hZ`.

These objects are bundled because the residual actions are named
structures, not global instances. Typing a map between bundled objects lets
instance resolution find exactly the named actions on its source and
target.

## One-sided natural maps

`sourceMap hY hY' f g` is the original left `R`-linear map
`sourceHom hY Z → sourceHom hY' Z'` with underlying additive map
`mapAddHom f.toLeftHom g`. Here `f : NonUnitalBimoduleHom S R Y' Y` is an
`S`–`R` bimodule intertwiner and `g : NonUnitalModuleHom S Z Z'` is only
left `S`-linear; no `T`-action is involved. Linearity is the identity
`g (h (f (op r • y))) = g (h (op r • f y))`, which is `f.map_op_smul`.

`targetMap hZ hZ' f g` is the original right `T`-linear map
`targetHom Y hZ → targetHom Y' hZ'` with underlying additive map
`mapAddHom f g.toLeftHom`. Here `f : NonUnitalModuleHom S Y' Y` is only
left `S`-linear and `g : NonUnitalBimoduleHom S T Z Z'`; no `R`-action is
involved. Linearity is `g (t • h (f y)) = t • g (h (f y))`, which is
`g.map_smul_right`.

`rightSourceMap hY hY' f g` is the original right `R`-linear map
`rightSourceHom hY Z → rightSourceHom hY' Z'` with underlying additive map
`mapAddHom f.toRightHom g`, for an `R`–`S` bimodule intertwiner
`f : NonUnitalBimoduleHom R S Y' Y` and a right `S`-linear
`g : NonUnitalModuleHom Sᵐᵒᵖ Z Z'`. Linearity is `f.map_smul_left`. It
directly uses the supplied left `R`-action on `Y`, with no adapter
through a double opposite.

For each of the three maps, `_toAddMonoidHom` gives the entire underlying
additive map, `_apply` gives the value `g.comp (h.comp f)` as an original
Hom, and `_apply_apply` gives the pointwise formula `g (h (f y))`. The
lemmas `_id` and `_comp` give the identity law and the composition law
`(f ∘ f', g' ∘ g) ↦ (f', g') ∘ (f, g)`, with all six carriers in
independent universes. All of these hold by `rfl`.

## The bimodule natural map

For `f : NonUnitalBimoduleHom S R Y' Y` and
`g : NonUnitalBimoduleHom S T Z Z'`, the definition `homMap hY hY' hZ hZ' f g` is
the actual `R`–`T` bimodule intertwiner

```text
H(f,g) : hom hY hZ → hom hY' hZ',   H(f,g)(h) = g.toLeftHom.comp (h.comp f.toLeftHom).
```

It is the published subtype `NonUnitalBimoduleHom` on the core bimodules
(not a `NonUnitalBimoduleCat` morphism, so that the four carriers keep
independent universes). Its underlying additive map is
`mapAddHom f.toLeftHom g.toLeftHom`. Its left and right linearity proofs
are the `map_smul'` fields of `sourceMap` and `targetMap`.

`homMap_val` gives this entire underlying additive map, and
`homMap_val_eq_comp` writes it as
`(postcomposeAddHom g.toLeftHom).comp (precomposeAddHom f.toLeftHom)`.
`homMap_apply` gives the original-Hom value, and `homMap_apply_apply` gives
the pointwise formula `g (h (f y))`. `homMap_toLeftHom` and
`homMap_toRightHom` state that the two one-sided projections are exactly
`sourceMap hY hY' f g.toLeftHom` and `targetMap hZ hZ' f.toLeftHom g`.
`homMap_id` and `homMap_comp` are the whole-map identity and composition
laws, and they hold by `rfl`.

`homMap_add_left`, `homMap_zero_left`, `homMap_add_right` and
`homMap_zero_right` give additivity in each variable separately. They
follow from the corresponding `mapAddHom` lemmas by subtype
extensionality. `homMapAddHomLeft` bundles `f ↦ H(f, g)` for fixed `g` as
an additive map, and `homMapAddHomRight` bundles `g ↦ H(f, g)` for fixed
`f`. Their `_apply` lemmas are `simp` lemmas.

## Fixed-variable additive functors

For a fixed `S`–`R` bimodule `Y` with `hY : ActionsCommute S R Y`,

```text
homCovariantFunctor T hY :
  NonUnitalBimoduleCat.{uS, uT, uZ} S T ⥤ NonUnitalBimoduleCat.{uR, uT, max uY uZ} R T
```

sends `Z` to `hom hY Z.actionsCommute` and `g` to
`homMap hY hY _ _ (NonUnitalBimoduleHom.id S R Y) g`. The functor laws
hold by `rfl`. The instance `homCovariantFunctor_additive` states that it
is additive, using `homMap_add_right`. `homCovariantFunctor_obj`,
`homCovariantFunctor_obj_carrier` and `homCovariantFunctor_map` give the
complete object, carrier and map formulas. `homCovariantFunctor_map_val`
states that the underlying additive map of the image of `g` is
postcomposition by `g`.

For a fixed `S`–`T` bimodule `Z` with `hZ : ActionsCommute S T Z`,

```text
homContravariantFunctor R hZ :
  (NonUnitalBimoduleCat.{uS, uR, uY} S R)ᵒᵖ ⥤ NonUnitalBimoduleCat.{uR, uT, max uY uZ} R T
```

sends `Y` to `hom Y.unop.actionsCommute hZ` and `f` to
`homMap _ _ hZ hZ f.unop (NonUnitalBimoduleHom.id S T Z)`. The instance
`homContravariantFunctor_additive` uses `homMap_add_left` and Mathlib's
preadditive structure on the opposite category, in which `(f + f').unop =
f.unop + f'.unop`.
`homContravariantFunctor_obj`, `homContravariantFunctor_obj_carrier`,
`homContravariantFunctor_map` and `homContravariantFunctor_map_val` give
the complete object, carrier and map formulas; the image of `f` has
precomposition by `f.unop` as its underlying additive map.

Each functor fixes the carrier universe of its source category (`uZ` for
the covariant functor, `uY` for the contravariant one). It lands in the
actual Hom carrier universe `max uY uZ`. Neither functor is asserted to be
exact, and no functor of two variables is constructed.

## Checks

The companion `NonUnitalBimoduleHomNaturalityChecks` module checks the
complete unapplied interfaces, competing instances, subsingleton carriers,
the nonzero integer Hom with zero residual actions, and the failure of
joint additivity. Its paired Markdown describes these checks.

## Remaining work

This unit gives only the natural maps of the residual-action Hom spaces in
the variables `Y` and `Z`, and their categorical packaging. It does not
assert or construct the tensor-Hom isomorphisms (I.2.2.1)–(I.2.2.7), their
naturality in `X`, any adjunction or exactness, a nondegenerate part of
Hom, or comparison with recovered coefficient scalars or unitization. The
actual `F`, pseudo-`F`, `I` and `P` functors of I.2.3 and later sections
remain separate definition or proposition/proof units. The tensor-action,
corner and annihilator-quotient tasks keep their existing scope.
