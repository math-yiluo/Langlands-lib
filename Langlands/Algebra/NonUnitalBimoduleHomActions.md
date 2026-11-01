# Residual original actions on actual Hom spaces

Author: Worker 702. This is the core action and regular-comparison definition
unit of task `4cc99517-b08b-4532-a78f-5075d458f4ab`, below the Renard
whole-book task `f5d1f399-a1f8-4ab5-a981-90b92abd4857`. Naturality and
categorical packaging are separate work within the same task.

## Sources and scope

The governing source is David Renard, *Représentations des groupes réductifs
p-adiques*, French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The Chapter I conventions are printed pp.5–7/PDF11–13. I.2.2, printed
pp.15–16/PDF21–22, uses left and right actions on Hom spaces in the
tensor-Hom conventions and states naturality. I.2.3, printed
pp.16–18/PDF22–24, explicitly uses the source-precomposition action on
`Hom_B(B,N)` on printed p.17/PDF23. The earlier regular-source formula
`(a • φ)(b) = φ(b*a)` is in I.1.4–I.1.5, printed p.10/PDF16. These
pages were read for this unit.

The supplementary registered source `renard-2010-corrections-complements`,
SHA256 `fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
was consulted at PDF1–2 and PDF18–19. Its correction for printed p.20
concerns adjunction orientation, and its correction for printed p.299
concerns the direction/order of precomposition and postcomposition in
naturality. Those corrections do not supply assumed action laws here.
No dedicated project Renard errata note was found in the inspected Library.

Renard works with complex algebras and, for the subsequent functors, the
appropriate nondegenerate modules and nondegenerate parts of Hom spaces.
The present definitions are internal prerequisites over arbitrary associative
nonunital rings and abelian groups with their specified original additive
actions. The module asserts no complex linearity or nondegeneracy of Hom.
It reuses `NonUnitalModuleHom`, its published pointwise group and `comp`,
`ActionsCommute` and its scalar endomorphisms, and `NonUnitalBimoduleCat`.
No alternate Hom carrier, group, unitization or assumed action laws are
introduced.

## Additive composition and residual actions

All declarations below are in
`Langlands.Algebra.NonUnitalBimoduleHomActions`. Let `S`, `R` and `T`
be nonunital rings in independent universes. Each carrier also has its own
universe and its specified `AddCommGroup` and original module structures.

`precomposeAddHom f` is the actual additive map `h ↦ h.comp f` for an
original `S`-linear map `f : Y' → Y`. `postcomposeAddHom g` is the actual
additive map `h ↦ g.comp h` for an original `S`-linear map `g : Z → Z'`.
`mapAddHom f g` is their composite, with value `g.comp (h.comp f)`.
The three `_apply` lemmas expose these whole original-Hom values.
Precomposition is additive pointwise; postcomposition uses `g.map_zero`
and `g.map_add`. These are additive maps in the Hom argument `h`; no
joint additivity in the pair `(f,g)` is asserted.

If `hY : ActionsCommute S R Y` and `Z` is only an original left
`S`-module, `sourceAction hY` is a named `NonUnitalModule R` on exactly
`NonUnitalModuleHom S Y Z`, with

```text
(r • h)(y) = h(op r • y).
```

It is defined by original composition with `hY.rightActionHom (op r)`,
so the result is still an original `S`-intertwiner. The theorem
`sourceAction_toEndHom` identifies the entire scalar endomorphism with
`precomposeAddHom (hY.rightActionHom (op r))`, and
`sourceAction_smul` gives evaluation. Multiplication is proved by
`right_mul_smul`: `op (r*s) • y = op s • (op r • y)`, which gives the
required order after precomposition. Scalar addition and zero use the
original source action laws and additivity of `h`; addition and zero in
`h` are pointwise. No target residual action is required.

Independently, for `hZ : ActionsCommute S T Z` and an original left
`S`-module `Y`, `targetAction hZ` is a named `NonUnitalModule Tᵐᵒᵖ`
on the same Hom carrier. Its value is

```text
(t • h)(y) = t • h(y),     t : Tᵐᵒᵖ.
```

The scalar endomorphism is exactly
`postcomposeAddHom (hZ.rightActionHom t)` (`targetAction_toEndHom`),
and `targetAction_smul` records evaluation. All module laws follow by
original-Hom extensionality from the supplied target action laws.
No source residual action is required. Both action definitions are
abbreviations, with no global instance installed on Hom.

When both sets of data are available, `actionsCommute hY hZ` proves
commutation: evaluating either order gives `t • h(op r • y)`.
`hom hY hZ` is a definition of an actual
`NonUnitalBimoduleCat.{uR,uT,max uY uZ} R T`. It stores exactly the
original Hom carrier, the published pointwise group and the two named
actions. The definitional identities `hom_carrier`,
`hom_isAddCommGroup`, `hom_isLeftModule` and `hom_isRightModule`
expose these choices. `hom_left_toEndHom` and `hom_right_toEndHom`
expose the same complete additive scalar endomorphisms as above.

## The opposite handed source convention

For an `R–S` bimodule `Y` and an original right `S`-module `Z`,
`rightSourceAction hY` constructs a named original right `R`-action on
exactly `NonUnitalModuleHom Sᵐᵒᵖ Y Z`:

```text
(op r • h)(y) = h(r • y).
```

The implementation directly precomposes `hY.leftActionHom r`, which is
an original right `S`-linear map. It uses the supplied left action on
`Y`, without replacing any group or action through a double opposite.
For opposite scalars `a,b`, their product unwraps to `b.unop*a.unop`;
the supplied `mul_smul` law gives the precomposition action law in that
order. The other laws use pointwise addition and the original action
laws. `rightSourceAction_toEndHom` identifies the complete scalar
endomorphism with `precomposeAddHom (hY.leftActionHom a.unop)`;
`rightSourceAction_smul` gives the displayed right-action formula.

## Comparison with the published regular source

`regularSourceAction` specializes `sourceAction` using precisely
`NonUnitalModule.regular A`, `NonUnitalModule.rightRegular A` and their
published commutation proof. For every nonunital ring `A` and original
left `A`-module `M`, its formula is

```text
(a • h)(b) = h(b*a).
```

`regularSourceAction_apply` records this formula;
`regularSourceAction_mul_apply` records
`((a*c) • h)(b) = h((b*a)*c)` over arbitrary, possibly noncommutative
`A`. Associativity is the only multiplication rewrite used.

`fromRegular` refines exactly
`RegularModuleHom.equivNonUnitalModuleHom` to an original `A`-linear
map from the published regular model, with its existing
`RegularModuleHom.instNonUnitalModule`, to the actual original Hom with
`regularSourceAction`. `toRegular` similarly refines its inverse.
Their `_toAddMonoidHom` theorems identify the entire additive maps with
the forward and inverse additive equivalence. `toRegular_comp_fromRegular`
and `fromRegular_comp_toRegular` are both whole original-Hom inverse
identities. `regularSourceAction_compat` identifies the full additive
endomorphism composites on both sides of this same equivalence.
Linearity and these identities hold definitionally. A section-local
instance permits elaborating the adapters; it is not exported as a global
Hom-action instance. The target action on `M` remains the supplied one,
even if `M` has the same underlying carrier as `A`.

## Degenerate cases and checks

`sourceAction_toEndHom_eq_zero` and `targetAction_toEndHom_eq_zero`
prove that a zero residual action induces zero scalar endomorphisms on
the entire Hom, by two levels of extensionality and the additive zero
law. `hom_subsingleton` and `hom_subsingleton_of_source` cover a
subsingleton target and source respectively; the latter uses that every
source element equals zero and both original maps preserve zero.

The companion `NonUnitalBimoduleHomActionsChecks` module checks all
principal action, commutation, bundled-Hom, complete scalar-endomorphism
and regular-adapter interfaces as unapplied declarations at independent
universes and at unequal 0/1 assignments in both directions. It checks
specified ring, group and original action choices in the presence of
competing instances, including competing actions on the exact Hom
carrier. It checks subsingleton source and target carriers.

For arbitrary `S` and unital residual rings `R,T`, the checks choose zero
original actions on two copies of `ℤ`. The identity additive map is a
nonzero element of the actual original Hom, witnessed by evaluation at
`1`. Nevertheless both residual scalar endomorphisms on the whole Hom
are zero. Thus a unital scalar ring imposes no unit law on these actions.
An integer regular-source example evaluates `fromRegular (a • φ)` at
`b` for the identity additive map `φ`, obtaining `b*a`.

## Remaining work

This unit does not assert I.2.2's tensor-Hom isomorphisms or complete
I.2.3. The actual one-sided and bimodule natural maps, their laws and the
fixed-variable additive Hom functors are separate work within the current
task. Taking a nondegenerate part, comparison with recovered coefficient
scalars or unitization, (I.2.2.1)–(I.2.2.7), adjunctions, exactness, tensor
associativity and the actual `F`, pseudo-`F`, `I` and `P` functors remain
separate definition or proposition/proof units. The tensor-action,
corner and annihilator-quotient tasks retain their existing scope.
