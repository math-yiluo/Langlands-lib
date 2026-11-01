# Complex residual Hom coefficient actions

This module specializes the actual constructions in
`NonUnitalBimoduleHomScalars` and `NonUnitalBimoduleHomScalarsParts` at
`k = ℂ`. The four action homomorphisms, two inherited part Modules, and two
linear inclusions are abbreviations of the generic objects, with explicit
result types. Both nonunital rings and both original module carriers retain
independent universes.

## Named coefficients and sufficient inputs

For the left orientation, `H = NonUnitalModuleHom R X Z` has exactly
`NondegenerateModuleHomScalars.homModule ℂ hR hRZ`. Its residual action is
exactly `NonUnitalBimoduleHomActions.sourceAction hX`, and its part is exactly
`P = nondegeneratePart hS H` for that action. The original additive groups
and inherited subtype action are retained.

The action homomorphisms require `hRX : IsNondegenerate R X` and
`hc : SourceCompatible ℂ hR hRX`. This predicate installs exactly
`NondegenerateScalars.module ℂ hR hRX` on the original source and asks for
`IsScalarTower ℂ Sᵐᵒᵖ X` with its original right action. It contains no
assumed output compatibility. The target coefficients are recovered from
`hRZ : IsNondegenerate R Z`. No coefficient Module on either original
carrier, nondegeneracy of the ambient Hom, or right-`S` nondegeneracy of `X`
is an input.

For the right orientation, `H' = NonUnitalModuleHom Sᵐᵒᵖ Y Z` has exactly
`NondegenerateModuleHomScalars.homModule ℂ hS.op hSZ`. Its residual action is
exactly `NonUnitalBimoduleHomActions.rightSourceAction hY`, and its part is
exactly `P' = nondegeneratePart hR.op H'`.
`RightSourceCompatible ℂ hS hSY` asks for `IsScalarTower ℂ R Y` after
installing exactly `NondegenerateScalars.module ℂ hS.op hSY`. There is no
left-`R` nondegeneracy assumption on `Y`.

The recovering ring carries its specified complex Module and both
multiplication compatibility laws. The residual ring's specified Module is
needed for its algebra action, and its multiplication compatibility laws
are additionally needed for the recovered-part Module comparison. Opposite
rings use the coefficient structure induced from the specified original-ring
Module. Inherited part coefficients and inclusions need only target recovery
and pointwise commutation with the residual action. There is no unit-action,
commutativity, nontriviality, or dimension assumption.

## Actual maps and implemented proofs

`complexSourceActionHom` is an actual
`S →ₙₐ[ℂ] Module.End ℂ H`. Its entire per-`s` additive map is
`precomposeAddHom (hX.rightActionHom (op s))`; its function is that same
precomposition, and evaluation gives `f (op s • x)`. The corresponding
`_toAddMonoidHom`, `_function`, and `_apply` theorems are reflexive identities.
`complexSourceActionHom_ofLinearEndHom` reuses the generic equality of whole
action structures with the original `sourceAction`.

`complexRightSourceActionHom` is an actual
`Rᵐᵒᵖ →ₙₐ[ℂ] Module.End ℂ H'`. At `op r`, its whole additive map and
function are `precomposeAddHom (hY.leftActionHom r)`, evaluating to
`f (r • y)`. Its forgotten action is the whole original `rightSourceAction`,
by the generic theorem.

`complexSourcePartModule` and `complexRightSourcePartModule` are the named
inherited pointwise complex Modules on the exact original parts. Their
`_smul_apply` theorems give `(c • f).val x = c • f.val x` and its right
counterpart, with the recovered target coefficients explicitly selected.
The generic construction preserves the same fixing idempotent under
coefficient scaling and proves all subtype Module laws by extensionality;
these abbreviations retain that construction.

`complexSourcePartInclusion` and `complexRightSourcePartInclusion` are
actual complex-linear maps into the original Hom spaces. Their full
underlying additive maps are the original subtype inclusions, their whole
functions are `Subtype.val`, and evaluation is `f.val`. These identities are
reflexive.

`complexSourcePartActionHom` and `complexRightSourcePartActionHom` are
actual algebra homomorphisms into the linear endomorphisms of `P` and `P'`.
Their full additive maps and functions are the inherited original subtype
actions. Composing with the original subtype inclusion gives exactly the
original ambient precomposition additive map composed with that inclusion,
as stated by the `_subtype_toAddMonoidHom` theorems. Evaluation gives
`f.val (op s • x)` and `f.val (r • y)`. The `_ofLinearEndHom` theorems reuse
the generic equalities of complete original action structures.

Finally, `complexSourcePartRecoveredModule_eq` compares the actual Module
recovered using exactly
`nondegeneratePart_isNondegenerate (M := H) hS` with
`complexSourcePartModule`. `complexRightSourcePartRecoveredModule_eq` uses
exactly `nondegeneratePart_isNondegenerate (M := H') hR.op` and compares
with `complexRightSourcePartModule`. Both proofs specialize the generic
uniqueness argument: the inherited tower is derived from the stipulated
source compatibility, then `NondegenerateScalars.module_eq_of_compatible`
identifies the actual Module structures. The corresponding
`_recovered_smul_eq` theorems expose equality of the two coefficient actions
on every original part element. The source nondegeneracy and compatibility
arguments remain explicit theorem inputs even though their conclusions
only mention target recovery and the two part Modules.

## Provenance and scope

These are derived internal specializations of the generic sufficient-input
adapter. They combine the published original Hom actions, pointwise
recovered coefficients, compatible-action conversion, and recovery
uniqueness; they do not posit a new coefficient structure on a replacement
carrier.

The governing original is David Renard, *Représentations des groupes
réductifs p-adiques*, French edition dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The relevant passages are I.1.1, printed pp.5–6 / PDF11–12 (original module
and commuting-action conventions); I.2.1, printed p.14 / PDF20 (recovered
coefficients); I.2.2–I.2.3, printed pp.15–18 / PDF21–24 (Hom actions and
nondegenerate parts); and I.4.2, printed pp.23–24 / PDF29–30 (later duality
motivation).

The stipulated compatibility with the named recovered source Module is
part of the scope. Arbitrary commuting additive actions alone are not
used to identify separately recovered coefficient Modules. The full-source
I.4.2 coefficient convention, F/P comparisons, duality equivalences,
Hom-chain and categorical natural isomorphisms, and dual-completion
results remain parent obligations.
