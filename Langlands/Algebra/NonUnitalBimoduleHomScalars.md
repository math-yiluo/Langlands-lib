# Coefficient-linear residual actions on original Hom spaces

This is internal sufficient-input infrastructure for Renard's original
nonunital module conventions. It constructs both ambient residual actions on
the exact published additive Hom groups. It does not install coefficient
instances globally, replace an original action, or assume that an ambient Hom
space is nondegenerate.

## Named coefficients and additional input

The coefficient ring `k`, nonunital rings `R`, `S`, and carriers `X`/`Y`, `Z`
have independent universes. The recovering ring has its specified coefficient
module and both multiplication compatibility laws. The residual ring has its
specified coefficient module; its self-multiplication laws are not needed in
this ambient construction. There are no coefficient-module inputs on the
original carriers and no unit, nontriviality, finite-dimensionality, or
commutative-algebra hypotheses. Opposite rings retain Mathlib's coefficients
induced from the specified original-ring module.

For the left orientation, `SourceCompatible k hR hRX` is precisely
`IsScalarTower k Sᵐᵒᵖ X` with the local coefficient module on `X` set to
`NondegenerateScalars.module k hR hRX`. Source nondegeneracy is only for `R`.
The target coefficients are recovered using `hRZ`; the Hom module is exactly
`NondegenerateModuleHomScalars.homModule k hR hRZ`. No output compatibility
certificate is an input.

For the right orientation, `RightSourceCompatible k hS hSY` is precisely
`IsScalarTower k R Y` with the local module on `Y` set to
`NondegenerateScalars.module k hS.op hSY`. Source nondegeneracy is only for
`Sᵐᵒᵖ`. Target and Hom coefficients are the corresponding named constructions
using `hS.op` and `hSZ`. All declaration types explicitly select these modules.

## Actual maps and their proofs

`sourceLinearEnd` uses the original
`precomposeAddHom (hX.rightActionHom (op s))`. Its full additive map, full
function, and evaluation formula are identified by
`sourceLinearEnd_toAddMonoidHom`, `sourceLinearEnd_function`, and
`sourceLinearEnd_apply`. Pointwise Hom coefficients make this linear by
reflexivity after evaluating at a source vector.

`sourceIsScalarTower` evaluates the original residual action at a vector,
uses the supplied source tower to move the coefficient through the source
action, and applies `NondegenerateScalars.map_smul` to the original
`R`-intertwiner. `sourceSmulCommClass` is pointwise reflexivity. The actual
`sourceActionHom : S →ₙₐ[k] Module.End k (NonUnitalModuleHom R X Z)` packages
these derived laws through `NonUnitalModule.toLinearEndHom`. Its entire
per-s additive map and function are the preceding precomposition map. The
formula is `rho s f x = f (op s • x)`. The theorem
`sourceActionHom_ofLinearEndHom` proves equality of whole original action
structures with `NonUnitalBimoduleHomActions.sourceAction hX`, by action
structure extensionality.

`rightSourceLinearEnd`, `rightSourceIsScalarTower`,
`rightSourceSmulCommClass`, and `rightSourceActionHom` implement the direct
mirror on the published `rightSourceAction hY`, without transporting through
a double opposite. For `r : R`, the whole additive map and function at `op r`
are `precomposeAddHom (hY.leftActionHom r)`, and evaluation is
`rho' (op r) f y = f (r • y)`. The corresponding
`rightSourceActionHom_ofLinearEndHom` identifies the complete original
right residual action. These identities retain the exact supplied Hom
carriers and additive groups.

## Provenance and boundary

The governing original is David Renard, *Représentations des groupes
réductifs p-adiques*, French edition dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Relevant passages are I.1.1, printed pp.5–6 / PDF11–12 (original modules and
commuting actions), I.2.1, printed p.14 / PDF20 (recovered coefficients),
I.2.2–I.2.3, printed pp.15–18 / PDF21–24 (tensor/Hom conventions), and I.4.2,
printed pp.23–24 / PDF29–30 (duality motivation). These passages and the
older supplement `renard-2010-corrections-complements`, PDF1–2, were read.
The 2026 edition governs.

This adapter is derived from the published original Hom actions, pointwise
Hom coefficients, automatic scalar linearity, and compatible-action
conversion. The explicit sufficient source compatibility is part of its
scope; arbitrary commuting additive actions do not here identify separately
recovered coefficient modules. Exact-part coefficients and comparisons are
provided separately in `NonUnitalBimoduleHomScalarsParts`. The parent's
full-source I.4.2 coefficient-convention obligation remains open, as do F/P
comparisons, duality equivalences, Hom-chain and categorical natural
isomorphisms, and dual-completion results.
