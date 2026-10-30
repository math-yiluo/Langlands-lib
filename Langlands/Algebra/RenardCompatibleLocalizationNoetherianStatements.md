# Noetherian unitized actions on actual endomorphism localization

Author: Worker 709. This is a statement-only internal derived unit under
whole-book Renard task `f5d1f399-a1f8-4ab5-a981-90b92abd4857`, revision 2.
Its module is
`Langlands.Algebra.RenardCompatibleLocalizationNoetherianStatements`, in
namespace `Langlands.Renard.AlgebraActionLocalization`.

## Original source and scope

David Renard, *Représentations des groupes réductifs p-adiques*, French
version dated 9 July 2026, is the governing source. Registered source:
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Original file:
`/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`.
Printed body page equals PDF page minus 6.

The final C.II proposition (printed 279 / PDF 285) assumes a commutative
Noetherian complex algebra B, a finite-type B-module L, an endomorphism a,
and a finite-type localization L_a. It concludes eventual stability and
identifies the localization with the image for every positive stable power.
Worker 709 reread this page, including its rendered image, for this unit.
C.II's definition (printed 276 / PDF 282) requires both kernel and image
equalities for stability, and a positive power for eventual stability.
The actual localization is A.III.1, example 5 and the following lemma and
corollary (printed 252–253 / PDF 258–259).

The conventions (printed 6 / PDF 12) allow nonunital rings and actions,
even actions of unital rings whose unit does not act as the identity.
I.2.1 (printed 14 / PDF 20) describes adjoining a unit and gives the Hom
comparison for complex-linear intertwiners. Worker 709 reread both passages.
The local unitized module here is the already published implementation of
that construction, not an assumed action on a replacement localization.

These targets are **internal derived content**, not a formal restatement
of the complete source proposition. They impose explicit ordinary
Noetherianity or finite generation over U = Unitization ℂ B. They neither
define nor identify the source's finite-type or Noetherian conventions.
They remove commutativity of B under these explicit hypotheses. They assert
surjectivity and a common positive kernel/stability exponent, leaving the
canonical stable-image identification to its separate existing statement
and proof branch. The source convention question and the whole final C.II
proposition remain parent obligations.

The older registered supplementary source
`renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`, has
relevant Appendix C errata on PDF 18–19. Worker 709 reread both pages;
they contain no correction to the final C.II proposition or replacement of
the nonunital conventions. They do not replace the 2026 source. The dedicated
project and current-Library source errata file
`notes/errata/renard-2026-representations-groupes-reductifs-padiques.md`
is absent (checked 29 October 2026).

## Actual data and local action selection

All closed propositions bind independent universes `uB` and `uV`:

```text
B : Type uB
[NonUnitalRing B] [Module ℂ B]
[IsScalarTower ℂ B B] [SMulCommClass ℂ B B]
V : Type uV
[AddCommGroup V] [Module ℂ V]
ρ : B →ₙₐ[ℂ] Module.End ℂ V
f : LinearIntertwiner ρ ρ
```

The two compatibility classes on B express complex bilinearity of its
multiplication. There is no unit law, commutativity, nondegeneracy,
nontriviality, countability or finite-dimensionality assumption. Zero and
degenerate actions and zero spaces are included whenever the displayed
Noetherian or finite hypotheses hold.

Put a = f.toLinearMap and ha b z = f.map_action' b z. Use the actual public
`Localized a`, `iota a` and
σ = `localizedAction a ρ ha`. The localized carrier has universe uV since
ℂ is in Type 0. The actual action σ is constructed on that same carrier.
The chosen unitized module on V is exactly `CompatibleUnitization.module ρ`;
on `Localized a` it is exactly `CompatibleUnitization.module σ`.
Each needed module is selected with `letI`, never a new global instance.
An ordinary `Module.Finite` hypothesis below refers to that selected module,
not to finite dimension over ℂ or additive generation under B.

## Parameterized conclusion

`CompatibleLocalizationStabilizationAt ρ f` is a Prop with no Noetherian or
finite-generation premise. Under the local unitized source action set

```text
powers n = CompatibleUnitization.toLinearIntertwiner
             ((CompatibleUnitization.ofLinearIntertwiner f) ^ n).
```

It asserts exactly

```text
Function.Surjective (iota a) ∧
  ∃ n : ℕ, 0 < n ∧
    (iotaIntertwiner a ρ ha).ker = (powers n).ker ∧ Stable (a ^ n).
```

Both kernels in the displayed equality are actual elements of
`CompatibleSubmodule ρ`. The first is the compatible kernel of the actual
canonical map into σ; the second is the compatible kernel of the actual
unitized power transported through the public Hom correspondence. The
underlying complex-linear power is a ^ n. The `Stable` conjunct is the
existing predicate from `StableEndomorphismStatements`: both
ker(a ^ n) = ker((a ^ n) ^ 2) and
range(a ^ n) = range((a ^ n) ^ 2), as ordinary complex subspaces. The **same
strictly positive n** occurs in the kernel equality and both stability
equalities. No desired surjectivity, stability or decomposition is assumed.

## Three closed targets

`UnitizedNoetherianSurjectivityStatement` assumes only
`IsNoetherian U (Localized a)` for the actual unitized σ-action and concludes
`Function.Surjective (iota a)`. No Noetherian source or ring is needed.

`UnitizedNoetherianStabilizationStatement` assumes exactly
`IsNoetherian U V` and `IsNoetherian U (Localized a)` for the two actual
chosen actions and concludes `CompatibleLocalizationStabilizationAt ρ f`.
It assumes no ring Noetherianity or finite generation.

`UnitizedFiniteStabilizationStatement` assumes exactly
`IsNoetherianRing U`, `Module.Finite U V` and
`Module.Finite U (Localized a)` for those actions and concludes the same
parameterized Prop. It does not additionally assume module Noetherianity.
Mathlib's ring Noetherianity concerns the ordinary regular left U-module;
it does not require commutativity of U or B.

`CompatibleLocalizationNoetherianStatements.{uB,uV}` is precisely the
conjunction of these three closed targets, in that order. Every statement
is a transparent Prop-valued definition. This file proves none of them.

## Derivation rationale and dependencies

A future proof can convert `f`, `iotaIntertwiner`,
`localizedEndIntertwiner` and `localizedInvIntertwiner` into actual U-linear
maps with `CompatibleUnitization.ofLinearIntertwiner`. The inverse identities
of the actual localized operators give a U-linear automorphism. The public
actual localization fraction and kernel lemmas supply inverse-power
exhaustion and local nilpotence of the canonical-map kernel. These are
construction theorems, not extra premises of this unit.

Apply the published ordinary, possibly noncommutative-ring
`NoetherianLocalizationCore.exhaustion_surjective` and `localization_core`
to those actual carriers and maps. Equality of the U-linear kernels and
ranges yields equality of their underlying sets; the same functions and
power coherence then give the displayed compatible-kernel equality and the
ordinary complex stability predicate. Finite modules over a Noetherian ring
supply the two Noetherian module instances for the third target. This is a
derivation route, not a claim that this statement file implements a proof.

The statement module imports only the public actual action construction,
`CompatibleSubmodule`, `CompatibleUnitization`, the existing stability
predicate module and Mathlib's Noetherian module definitions. It does not
import a proof draft or the separate compatible stable-image statement.
It supplies no replacement localization, no new action/power constructor,
no global module instance and no new axiom. Compilation and statement
inspection are development evidence only; independent semantic review and
Library publication are required before a proof successor.


## Development verification

The canonical module and closed aggregate were recompiled on 29 October
2026 in environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`, with zero errors
or warnings. The service confirmed a Prop-valued definition, independent
level parameters `uB` and `uV`, and only the standard assumptions
`propext`, `Classical.choice` and `Quot.sound`.

A separate private diagnostic printed all five complete declaration
bodies and unapplied types, checked both orders of distinct universe
instantiations, and compiled reflexive equivalences exposing the exact
module arguments of every closed target. These confirm that source
hypotheses use `CompatibleUnitization.module ρ` and target hypotheses use
`CompatibleUnitization.module (localizedAction a ρ ha)`, rather than an
ambient module instance. The printed parameterized body uses the same
positive exponent in its compatible-kernel equality and ordinary
stability conjunct. These checks inspect elaborated meaning and do not
prove any of the three closed target propositions. The diagnostic is
excluded from the public pair.
