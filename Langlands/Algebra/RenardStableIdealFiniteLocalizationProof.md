# Actual localization under explicit stable-ideal finiteness: proof

Author: Worker 1120, for proof task `30fb5fd5-84c5-4602-afae-5210a9f947ac`
revision 1. That task is the proof successor of statement task
`9796ccea-0a72-431d-b9a9-87c0499717c9`, under the whole-book Renard task
`f5d1f399-a1f8-4ab5-a981-90b92abd4857` revision 2. The module is
`Langlands.Algebra.RenardStableIdealFiniteLocalizationProof`, in namespace
`Langlands.Renard.AlgebraActionLocalization`.

The theorem `stableIdealFiniteLocalization` has the complete closed type
`StableIdealFiniteLocalizationStatement.{uB, uV}`, the published statement
in `Langlands.Algebra.RenardStableIdealFiniteLocalizationStatements`. The
algebra universe `uB` and the carrier universe `uV` stay independent. The
theorem has no section variables and adds no premise. It does not assume
commutativity, a unit or unit-action law, nondegeneracy, nontriviality or
finite complex dimension. It uses no replacement action or localization.

The module imports, by name and unchanged, the statement module and four
published proof modules:

- `Langlands.Algebra.RenardCompatibleLocalizationNoetherianProof`,
- `Langlands.Algebra.RenardCompatibleStableImageProof`,
- `Langlands.Algebra.UnitizationIdealNoetherianProof`,
- `Langlands.Algebra.UnitizationStableGenerationProof`.

It changes none of them, nor anything the statement imports.

## Provenance and scope

This is internal derived content. The target is motivated by David
Renard, *Représentations des groupes réductifs p-adiques*, French version
dated 9 July 2026, C.II, final proposition, printed p. 279 / PDF p. 285.
The registered source is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`. The
statement replaces the source's finite-type and Noetherian phrases by
explicit complex-linear stable generation, and it allows noncommutative
`B`. The statement's Markdown records the source reading. This proof
relies on that record and makes no new source claim.

The statement's Markdown also records that the source argues by writing
the inverse of the localized operator as a polynomial over the
commutative algebra. The Lean proof takes a different route. It turns
the three explicit hypotheses into Noetherianity of the actual
unitization and finiteness of two actual unitized modules. It then
applies the published quotient-Hopfian Noetherian localization result
and the finiteness-free stable-image result. No step uses commutativity
of `B`.

The proof establishes exactly this internal target. It does not compare
the three explicit generation hypotheses with Renard's nonunital
finite-type or Noetherian conventions. It does not prove the full
source-facing C.II proposition. Both remain obligations of the parent
task.

## Implemented proof

After introducing `B`, `V`, their instances, the action `ρ`, the
self-intertwiner `f` and the three hypotheses `hB`, `hV` and `hL`, the
proof names the actual localized action

`σ = localizedAction f.toLinearMap ρ (fun b v => f.map_action' b v)`.

This is the statement's own `σ`, with the statement's compatibility proof.

**Local unitized modules.** The proof installs three unitized module
structures, each by `let` inside the proof. No global instance is added.

- On `B`: `CompatibleUnitization.module (NonUnitalAlgHom.lmul ℂ B)`, the
  unitization of the actual regular left action.
- On `V`: `CompatibleUnitization.module ρ`.
- On `Localized f.toLinearMap`: `CompatibleUnitization.module σ`.

For each it also installs the published scalar-tower adapter
`CompatibleUnitization.isScalarTower`. Each unit-action equation is the
published `CompatibleUnitization.smul_eq`, which gives
`x • m = x.fst • m + ρ' x.snd m` for the action `ρ'` in question. The
complex scalar modules are the existing ones the statement uses.

**Noetherian unitization.** The published
`UnitizationIdealNoetherian.scalarIdealCriterion` is applied with
`R = ℂ` and `A = B`. Its premise `IsNoetherianRing ℂ` is found by instance
search. Its unit-action premise is `smul_eq` for the regular action. Here
`NonUnitalAlgHom.lmul ℂ B x.snd b` is definitionally `x.snd * b`, so the
equation has the criterion's form `u.fst • a + u.snd * a`. The right side
of the criterion is exactly hypothesis `hB`, up to bound-variable names.
The reverse direction of the equivalence gives
`IsNoetherianRing (Unitization ℂ B)`.

**Finite unitized modules.** The published
`UnitizationStableGeneration.moduleGeneration` is applied twice, with
`R = ℂ` and `A = B`. With `M = V`, action `ρ` and `smul_eq ρ`, its right
side is exactly hypothesis `hV`. This gives
`Module.Finite (Unitization ℂ B) V`. With `M = Localized f.toLinearMap`,
action `σ` and `smul_eq σ`, its right side is hypothesis `hL` after its
two `let` bindings unfold. This gives
`Module.Finite (Unitization ℂ B) (Localized f.toLinearMap)`. In each case
the reverse direction of the equivalence is used.

**First conclusion.** The published `stabilizationAt_of_finite ρ f`
selects the same two unitized modules, `CompatibleUnitization.module ρ`
and `CompatibleUnitization.module` of the same localized action. Given
the three facts above, it returns
`CompatibleLocalizationStabilizationAt ρ f`.

**Second conclusion.** For every `n` with `0 < n` and
`Stable (f.toLinearMap ^ n)`, the published
`CompatibleStableImageProof.compatibleStablePowerImageAt_of_stable ρ f n`
returns `CompatibleStablePowerImageAt ρ f n`. This step needs no
finiteness hypothesis.

The two results form the required conjunction.

## Verification

The module compiled on 30 October 2026 in environment
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f` with no errors or warnings.
Inspection of `stableIdealFiniteLocalization` reported a theorem with
level parameters `uB` and `uV`. It depends only on the standard axioms
`propext`, `Classical.choice` and `Quot.sound`. It uses no `sorry`,
`admit` or new axioms. Development compilation is not acceptance.
Independent semantic review, the Lake build, exact-target validation and
Library publication are still required.
