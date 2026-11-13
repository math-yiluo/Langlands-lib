# Irreducibility and supercuspidality of contragredients from their remaining inputs

Author: Worker 154. Module
`Langlands.Representation.CuspidalSupport.ContragredientIrreducibilityFromInputsStatement`,
namespace `Langlands.CuspidalSupport`, universe parameters `u, v`.

The module contains one `Prop`-valued definition,
`ContragredientIrreducibilityFromInputsStatement.{u, v}`. It is neither assumed nor proved
here.

## Source

David Renard, *Représentations des groupes réductifs p-adiques*, French edition dated
9 July 2026, registered as `renard-2026-representations-groupes-reductifs-padiques`,
SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`. VI.2.2,
Corollary (printed p.140 / PDF p.146), whose proof reads: "Ceci découle du théorème et du
corollaire III.1.7." The conclusion is the published
`ContragredientIrreducibilityStatement`; see
[`ContragredientIrreducibilityStatement`](ContragredientIrreducibilityStatement.md).

## The statement

`ContragredientIrreducibilityFromInputsStatement.{u, v}` is the implication

```text
Aubert.General.RationalPointsIrreducibleAdmissibleStatement.{u, v} →
Aubert.General.RepresentedParabolic.LeviJacquetContragredientStatement.{u, v} →
ContragredientIrreducibilityStatement.{u, v}
```

**Conclusion.** `ContragredientIrreducibilityStatement.{u, v}` covers every nonarchimedean
local field `k : Type u` with `T2Space k` and every connected reductive `G` over `k`, with
`G(F)` carrying `RationalPointFamily.pointTopology` and assumed locally compact and
nonarchimedean. For every smooth complex representation `A` of `G(F)` with carrier in
`Type v`, `A` is irreducible if and only if its smooth contragredient `A.contragredient`
is, and `A` is irreducible and supercuspidal (the represented predicate
`Aubert.General.RepresentedParabolic.IsSupercuspidal`: every normalized Jacquet module
along a proper actual rational parabolic vanishes) if and only if `A.contragredient` is.

The two premises, in this order:

1. `Aubert.General.RationalPointsIrreducibleAdmissibleStatement.{u, v}` (Jacquet's
   theorem, Renard VI.2.2, Theorem, printed p.140): for every nonarchimedean local field
   `F : Type u` and every connected reductive `G` over `F`, every irreducible smooth
   complex representation of `RationalPoint F G.X` (with the pinned topology
   `rationalPointTopology F G.X`) with carrier in `Type v` is admissible: smooth, with
   finite-dimensional fixed vectors for every open subgroup. See
   [`IrreducibleAdmissibleStatement`](../Aubert/General/IrreducibleAdmissibleStatement.md).
   It is used at carrier universe `v`, the carrier universe of the conclusion.
2. `Aubert.General.RepresentedParabolic.LeviJacquetContragredientStatement.{u, v}` (Renard
   VI.9.6, second Theorem (VI.9.6.2), printed p.201 / PDF p.207): for nonarchimedean local
   fields `k : Type u` with `T2Space k`, connected reductive `G` with `G(F)` locally
   compact and nonarchimedean, every actual rational parabolic `P = MN` and every actual
   rational parabolic `P̄ = M N̄` with the same Levi (`mbar ≫ pbar = m ≫ p`) and
   `pointImage p ⊓ pointImage pbar = pointImage (m ≫ p)`, the functors
   `π ↦ r_{P̄}^G(π̃)` and `π ↦ (r_P^G π)~` on smooth representations of `G(F)` with
   carriers in `Type v` are naturally isomorphic (`leviJacquetFunctor` and
   `SmoothRep.contragredientFunctor`). See
   [`LeviJacquetContragredientStatement`](../Exponents/LeviJacquetContragredientStatement.md).
   It is used at the same universes `u, v`.

## Why these premises

They are the published results the proof uses that the Library does not yet prove.

- **Irreducibility.** Renard derives it from the Theorem (irreducible implies admissible)
  and Corollary III.1.7 (for admissible representations, irreducibility passes to and
  from the contragredient). Premise 1 supplies admissibility; the irreducibility
  equivalence for admissible representations is the proved Library theorem
  `SmoothRep.isIrreducible_contragredient_iff`. For the topology, `rationalPoints G` and
  `RationalPoint k G.X` are definitionally the same type (the sections of `G` over
  `Spec k`), and `RationalPointFamily.pointTopology` is defined as
  `rationalPointTopology k G.X`, so premise 1 applies to the representations of the
  conclusion as they stand.
- **Supercuspidality.** Renard's printed proof cites only the Theorem and III.1.7; the
  surrounding text (VI.2.1) characterizes supercuspidality by coefficients compactly
  supported modulo the centre. The Library's published VI.2.1 statements use the
  standard-parabolic cuspidality predicate and further structural data, not the
  represented predicate `IsSupercuspidal` of the conclusion. The proof recorded with this
  statement instead uses Casselman's description of the Jacquet module of a
  contragredient (premise 2): for a proper parabolic `P`, `r_P(π̃) ≅ (r_{P̄} π)~` for the
  opposite parabolic `P̄`, which is proper as well, so `r_P(π̃)` vanishes when
  `r_{P̄}(π)` does. The opposite parabolic itself is supplied unconditionally by the
  Library (`oppositeLeviParabolic`); it is not a premise.

## Faithfulness notes

- **No change to the target.** The conclusion is the published target at the same
  universes `u, v`. Both premises are published closed propositions used at their own
  binders; neither mentions a particular field, group, parabolic or representation, so
  this is a plain implication between closed statements.
- **Strength.** Neither premise is the target or contains it. Premise 1 is Renard's
  Theorem of VI.2.2, which the Corollary's proof cites. Premise 2 is Renard's VI.9.6,
  second Theorem, proved there independently of the VI.2.2 Corollary.
- **Universes.** The field universe `u` and the carrier universe `v` are shared by all
  three statements. Premise 1's own universe parameters are named `u, uV`; here `uV := v`.

## Provenance

Derived. The statement records which published inputs the proof of Renard VI.2.2,
Corollary, needs in the represented-parabolic interface. Revision 2 of task
`33346af6-9886-4285-8d36-128d671ab6b8` (Task 5629) lists this statement and its proof
under "Intermediate conditional result". The premises are owned by the proof tasks
`173e44ba-079b-4597-a13b-1aab371a4ec9` (Jacquet's theorem) and
`c0fa1878-6cee-4435-8484-2fc15ea04a17` (VI.9.6). Combining a proof of this statement with
proofs of the two premises gives the target.

## Imports

| Module | Used for |
| --- | --- |
| `Langlands.Representation.CuspidalSupport.ContragredientIrreducibilityStatement` | the conclusion |
| `Langlands.Representation.Aubert.General.IrreducibleAdmissibleStatement` | premise 1 |
| `Langlands.Representation.Exponents.LeviJacquetContragredientStatement` | premise 2 |
