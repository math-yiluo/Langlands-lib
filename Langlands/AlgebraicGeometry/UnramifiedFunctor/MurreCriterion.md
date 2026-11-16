# Murre's criterion for unramified functors

Module `Langlands.AlgebraicGeometry.UnramifiedFunctor.MurreCriterion` proves

```lean
theorem murreCriterion : MurreCriterionStatement.{u, v}
```

for arbitrary universes `u` and `v`. It adds no hypothesis. The statement
`Langlands.AlgebraicGeometry.UnramifiedFunctor.MurreCriterionStatement` is in
module `Langlands.AlgebraicGeometry.UnramifiedFunctor.MurreCriterionStatement`.
Let `S : Scheme.{u}` be locally noetherian and let `F : (Over S)ᵒᵖ ⥤ Type v`
have `u`-small values and satisfy (F1a), (F1b), (F2), (F3), (F4′), strong
(F5), (F6), (F7) and (F8). Then there are `Y : Scheme.{u}` and `q : Y ⟶ S` such
that `F` is represented by `Over.mk q` and `q` is separated, locally of finite
type and formally unramified. This is the sufficiency direction of Murre's
Theorem 1 in the form of its Corollary 1 (J. P. Murre, Séminaire Bourbaki
exp. 294, printed p.246, PDF p.5; printed page `p` is PDF page `p − 241`).

## Proof

The proof is one term:

```lean
murreCriterion_of_steps ⟨murreBaseChange, murreLocalToGlobal, murreLocalStep⟩
```

It uses four published Library results.

- `murreCriterion_of_steps : MurreProofStepsStatement.{u, v} →
  MurreCriterionStatement.{u, v}` (module `MurreReduction`). Here
  `MurreProofStepsStatement.{u, v}` (module `MurreProofSteps`) is the
  conjunction of the three statements below, and the anonymous constructor
  builds it. The reduction first shows `MurreDimensionBound.{u, v} n` for every
  `n : ℕ`, by strong induction on `n`. This is Murre's criterion over every
  locally noetherian base all of whose local rings have Krull dimension `< n`.
  At each point `s`, the local ring of `S` at `s` is local noetherian, so its
  Krull dimension is a natural number `m`. The local step at `m` then applies
  to the base change of `F` to the spectrum of that local ring, and
  Proposition 2 assembles the results. This argument needs no separate base
  case. For a general `S` the reduction uses Proposition 2 directly. At a point
  of dimension `m` it uses the local step with the bound for `m`. So it does
  not need a global bound on the dimensions of the local rings of `S`.
- `murreBaseChange : MurreBaseChangeStatement.{u, v}` (module
  `MurreBaseChange`). If `F` satisfies Murre's conditions `MurreConditions F`,
  then so does its base change `(Over.map g).op ⋙ F` along any morphism
  `g : S' ⟶ S`. Murre states this in the first sentence of his Section 2
  (printed p.247).
- `murreLocalToGlobal : MurreLocalToGlobalStatement.{u, v}` (module
  `MurreLocalToGlobal`), Murre's Proposition 2 (Section 2, printed
  pp.249–250).
  Let `S` be locally noetherian and let `F` satisfy the conditions. Suppose
  that for every point `s`, the base change of `F` to the spectrum of the
  local ring at `s` is represented by a separated, locally of finite type,
  formally unramified scheme. Then so is `F` over `S`.
- `murreLocalStep : MurreLocalStepStatement.{u, v}` (module
  `MurreLocalStep`), Steps 1, 2a and 2b of Case I of Murre's induction
  (Section 2, printed pp.247–249). It assumes `MurreDimensionBound.{u, v} n`.
  Then the criterion holds over the spectrum of a local noetherian ring of
  Krull dimension `n`.

The import closure uses none of the declarations excluded by the task
(`NoetherianTwoAxisClassRepresentabilityStatement`,
`NormalFiniteTypeTwoAxisExtensionProperty`,
`NormalFiniteTypeAbelianAmpleExistenceStatement`,
`NormalFiniteTypeAbelianPicardSheafAFSchemeStatement`,
`FiniteTypeAbelianPicardSheafSchemeStatement`,
`FiniteTypeSmoothFamilyAbelianRepresentabilityStatement`,
`SmoothFamilyAbelianRepresentabilityStatement`) and no proof of them. The
theorem depends only on the axioms `propext`, `Classical.choice` and
`Quot.sound`.
