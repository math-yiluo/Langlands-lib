# Murre's criterion from the steps of its proof

Module `Langlands.AlgebraicGeometry.UnramifiedFunctor.MurreReduction` proves
that the three statements of
`Langlands.AlgebraicGeometry.UnramifiedFunctor.MurreProofSteps` imply
`Langlands.AlgebraicGeometry.UnramifiedFunctor.MurreCriterionStatement`. It is
a conditional reduction: the steps themselves are not proved here.

## Results

- `exists_nat_eq_ringKrullDim R`: for a local noetherian ring `R`,
  `ringKrullDim R = m` for some `m : ℕ`.
- `murreDimensionBound_of_steps h0 h1 h2 n`: from
  `h0 : MurreBaseChangeStatement.{u, v}`,
  `h1 : MurreLocalToGlobalStatement.{u, v}` and
  `h2 : MurreLocalStepStatement.{u, v}`, the statement
  `MurreDimensionBound.{u, v} n` holds for every `n : ℕ`.
- `murreCriterion_of_steps : MurreProofStepsStatement.{u, v} →
  MurreCriterionStatement.{u, v}`.

## Proofs

`exists_nat_eq_ringKrullDim`. Mathlib's instance in
`Mathlib.RingTheory.Ideal.KrullsHeightTheorem` gives `FiniteRingKrullDim R`
for a local noetherian ring, so `ringKrullDim R` (in `WithBot ℕ∞`) is neither
`⊥` (`ringKrullDim_ne_bot`) nor `⊤` (`ringKrullDim_ne_top`). Hence it is the
image of some `k : ℕ∞` with `k ≠ ⊤`, that is, of a natural number.

`murreDimensionBound_of_steps`, by strong induction on `n`. Assume
`MurreDimensionBound m` for all `m < n`. Let `S` be locally noetherian with all
local rings of dimension `< n`, and let `F` satisfy `MurreConditions F`. By the
local-to-global statement `h1` it suffices to show, for each point `s`, that
`baseChange (S.fromSpecStalk s) F` is `UnramifiedRepresentable`. The stalk
`S.presheaf.stalk s` is a local noetherian ring (Mathlib instances for schemes
and for locally noetherian schemes), so its dimension is some `m : ℕ`, and
`m < n` by hypothesis. The base change satisfies `MurreConditions` by `h0`.
The local step `h2` at `m`, with the induction hypothesis
`MurreDimensionBound m`, applied to `R = S.presheaf.stalk s`, gives the claim.
There is no separate base case: for `n = 0` the local rings would have
dimension `< 0`, so no point exists and the requirement of `h1` is vacuous.

`murreCriterion_of_steps`. Let `S` be locally noetherian and let `F` satisfy
the ten hypotheses of `MurreCriterionStatement`, which together are
`MurreConditions F`. The conclusion of `MurreCriterionStatement` is
`UnramifiedRepresentable F`. Apply `h1`: for each point `s`, the stalk has
dimension some `m : ℕ`, and `h2` at `m`, with
`murreDimensionBound_of_steps h0 h1 h2 m` and `h0` for the base change along
`S.fromSpecStalk s`, gives the representability of the base change. No bound on
the dimensions of all local rings of `S` is needed, which covers Murre's
Case II (`dim S = ∞`) as he does, through Proposition 2.
