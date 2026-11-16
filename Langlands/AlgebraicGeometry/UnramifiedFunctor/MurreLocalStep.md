# The local step of Murre's induction

Module `Langlands.AlgebraicGeometry.UnramifiedFunctor.MurreLocalStep` proves

```lean
theorem murreLocalStep : MurreLocalStepStatement.{u, v}
```

for arbitrary universes `u` and `v`. The statement
`Langlands.AlgebraicGeometry.UnramifiedFunctor.MurreLocalStepStatement` is in
module `Langlands.AlgebraicGeometry.UnramifiedFunctor.MurreProofSteps`. It says:
let `n : ℕ` and assume `MurreDimensionBound.{u, v} n`, that is, Murre's
criterion over every locally noetherian scheme all of whose local rings have
Krull dimension `< n`. Let `R : CommRingCat.{u}` be a local noetherian ring with
`ringKrullDim R = n`, and let `F : (Over (Spec R))ᵒᵖ ⥤ Type v` satisfy
`MurreConditions F`. Then `UnramifiedRepresentable F` holds: `F` is represented
by a separated, locally of finite type, formally unramified scheme over
`Spec R`. This is the induction step of Case I in Murre's outline, Steps 1, 2a
and 2b (J. P. Murre, Séminaire Bourbaki exp. 294, Section 2, printed
pp.247–249, PDF pp.6–8). The theorem adds no hypothesis.

## Proof

The proof is one term:

```lean
murreLocalStep_of_parts ⟨murreArtinianBase, murreCompleteLocalStep, murreCompletionDescent⟩
```

It uses four published Library results.

- `murreLocalStep_of_parts : MurreLocalStepPartsStatement.{u, v} →
  MurreLocalStepStatement.{u, v}` (module `MurreLocalStepReduction`). It does
  the dimension bookkeeping. If `n = 0`, then `R` is artinian and Step 1
  applies. If `n > 0`, the induction hypothesis gives representability over the
  punctured spectra of `R` and of its completion `R̂`, whose local rings have
  dimension `< n`. It also gives representability over the artinian quotients
  `R̂/m̂^(k+1)`, whose local rings have dimension `0 < n`. Mathlib's
  `AdicCompletion` makes `R̂` complete, so Step 2a gives representability over
  `Spec R̂`. Step 2b then descends it to `Spec R`.
- `murreArtinianBase : MurreArtinianBaseStatement.{u, v}` (module
  `MurreArtinianBase`), Step 1. If `R` is a local artinian ring and
  `MurreConditions F` holds, then `UnramifiedRepresentable F`.
- `murreCompleteLocalStep : MurreCompleteLocalStepStatement.{u, v}` (module
  `MurreCompleteLocalStepProof`), Step 2a. Let `R` be a complete local
  noetherian ring and let `F` satisfy the conditions. Suppose `F` is
  representable over the punctured spectrum and over every `Spec (R/m^(k+1))`.
  Then `F` is representable.
- `murreCompletionDescent : MurreCompletionDescentStatement.{u, v}` (module
  `MurreCompletionDescentProof`), Step 2b. Let `R` be a local noetherian ring
  and let `F` satisfy the conditions. Suppose `F` is representable over the
  punctured spectrum of `R` and over `Spec R̂`. Then `F` is representable.

Here "representable" means `UnramifiedRepresentable` of the corresponding base
change. The three step statements and the reduction were published together in
module `MurreLocalStepParts` and module `MurreLocalStepReduction`. The anonymous
constructor builds their conjunction `MurreLocalStepPartsStatement.{u, v}`.

The import closure does not use `MurreCriterionStatement` (only the condition
definitions in its module) or `MurreProofStepsStatement`. It uses no other
statement excluded by the task.
