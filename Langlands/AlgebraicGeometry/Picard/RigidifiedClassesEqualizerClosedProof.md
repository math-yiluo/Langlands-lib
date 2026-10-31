# Proof: the locus where two rigidified classes agree is closed

Author: Worker 956.

This module proves the published proposition
`Langlands.AbelianScheme.RigidifiedClassesEqualizerClosedStatement.{u}` from module
`Langlands.AlgebraicGeometry.Picard.RigidifiedClassesEqualizerClosedStatement`:

```lean
theorem Langlands.AbelianScheme.rigidifiedClassesEqualizerClosed :
    RigidifiedClassesEqualizerClosedStatement.{u}
```

Let `A` be an abelian scheme over an arbitrary scheme `S`, let `T` be an object of `Over S`, and
let `q`, `r` be two actual rigidified classes on `T ×_S A`. Then there is a closed immersion
`ι : Z ⟶ T.left`, with `Z` in universe `u`, such that a morphism `h : T' ⟶ T` in `Over S`
factors through `ι` exactly when the rigidified pullbacks of `q` and `r` along `h` are equal.
See the statement's Markdown for the exact interface and the Stacks source (tags 0BDP and 0BF0).
The theorem has no hypotheses beyond those of the statement; its axioms are `propext`,
`Classical.choice` and `Quot.sound`.

## Proof

The module contains no new mathematics. Its one declaration is a single term that applies two
published implications to published proofs of their hypotheses:

```lean
rigidifiedClassesEqualizerClosedReduction
  (rigidifiedClassesEqualizerClosedAffine_of_noetherian
    rigidifiedClassesEqualizerClosedNoetherianAffine
    rigidifiedClassesNoetherianApproximation)
  rigidifiedClassesZariskiSeparated
```

All names are in `Langlands.AbelianScheme`.

1. **Reduction to an affine base.** `rigidifiedClassesEqualizerClosedReduction` (module
   `Langlands.AlgebraicGeometry.Picard.RigidifiedClassesEqualizerClosedReductionProof`) proves
   `RigidifiedClassesEqualizerClosedReductionStatement.{u}`, the implication
   `RigidifiedClassesEqualizerClosedAffineStatement.{u} →
   RigidifiedClassesZariskiSeparatedStatement.{u} → RigidifiedClassesEqualizerClosedStatement.{u}`.
   It glues closed subschemes over the affine opens of `T.left`, each obtained from the affine
   case after base change of `A` to the affine open.
2. **The affine case from the noetherian case.**
   `rigidifiedClassesEqualizerClosedAffine_of_noetherian` (module
   `Langlands.AlgebraicGeometry.Picard.RigidifiedClassesEqualizerClosedAffineFromNoetherianProof`)
   proves the implication
   `RigidifiedClassesEqualizerClosedNoetherianAffineStatement.{u} →
   RigidifiedClassesNoetherianApproximationStatement.{u} →
   RigidifiedClassesEqualizerClosedAffineStatement.{u}`: the closed subscheme found over a
   noetherian model `Spec R₀` is pulled back to `Spec R`.
3. **Noetherian affine case.** `rigidifiedClassesEqualizerClosedNoetherianAffine` (module
   `Langlands.AlgebraicGeometry.Picard.RigidifiedClassesEqualizerClosedNoetherianProof`) proves
   `RigidifiedClassesEqualizerClosedNoetherianAffineStatement.{u}`. It is the first argument in
   step 2.
4. **Noetherian approximation.** `rigidifiedClassesNoetherianApproximation` (module
   `Langlands.AlgebraicGeometry.Picard.RigidifiedClassesNoetherianApproximationProof`) proves
   `RigidifiedClassesNoetherianApproximationStatement.{u}`. It is the second argument in step 2.
   Steps 2 to 4 together give `RigidifiedClassesEqualizerClosedAffineStatement.{u}`, the first
   argument in step 1.
5. **Zariski separatedness.** `rigidifiedClassesZariskiSeparated` (module
   `Langlands.AlgebraicGeometry.Picard.RigidifiedClassesZariskiSeparatedProof`) proves
   `RigidifiedClassesZariskiSeparatedStatement.{u}`: two classes that agree on every member of
   an open cover of `T.left` are equal. It is the second argument in step 1.

Each component's own Markdown describes its proof and provenance.

## Provenance

The route through an affine base, a noetherian model and Zariski gluing follows the plan agreed
in this task by its executors, Worker 848 and Worker 956. The final composition is original to
this project. The underlying mathematics is that of Stacks Project Lemmas 37.33.1 (tag 0BDP) and
37.33.4 (tag 0BF0), registered as `stacks-picard-diagonal-seesaw-0bdp-0bf0-a04446e5`, together
with the standard limit arguments of Stacks Chapter 32 "Limits of Schemes", registered as
`stacks-limits-of-schemes-a04446e5`; the Lean proofs of the components need not follow the Stacks
proofs.
