# Proof: the agreement locus of two rigidified classes over an affine base

Author: Worker 281.

This module proves the published proposition
`Langlands.AbelianScheme.RigidifiedClassesEqualizerClosedAffineStatement.{u}` from module
`Langlands.AlgebraicGeometry.Picard.RigidifiedClassesEqualizerClosedAffineStatement`:

```lean
theorem Langlands.AbelianScheme.rigidifiedClassesEqualizerClosedAffine :
    RigidifiedClassesEqualizerClosedAffineStatement.{u}
```

For a commutative ring `R`, an abelian scheme `A` over `Spec R` and two actual rigidified classes
`q`, `r` on `Spec R ×_{Spec R} A`, there is a closed immersion `ι : Z ⟶ Spec R` such that a
morphism `h : T' ⟶ Over.mk (𝟙 (Spec R))` factors through `ι` exactly when the rigidified
pullbacks of `q` and `r` along `h` are equal. The theorem has no hypotheses beyond those of the
statement, and it holds for every universe `u`.

## Proof

The proof applies three published theorems. The published reduction
`Langlands.AbelianScheme.rigidifiedClassesEqualizerClosedAffine_of_noetherian` (module
`Langlands.AlgebraicGeometry.Picard.RigidifiedClassesEqualizerClosedAffineFromNoetherianProof`)
proves `RigidifiedClassesEqualizerClosedAffineFromNoetherianStatement.{u}`, which is the
implication

```lean
RigidifiedClassesEqualizerClosedNoetherianAffineStatement.{u} →
  RigidifiedClassesNoetherianApproximationStatement.{u} →
  RigidifiedClassesEqualizerClosedAffineStatement.{u}
```

Its Markdown file describes the argument: noetherian approximation replaces `R`, `A`, `q`, `r`
by a noetherian ring `R₀` with a ring map `R₀ ⟶ R` and data over `Spec R₀` that have the same
agreement predicate. The noetherian case then gives a closed subscheme of `Spec R₀`. Its pullback
along `Spec R ⟶ Spec R₀` is the required closed subscheme of `Spec R`. The two hypotheses are
discharged by:

- `Langlands.AbelianScheme.rigidifiedClassesEqualizerClosedNoetherianAffine`
  (module `Langlands.AlgebraicGeometry.Picard.RigidifiedClassesEqualizerClosedNoetherianProof`),
  which proves `RigidifiedClassesEqualizerClosedNoetherianAffineStatement.{u}`;
- `Langlands.AbelianScheme.rigidifiedClassesNoetherianApproximation`
  (module `Langlands.AlgebraicGeometry.Picard.RigidifiedClassesNoetherianApproximationProof`),
  which proves `RigidifiedClassesNoetherianApproximationStatement.{u}`.

All three theorems are used at the universe `u` of the target. The proof term elaborates
without any unfolding. It does not use the general
`RigidifiedClassesEqualizerClosedStatement` or any other unproved hypothesis.

## Provenance

The mathematical route is the standard reduction to the noetherian case by limit arguments
(Stacks Project, Chapter 32 "Limits of Schemes"), combined with the noetherian case of Stacks
Project, *More on Morphisms*, Lemma 37.33.4 (tag 0BF0). The provenance of the statements is
given in their own Markdown files. This file adds no new mathematics: it only combines published
Library results. The decomposition into the noetherian case, noetherian approximation and the
reduction was planned by Worker 848, who proved the reduction.
