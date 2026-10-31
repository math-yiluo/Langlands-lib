# Proof: the agreement locus of two rigidified classes over a noetherian affine base

Authors: Worker 766, Worker 1048.

This module proves the published proposition
`Langlands.AbelianScheme.RigidifiedClassesEqualizerClosedNoetherianAffineStatement.{u}` from
module `Langlands.AlgebraicGeometry.Picard.RigidifiedClassesEqualizerClosedNoetherianStatement`:

```lean
theorem Langlands.AbelianScheme.rigidifiedClassesEqualizerClosedNoetherianAffine :
    RigidifiedClassesEqualizerClosedNoetherianAffineStatement.{u}
```

For a noetherian ring `R`, an abelian scheme `A` over `Spec R` and two actual rigidified classes
`q`, `r` on `Spec R ×_{Spec R} A`, there is a closed immersion `ι : Z ⟶ Spec R` such that a
test scheme `T' ⟶ Spec R` factors through `ι` exactly when `q` and `r` agree after rigidified
pullback to `T'`. The theorem has no hypotheses beyond those of the statement.

## Proof

The proof is a single application of three published theorems to the published reduction
`Langlands.AbelianScheme.rigidifiedClassesEqualizerClosedNoetherianAffine_of_seesaw`
(module `Langlands.AlgebraicGeometry.Picard.RigidifiedClassesEqualizerClosedNoetherianOfSeesawProof`).
That reduction proves the implication

```lean
NoetherianLineBundleSeesawStatement.{u} → RigidifiedClassesZariskiSeparatedStatement.{u} →
  SmoothGeometricIntegrality.{u} → RigidifiedClassesEqualizerClosedNoetherianAffineStatement.{u}
```

Its Markdown file describes the argument. Smooth geometric integrality makes the structure
morphism of `A` geometrically integral; with the published
`Langlands.AlgebraicGeometry.smoothProperConnectedGlobalFunctions` this gives the
global-functions hypothesis of the seesaw. The seesaw then gives a closed subscheme of `Spec R`
cutting out the locus where the carrier sheaves of representatives of `q` and `r` become locally
isomorphic over the test scheme. Zariski separatedness turns that local isomorphism into
equality of the rigidified classes. The three hypotheses are discharged by:

- `Langlands.AlgebraicGeometry.Picard.noetherianLineBundleSeesaw`
  (module `Langlands.AlgebraicGeometry.Picard.NoetherianLineBundleSeesawProof`), which proves
  `NoetherianLineBundleSeesawStatement.{u}` from the ported Anthropic FLT theorem
  `AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_isClosedImmersion_forall_iff_locallyIsoOver_of_flat_of_isProper`;
- `Langlands.AbelianScheme.rigidifiedClassesZariskiSeparated`
  (module `Langlands.AlgebraicGeometry.Picard.RigidifiedClassesZariskiSeparatedProof`), which
  proves `RigidifiedClassesZariskiSeparatedStatement.{u}`;
- `Langlands.AbelianScheme.smoothGeometricIntegrality`
  (module `Langlands.AbelianScheme.SmoothGeometricIntegralityProof`), which proves
  `SmoothGeometricIntegrality.{u}`.

All four theorems are used at the same universe `u` as the target, and the term elaborates
without further unfolding. The proof uses only the axioms `propext`, `Classical.choice` and
`Quot.sound`.

## Provenance

The mathematical route is that of the reduction: the standard argument behind Stacks Project,
*More on Morphisms*, Lemma 37.33.4 (tag 0BF0). This file adds no new mathematics; it only
combines published Library results. It was planned jointly with Worker 1048, who led the port
of the noetherian seesaw used here.
