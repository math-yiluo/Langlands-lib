# Cohomology of large twists on the fibres of a projective flat family (proof)

Authors: Worker 5705.

The module `Langlands.AlgebraicGeometry.Modules.ProjectiveFibreTwistCohomologyProof` proves

```lean
theorem projectiveFibreTwistCohomology : ProjectiveFibreTwistCohomologyStatement.{u}
```

The three clauses are proved in helper modules (namespace
`Langlands.AlgebraicGeometry.Modules.FibreTwist`):

1. Uniform vanishing near every point: `uniformVanishing`, module
   `ProjectiveFibreTwistUniformVanishing`. It combines relative Serre vanishing on an affine
   noetherian neighbourhood (The Stacks Project, Tag 02O1, from the FLT port's projective-space
   Čech cohomology) with the perfect model of the semicontinuity proof and the algebraic form of
   Mumford's Corollary 3 (*Abelian Varieties*, II §5, p.53).
2. Nonzero sections on nonempty fibres: `nonzeroSections`, module `ProjectiveFibreTwistSections`.
   It uses global generation of large twists (FLT port; The Stacks Project, Tag 01Q3) and nonzero
   sections of invertible modules on nonempty affines.
3. Polynomial Euler characteristics of degree at most `N`: `eulerPolynomial_of_point`, module
   `ProjectiveFibreTwistEuler`, at the point `T.fromSpecResidueField t` over the residue field
   (`Field.toIsField`). It uses the FLT port's Hilbert-polynomial theorem with its dimension bound
   for closed subschemes of `ℙᴺ` (The Stacks Project, Tag 0BEM). The Library's
   `fibreEulerCharacteristic` is unfolded to the alternating sum that this lemma computes.

The literature ids are `stacks-projective-cohomology-ample-2026-11-13` and
`mumford-abelian-varieties-chapter-ii-scan`. The proof uses only the axioms `propext`,
`Classical.choice` and `Quot.sound`.
