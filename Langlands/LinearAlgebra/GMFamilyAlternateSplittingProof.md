# Alternate splitting for `(G, M)`-families

`Langlands.GMFamily.alternateSplittingFormula` proves
`Langlands.GMFamily.AlternateSplittingFormulaStatement`. It chooses as the
exceptional vectors all nonzero orthogonal restrictions of roots to `a`.

For a fixed pair of chambers, the proof first expands `cQM` for each family
into its incident chambers by adjoining the positive roots of the face to a
chamber of its Levi roots. The local simple roots are the global simple roots
whose evaluations on the face vanish. This expresses the coefficient of
`c P₁ Λ * d P₂ Λ` as a sum over complementary Levi flats whose sections are
incident to `P₁` and `P₂`.

The two chambers are translated by opposite displacements in
`a ∩ (centralSpace R)ᗮ`. Each incident Levi pair gives a feasible intersection
of a basis of the two sets of labelled simple inequalities, with the remaining
inequalities strict. Conversely a feasible intersection determines the two
flats from its tight normals. The section points are `x + ξ` and `x − ξ` for
the intersection `x`. The regularity premise gives nonzero slack for every
inequality outside the chosen basis. Change of basis in the two normal spaces
factors the combined Gram volume into the two local Gram volumes and
`dCoeff`. The denominator factors according to the same two sets of normals.

The affine coefficient sum is invariant under changing generic intercepts.
At a wall its change is the sum of a linear dependence among the normals with
one extra tight inequality, evaluated at the imaginary parameter. A generic
segment reduces arbitrary changes of intercepts to this cancellation. For two
distinct chambers, a root and its negative are positive on the two respective
chambers, so positive reference intercepts give no feasible basis. For a
repeated chamber, reference intercepts with the left bounds strictly larger
than their right duplicates give the single left basis, with weight
`(theta a P₁ Λ)⁻¹`. Summing the resulting diagonal coefficients gives `cM` of
the product. Only pointwise values of the two families enter this argument.

## Sources and inputs

The statement corresponds to J. Arthur, *An introduction to the trace formula*,
§17, Lemma 17.6, printed p. 101 (PDF p. 113), registered as
`arthur-ellwood-kottwitz-2005-harmonic-analysis-shimura`, SHA-256
`88ba9a23fa62e2f62f14af7a5a2a8ffb062be29fc4590bf39c60c173add0a8a7`.
The direct Euclidean coefficient and the two-family summand follow the
conventions of Arthur, *The invariant trace formula. I. Local theory*, §7,
Corollary 7.4 and the determinant definition on printed pp. 356 and 358
(PDF pp. 34 and 36), registered as `arthur-1988-invariant-trace-formula-I`,
SHA-256 `902db792ffe113507165a252b0c1b8c59f78ab8d04def1c5c39b0372362dc3ac`.
The affine proof is a direct derivation from chamber geometry and finite
linear algebra. Its supporting modules are
`GMFamilyRootGeometry`, `GMFamilyAffineBases`, `GMFamilyAffineWall`,
`GMFamilyAffineInvariance`, `GMFamilySplittingMeasures`,
`GMFamilySplittingGeometry`, `GMFamilySplittingReference`,
`GMFamilySplittingWeights` and `GMFamilySplittingVertices`.
