# Proof of field-extension descent for (G,M)-families

This module proves `Langlands.GMFamily.FieldExtensionDescentStatement`
([GMFamilyFieldDescentStatement](GMFamilyFieldDescentStatement.md)), J. Arthur, *An introduction
to the trace formula* (2005), Lemma 17.5 and (17.13), printed pp.99–100,
`arthur-ellwood-kottwitz-2005-harmonic-analysis-shimura`, as the theorem
`Langlands.GMFamily.fieldExtensionDescent`.

The proof applies `fieldExtensionDescent_of_inputs` to three theorems.

- `fieldLeviSplitComponentInclusion` factors the base change to `K` of the split component
  of `M` through the split component of `M₁`.
  [FieldLeviSplitComponentProof](../GroupScheme/Rational/FieldLeviSplitComponentProof.md)
- `leviWeightFibreDeterminant` identifies the multiplicity-weighted sum of the fine roots
  over a nonzero coarse character with the restriction of a rational character over `k`.
  The character is the determinant of `M` acting on the corresponding coarse weight space.
  [LeviWeightFibreDeterminantProof](../GroupScheme/Lie/LeviWeightFibreDeterminantProof.md)
- `leviSplitComponentRootDatum` identifies the real cocharacters of the split component
  with a root flat in a maximal split torus. Integral reflections in the relative roots
  preserve the dimensions of the adjoint weight spaces.
  [LeviSplitComponentRootDatumProof](../GroupScheme/Rational/LeviSplitComponentRootDatumProof.md)

The assembly uses these comparisons to choose Euclidean coordinates compatible with
restriction of rational characters. In those coordinates the coarse space satisfies
the weighted special-subspace condition. The Euclidean descent identity extends from
generic imaginary parameters to the smooth supplementary functions everywhere by
continuity, including at zero.
[GMFamilyFieldDescentAssembly](GMFamilyFieldDescentAssembly.md)
