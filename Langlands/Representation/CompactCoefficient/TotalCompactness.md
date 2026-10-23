# Compactness and exhaustion of the total compact-isotypic part

This internal derivation supplies two inputs to the published conditional
decomposition construction. It uses the published extension of smooth
functionals and the separating-intertwiner proof of compact-coefficient
semisimplicity. It does not assert the remaining intrinsic-complement,
fixed-stratum finiteness or Harish-Chandra results.

The compact-coefficient vector submodule consists of vectors whose coefficients
against every ambient smooth functional have compact support. Addition and
scalar multiplication preserve it by the corresponding compact-support laws.
Every intertwiner from a compact-coefficient representation has image in this
submodule: pull the smooth functional back along the intertwiner.

If compact open subgroups are cofinal among open subgroups, smooth functionals
on a smooth subrepresentation extend to the ambient smooth representation,
by the published smooth-contragredient surjectivity theorem. Thus a
subrepresentation contained in the compact-coefficient vector submodule has
compact smooth-dual coefficients. In particular, compact coefficients pass
to actual subrepresentations.

The total isotypic part is the supremum of the images of all compact-coefficient
irreducible representatives. Every such image lies in the compact-coefficient
vector submodule, so the total part does too. Applying the preceding extension
argument proves compactness of its intrinsic smooth-dual coefficients. The
representative and ambient carrier universes are independent in this result.

For exhaustion, assume a Hausdorff, locally compact, totally disconnected
topological group with a Borel structure and a left Haar measure, and a smooth
representation with compact coefficients. The published separating-intertwiner
and lattice lemmas give that its atomic subrepresentations have supremum top.
Each atom is irreducible: the subrepresentation-submodule order isomorphism
preserves atoms, and its group-algebra module is isomorphic to the corresponding
simple submodule. Compact coefficients pass to the atom by smooth-functional
extension. It therefore defines a compact-coefficient irreducible
representative in the ambient carrier universe, and its inclusion has image
in the total isotypic part. The supremum of all atoms is top, so the total part
is top.

The exhaustion result uses the same universe for representatives and ambient
carriers, independent of the group universe. It does not assume admissibility,
finite length, finite dimension, unimodularity or countability. The group
hypotheses provide compact-open cofinality and the hypotheses of the published
semisimplicity helpers. These are internal consequences of the imported
Library theorems, not new translations of literature statements.

## Exported interfaces and provenance

- `Langlands.compactCoefficientVectors` is a complex submodule; it makes no
  assertion that the ambient representation is smooth.
- `Langlands.range_le_compactCoefficientVectors` uses only the source
  compact-coefficient property and intertwining, with independent carriers.
- `Langlands.hasCompactSmoothDualCoefficients_subrepresentation_of_le` and
  `Langlands.hasCompactSmoothDualCoefficients_subrepresentation` require a
  smooth ambient object and compact-open cofinality in a topological group.
- `Langlands.CompactCoefficientClass.totalIsotypicSubrepresentation_le_compactCoefficientVectors`
  is algebraic and does not require compact-open cofinality.
- `Langlands.CompactCoefficientClass.totalIsotypicSubrepresentation_hasCompactSmoothDualCoefficients`
  requires the same compact-open cofinality as smooth-functional extension.
- `Langlands.CompactCoefficientClass.totalIsotypicSubrepresentation_eq_top_of_compactCoefficients`
  takes a left Haar measure and the topological hypotheses described above.

The exhaustion proof invokes
`CompactCoefficientSemisimplicity.sSup_atoms_eq_top_of_separating` with
`CompactCoefficientSemisimplicity.exists_intertwiner_separating` directly;
it does not infer atomicity from an unproved semisimplicity assertion.
The private irreducibility bridge uses the group-algebra codomain restriction
pattern also present in the published
`Langlands.Representation.Filtration.NonzeroHomCommonSubquotientProof`.
All imported Library results are unchanged.

Worker 173 wrote the module and explanation. Worker 261 advised the
atomic-subrepresentation route to exhaustion and identified the reusable
semisimplicity helpers. Development compilation `78eb4744-5561-45e8-b90a-ff68b71c53c8`
finished with no errors or warnings; acceptance and publication remain separate.
