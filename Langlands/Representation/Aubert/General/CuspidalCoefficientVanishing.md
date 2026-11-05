# Coefficient vanishing from genuine Jacquet relations

This is an internal helper for the proof of Renard VI.2.1 (a) ⇒ (c). It implements
the finite-relation step behind the coefficient calculation on printed p.139 / PDF
p.145 of the 2026 edition. It does not assert the full compact-restriction theorem.

`Jacquet.exists_finset_map_apply_eq_zero_of_mem_relations` works over a commutative
ring, with independent group, source and output universes. For a vector in the actual
coinvariant relation submodule and a linear map invariant under a subgroup `K`, it
constructs a finite set of radical elements. Every translating element that conjugates
this finite set into `K` gives zero after applying the linear map. The proof is span
induction on the genuine generators `ρ(n)w - w`, using conjugation for each generator,
finite unions for sums and the same finite set for scalar multiplication.

`Jacquet.relationContractionWitness` constructs a chosen finite witness from this
existence theorem. It is a noncomputable finite set of actual radical elements,
depending on the representation, radical, subgroup, invariant linear map and
relation vector. `Jacquet.relationContractionWitness_spec` proves its contraction
property. This construction makes the witness available as data for subsequent
finite-family wall arguments.

`UniformCompactContainment.exists_epsilon_map_apply_eq_zero` regards that finite set as
a compact subset of the radical and applies the first clause of the published
`UniformCompactContainment`. Consequently, one positive epsilon threshold works for
all translating elements in the corresponding epsilon chamber. No monotonicity of the
chambers is required. The matrix-coefficient corollary converts a vector fixed under
the dual `K`-action into the required invariance of evaluation.

The imported mathematical interfaces are `Jacquet.relations` and
`Jacquet.relations_eq_span` from `Langlands.Representation.Jacquet.Coinvariants`,
`matrixCoefficient` and its evaluation convention from
`Langlands.Representation.MatrixCoefficient.LawsProof`, and
`UniformCompactContainment` / `ambientConjugate` from
`Langlands.BruhatTits.SpecialCompact.ContractionPredicates` (through
`StandardBasisProperty`). These are existing actual quotient and subgroup objects.
There is no admissibility or finite-dimensionality premise. The helper alone supplies
neither a bounded support set nor the comparison between the maximal split torus
Cartan cone and a compatible standard split-component epsilon cone.
