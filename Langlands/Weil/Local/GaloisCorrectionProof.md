# Actual local Galois type and commuting unramified correction

Worker 32 proves the existing `LocalWeilGaloisTypeFor` and
`LocalWeilUnramifiedCorrectionFor` in `Langlands.Weil.Local`. Both proofs retain
all primes, all actual finite p-adic fields in universe `u`, and an independent
representation-carrier universe `v`. The original statement pair is unchanged.

The Galois-type proof equips the original carrier with its canonical normed
complex structure and applies `FiniteRepresentation.isContinuous_of_iff`.
The field has characteristic zero via its injective p-adic algebra map, so its
algebraic closure is Galois and Mathlib supplies compactness of the absolute
Galois group. The compact Hausdorff actual absolute Galois group is nonarchimedean by
`LocalClassField.absoluteGaloisNonarchimedean`. The published
`finiteImageExtension` specializes to `localResidueDegree F`, which is
surjective, and constructs the unique continuous extension on that carrier.
Conversely, an actual continuous Galois extension restricts continuously along
`localProjection F`; its image is finite by
`continuous_compact_nonarchimedean_representation_finite_range`, so its
restriction has finite image too. Continuity of the original representation is
therefore a conclusion in this direction.

For the correction, compactness and openness of the actual inertia subgroup
come from `AssemblyProof`. The published
`Langlands.subgroupNonarchimedean` instance restricts the local Weil group
nonarchimedean structure to the degree kernel. The inertia subgroup
is definitionally the kernel of the actual degree map, which is surjective.
The first clause of `unramifiedReduction` then supplies the commuting
unramified correction and its finite-image product on the original carrier.
Continuity is transported back to the bundled predicates; the first theorem
supplies actual Galois type of the product. This works also in dimension zero
and imposes no irreducibility or semisimplicity condition.

These are internal specializations of published generic proofs, rather than
new statements or new local Langlands assertions. The source correspondence
is inherited from [RepresentationStatements.md](RepresentationStatements.md):
Henniart 1980 sections 2.1–2.6 and Tate sections 2.2–2.2.1. The implemented
routes are those in the imported
[finite-image extension proof](../Representation/FiniteImageExtensionProof.md)
and [unramified reduction proof](../Representation/UnramifiedReductionProof.md),
with the actual-group inputs supplied by [AssemblyProof.md](AssemblyProof.md)
and the topology adapters in
[ContinuityBridgeProof.md](../Representation/ContinuityBridgeProof.md).
