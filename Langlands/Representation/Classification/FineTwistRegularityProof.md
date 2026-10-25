# Proof of actual fine real-twist regularity

Author: Worker 166.

`Langlands.fineTwistRegularity` proves the published fine-twist regularity
statement by specializing scalar-twist and group-transport results.

The exact target is `Langlands.FineTwistRegularityStatement`,
with independent field and carrier universes. The proof introduces no
additional hypotheses and includes rank zero.

For an element of the actual refined unipotent radical, each block
component belongs to the corresponding standard unipotent subgroup.
The published determinant-one theorem makes each real determinant
character factor equal to one. Their finite product is therefore one,
proving `refinedUnipotent_le_ker_leviRealPowerCharacter`.

The published open-kernel result for the real Levi character allows
`isAdmissible_twist_iff` to prove admissibility invariance.
`isIrreducible_twist_iff` gives irreducibility invariance directly.
For each proper standard refinement, character triviality allows
`Jacquet.subsingleton_coinvariants_twist_iff` to identify vanishing of
the actual coinvariant modules. Quantifying over refinements proves
quasicuspidality invariance; combining it with admissibility proves
cuspidality invariance.

For the exact fine twist, the proof first applies these results to the
flattened product Levi with exponent
`-v₀(k) + t(((B.flattenBlockEquiv S).symm k).1)`.
It then pulls the twisted action back along the inverse of the published
flattened-Levi equivalence. The existing irreducibility pullback theorem
uses its multiplicative equivalence; the admissibility pullback theorem
uses its continuous multiplicative equivalence for the topology from `T`.
The needed topological-ring instance is derived from `T.moduleTopology`
by `IsModuleTopology.isTopologicalRing (Padic p) F.Carrier`; no extra
compatibility hypothesis is supplied.
Their underlying homomorphism is exactly the one used by `fineTwist`.
The final conjunct retains cuspidality on the flattened product Levi.

The final theorem assembles the three preservation clauses and the fine
specialization. Its inputs are the published twist, determinant,
coinvariant, and group-transport results named in the imports. This is
an internal specialization and transport argument. No generic comparison,
extraction, second adjointness, or classification theorem is used.
