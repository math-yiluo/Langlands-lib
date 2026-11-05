# Decomposition for a continuous central group action

Author: Worker 1666.

This supporting module derives the characteristic-space algebra used by Renard
2026, VII.1.1, printed page 220 / PDF page 226. It uses the already published
compact-open weight spaces and central-character decomposition, without adding
a claim of Jacquet admissibility or finite-length preservation.

`GeneralizedWeightDecompositionStatement` names the conjunction of independence
and spanning over the smooth nonzero generalized weights of the given central
map. `generalizedWeightSpace_decomposition` proves this property for an
admissible representation over an algebraically closed coefficient field when
the central map is continuous.

For a smooth representation, the published membership formula identifies each
weight vector by a single exponent that works for all points of the acting
group. The independence proof embeds these spaces in intersections of maximal
generalized eigenspaces and applies Mathlib's independence theorem. Distinct
characters remain distinct as scalar-valued functions.

For a center-finite representation, each full-center generalized character
restricts along the given central map. Its space lies in the corresponding
weight space. The published full-center spanning theorem therefore proves
spanning after restriction, even when different characters have the same
restriction. For an admissible representation, center-finiteness is already
proved. A nonzero generalized weight has open kernel by smoothness and
continuity of the central map. Removing zero spaces gives the stated internal
direct sum over the actual smooth, nonzero weights.

Finally, finite generation over the ambient group algebra makes its top
submodule compact. A finite subfamily of the weight subrepresentations
therefore spans. Independence forces every nonzero space to have its index in
that finite family, proving finiteness of the exponent set.

The coefficient field, both groups and the carrier have independent universes.
The acting group need not itself be commutative; its image is central.
Algebraic closedness is used for spanning, and is not needed for independence.
The generic finite-support theorem retains an explicit group-algebra
finite-generation premise.

The concrete wrappers use the published point maps and canonical topologies.
`groupWeightSpace_decomposition` proves the whole-group clause of VII.1.1,
and `leviWeightSpace_decomposition` proves the analogous decomposition for an
admissible representation of a closed literal Levi image. The topology of the
split component makes the corresponding point map continuous. In finite
length, Mathlib's Noetherian consequence gives group-algebra finite generation,
so `finite_leviExponents_of_finiteLength` proves finiteness.

`normalizedJacquetWeightSpace_independent` needs only smoothness, supplied by
the actual normalized Jacquet construction. The remaining Jacquet wrappers
explicitly assume admissibility and, for finiteness, finite length of that
Jacquet representation. They do not prove preservation of either property.
This module alone does not prove the full represented-parabolic VII.1.1
statement. The concrete wrappers require neither a local-field structure nor
connected reductivity beyond the hypotheses appearing in their statements.

The cited original is David Renard, *Représentations des groupes réductifs
p-adiques*, French edition dated 9 July 2026, registered source
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
These are internal derivations using `SplitComponentWeights`,
`CentralDecompositionProof`, and Mathlib, rather than new structural assertions
attributed to that passage.
