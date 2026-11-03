# Proof of splitting and topology for a finite projective ring extension

Author: Worker 105.

The theorem `finiteProjectiveAlgebraTopologyProperties_proof` proves exactly
`FiniteProjectiveAlgebraTopologyProperties R S`.

The auxiliary theorem `finiteProjectiveAlgebra_isUnimodular_one` first
constructs a linear functional taking 1 in S to 1 in R, that is, it proves
Mathlib's `Module.IsUnimodular R (1 : S)`. Let I be the ideal of values at 1
of all R-linear functionals S → R. The finite free splitting of S from
`Module.Finite.exists_comp_eq_id_of_projective` gives a finite dual-coordinate
expansion of 1. Every coefficient of this expansion lies in I, so the
extension of I to S contains 1 and is the unit ideal. Since S is finite over
R it is integral; because R → S is injective (`FaithfulSMul`), Mathlib's
integral lying-over consequence `Ideal.map_eq_top_iff` implies that I itself
is the unit ideal. A functional with value 1 therefore exists.

Linearity makes this functional a retraction of the coefficient map:
l (algebraMap R S r) = l (r • 1) = r. For the canonical module topology on S,
`IsModuleTopology.isTopologicalRing` supplies the topological-ring structure,
and `IsModuleTopology.continuous_of_linearMap` gives continuity of both the
retraction and the coefficient map `Algebra.linearMap R S`. The continuous
left-inverse criterion `Function.LeftInverse.isEmbedding` then proves that
R → S is a topological embedding. No separation hypothesis is used.

This follows the splitting assertion of Conrad Example 2.4, printed page 3,
using finite projective coordinates and integral ideal extension rather than
assuming freeness or assuming the splitting. The module quotient-topology
comparison and the Weil-restriction construction and point-space comparison
remain separate obligations.
