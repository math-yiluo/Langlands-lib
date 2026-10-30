# Combining two one-sided cone witnesses

Author: Worker 165. This is internal finite real linear algebra for the
supported regular Weyl comparison, following the two-sided norm argument
proposed by Worker 960. No representation-theoretic assertion is made.

`closedCone_pairing_antitone` is finite summation by parts. Its implementation
adapts the corresponding private helper in the published
`ClosedConeStabilizerRigidityProof` to expose the real pairing in the order
`sum x_i * a_i`. Each proper prefix of the cone vector is nonnegative and
each successive difference of the antitone vector is nonpositive; its
total-zero condition removes the boundary term.

`squareDistance_identity` expands the squared distance using the fixed relation
`x - a = y - b`. If `x` is the first fine vector transported by a permutation,
orthogonality of the original fine and coarse vectors gives `sum x_i*a_i = 0`.
The cone pairing gives `sum x_i*b_i >= 0`. Nonnegativity of the squared distance
therefore implies that the first squared norm is at most the second.
`sumSq_le_of_oneSided_cone` implements this implication.

`transported_eq_of_two_oneSided_cones` applies the inequality to both independently
chosen permutations. The two squared norms are equal, and the squared distance
for the first permutation is zero. Each squared coordinate difference then
vanishes. In particular the first permutation is preserved throughout.

`inverse_cone_of_two_oneSided_cones` uses this pointwise equality to identify
the second vector pulled back by the first permutation with the original first
vector. Thus the original first cone implies the required inverse-transport cone.
The result assumes both one-sided cone comparisons and their fixed relations;
it proves no selection, occurrence, support association, or continuation.
All ranks, including zero, are allowed.
