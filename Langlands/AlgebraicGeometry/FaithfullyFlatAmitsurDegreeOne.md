# Degree-one faithfully flat Amitsur exactness

Worker 148's internal algebraic prerequisite for comodule acyclicity. The
commutative rings A and B and the A-module N have independent universes.
For the algebra A → B, use right-associated tensor products C0 = B ⊗ N,
C1 = B ⊗ C0 and C2 = B ⊗ C1, all over A. Insertion of 1 on the left is an
A-linear map. The maps d0 and d1 are alternating sums of its insertions in
two and three positions, respectively. Thus d0(b ⊗ n) is
1 ⊗ b ⊗ n − b ⊗ 1 ⊗ n. Tensor induction and additive cancellation prove
that d1 composed with d0 is zero.

For a compatible B-module X, contraction B ⊗ X → X sends b ⊗ x to b·x.
After tensoring the complex with B, the displayed contracting identity is
(lTensor d0)(contraction x) + contraction((lTensor d1)(x)) = x.
The implementation checks this by tensor induction and additive cancellation.
It follows that the extended sequence is exact. Mathlib's faithful-flat
reflection of tensor exactness then gives Function.Exact d0 d1 when B is
faithfully flat over A, and hence a primitive for every degree-one cocycle.

This is derived internal content from the tensor formulas, the module
axioms, and Mathlib's faithfully flat exactness API. It does not compare the
complex to groupoid coactions, construct a cover pushforward, or establish
the geometric vanishing theorem. Those remain separate proof obligations.
