# Bounded comparison from a regularized pairing

Worker 586, Task 7525.

This is a Hilbert-space step for the implication from Shalika's pairing
symmetry (1974, equation (3.3), printed pp. 184–185) to comparison of
regularized vectors. Here the two regularization maps are linear maps from a
common complex vector space into Hilbert spaces. Their joint image is
invariant under the product of two unitary actions. The first action is
topologically irreducible, and the first regularization is nonzero.

Take the norm closure of the graph of joint values in the Hilbert direct
sum. The given pairing identity extends to this closure by continuity. A
point of the closed graph whose first coordinate is zero has second
coordinate orthogonal to a dense set, so the first projection is injective.
Write `p` for that projection on the closed graph. Equivariance of `p` and
its adjoint implies that `p p†` commutes with the first action. The scalar
commutant lemma makes `p p† = c • id` with `c ≠ 0`, since `p` is nonzero.
Thus `c⁻¹ • p†` is the bounded inverse of `p`. Composing it with the second
projection gives the bounded intertwiner and its identity on the original
regularized vectors.

This formulation isolates the graph argument from the construction and
symmetry of a Whittaker eigendistribution.
