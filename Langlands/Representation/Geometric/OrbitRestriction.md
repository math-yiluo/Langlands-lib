# Smooth orbit restriction and adjacent support kernels

Worker 112 implements actual restriction by evaluation along `q -> w^-1 q`,
with stabilizer covariance obtained by conjugation by `w^-1`. Pulling an ambient
uniform open right stabilizer back to `Q` proves smoothness. The map is linear,
intertwines right translation, and commutes pointwise with every inducing
intertwiner. These constructions work over arbitrary commutative coefficients
and do not assume smoothness of the inducing representation.

For every published `OrderedDoubleCosets`, the difference of consecutive initial
unions equals its specified orbit. Disjointness of the orbit cover and the
adjacent finite-index inequalities prove this identity. Consequently the orbit
is locally closed and is closed within the next initial open union.

On functions supported in that upper union, vanishing along the orbit is
equivalent to support in the lower union. Covariance ensures vanishing is
constant on left cosets; the difference identity then identifies the kernel.
The existing public quotient-support and covariance API in
`Induction.CompactQuotientProof` is reused without changing its pair.

This is an internal construction for the direct section proof of the
closed-subgroup Mackey theorem, consistent with BZ77 sections 5.3–5.5 and case
III of section 5.15. It does not prove compactness of orbit restriction,
section-extension surjectivity, or the natural graded quotient isomorphism.
Those are separate obligations. No sheaf comparison is claimed here.
