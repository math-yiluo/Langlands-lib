# Open stabilizers of Schwartz–Bruhat row test functions

`Langlands.HarmonicAnalysis.RowTestSmoothStatement F n` states that every
Schwartz–Bruhat function on the row space `Fin n → F` is invariant under right
multiplication by some open subgroup of `GL_n(F)`. The subgroup may depend on
the function. Its invariance holds for every row, including rows outside the
function's support.

The field has a topology making addition and multiplication continuous.
No continuity of field inversion, local compactness of the field, separation
axiom, or restriction on the natural-number rank is assumed. The general linear
group carries the existing topology on matrix units, in which both a matrix and
its inverse are coordinates. `SchwartzBruhat` already includes local constancy
and compactness of the topological support. The field universe is arbitrary.

This is a derived topological target, not a verbatim theorem from the
literature. It supports the compact-group finiteness step in the proof of
Theorem 2.7 of Jacquet–Piatetski-Shapiro–Shalika, *Rankin–Selberg Convolutions*
(1983), printed p. 391, immediately before display (3). The source applies that
step to p-adic fields. The present generalization isolates the elementary
topological argument: local constancy gives an open equality relation, the tube
lemma makes invariance uniform on compact support near the identity, and a
symmetric identity neighborhood extends it to all rows. This explanation is a
proof plan; this module only defines the proposition.

This statement supplies no convergence, rational continuation, or normalized
generator theorem for Rankin–Selberg integrals.

Source: `jpss-1983-rankin-selberg`, SHA256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`,
printed p. 391.
