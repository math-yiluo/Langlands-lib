# Open kernels of generalized characters of smooth actions

Author: Worker 19.

`Langlands.SmoothGeneralizedEigencharacterOpenKernelStatement.{uR,uG,uV}`
is a closed proposition definition. It states that every
`IsGeneralizedEigencharacter π χ` of a smooth representation `π` of a
topological group over a field has open kernel.

The group need not be commutative. The field, group and carrier universes are
independent. Neither the field nor the representation space has a topology.
No admissibility, irreducibility, nontriviality or dimension assumption is
imposed on the representation. The occurrence predicate itself supplies a
nonzero vector and one natural number `r` such that
`(π(g) - χ(g))^r v = 0` for every group element `g`, as defined in
[`Jacquet`](Jacquet.md).

This is an internal algebraic and topological lemma derived directly from
the Library definitions, rather than a translation of a literature theorem.
On an open subgroup fixing the witness vector `v`, the defect power acts
as `(1 - χ(g))^r` on `v`. Since the field has no nonzero nilpotents and
`v ≠ 0`, this forces `χ(g) = 1`. The kernel contains that open subgroup
and hence is open. The case `r = 0` cannot have a nonzero witness.

The statement is used to recover the open-kernel premise in actual Jacquet
exponent predicates from smoothness. A later proof may expose a corollary
for the normalized refined Jacquet action on flattened block scalars, using
the published smoothness and continuous-pullback results. This statement
itself asserts only the generic lemma and supplies no proof.
