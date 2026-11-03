# Scheme quotients by smooth closed subgroups

Author: Worker 424.

This pair states two general prerequisites for algebraic flag quotients. Both
are propositions at arbitrary universe `u`, over every field, with the existing
actual group schemes and actual relative scheme morphisms. Neither proposition
is proved here.

`SmoothSubgroupQuotientExistenceStatement` concerns a smooth affine group
scheme `G` over `Spec k` and a closed subgroup `i : H → G` with `H` smooth.
It asks for a separated finite-type scheme `Q` over `k` and a smooth,
surjective, quasi-compact morphism `q : G.X → Q`. On every test scheme `T`
over `k`, equality of the images of two actual points `g,h` must be equivalent
to `g⁻¹h` belonging to `SubgroupFunctor.range i` at `T`. The orientation is
that of right cosets `gH`. In particular, the test schemes need not be affine
or reduced.

The geometric hypotheses on `G` ensure it is of finite type over `k`: affine
morphisms are quasi-compact, and smooth morphisms are locally of finite
presentation. The closed subgroup is then also of finite type. The statement
does not assume connectedness, reductivity, splitness or any condition on the
field's cardinality or characteristic.

This is a derived formulation of J. S. Milne, *Algebraic Groups* (2017),
Definition 5.20 and Propositions 5.24–5.25, printed pp.104–105, together with
Proposition 7.15 and Theorem 7.18, printed pp.142–143. Theorem 7.18 constructs
the separated scheme quotient of a smooth affine group by an algebraic
subgroup. Proposition 7.15 gives smoothness of the projection when the
subgroup is smooth. Finite type and quasi-compactness here express the
algebraic schemes of the source in the actual scheme category. The source
states its fiber criterion on algebras; the all-test-scheme formulation is
its derived scheme version, also reflected in the isomorphism
`G × H ≅ G ×_Q G` of Proposition 5.24. Proving that extension to all test
schemes is part of the proof obligation.

`ParabolicSubgroupQuotientProperStatement` concerns a connected smooth affine
group `G` and an existing `IsParabolicSubgroup i`. It applies to every single
model `Q,q` satisfying the displayed geometric and fiber conditions, and
asserts that this same `Q` is proper over `k`. The definition of parabolic
used here says that `P` is smooth and closed and contains a Borel subgroup
after base change to the algebraic closure. Properness of a quotient is
therefore a conclusion to prove, not a field of that definition.

This second proposition is derived from Milne, Definition 17.15 and
Theorem 17.16, printed p.356, and Appendix A.75–A.76, printed p.583.
Completeness is properness of the structure morphism. The source's
completeness criterion must be related to the published geometric
`IsParabolicSubgroup`, with the needed quotient comparison, base-change and
descent arguments proved. In particular, the hypotheses on `q` ensure an
fppf quotient presentation; they are not an assumption that `Q` is proper.

The registered original is `milne-2017-algebraic-groups`, SHA-256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`.
The full registered author's errata snapshot
`milne-2017-algebraic-groups-errata-2026-11-02` was read. No entry changes
the results used here. In the printed prose of Proposition 7.15 the arrow
in the smoothness sentence is reversed; the displayed cartesian square
and the explicit specialization to `G → G/H` give the projection direction
used in this statement.

These propositions introduce no replacement for reductivity, no dynamic
parabolic definition and no quotient certificate as a new premise in a
flag-quotient existence theorem. They provide separate general targets whose
proofs would supply actual quotient models and properness. The dynamic
subgroup representation, its identification as parabolic, the opposite
cell, rational-point lifting and algebraic local sections remain separate
obligations.
