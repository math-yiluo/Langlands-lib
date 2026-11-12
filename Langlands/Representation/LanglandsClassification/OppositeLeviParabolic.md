# An actual opposite parabolic with the specified rational Levi

Worker 148. Internal construction for the opposite-parabolic input in
Renard VII.4.2 (i), printed p.243 / PDF p.249. The construction uses published
unconditional algebraic-group proofs, with no local-field, topology,
representation, finite-length or admissibility hypothesis.

For a connected reductive group scheme `G` over an arbitrary field `k`, a
rational parabolic `p : P -> G` and a specified rational Levi `l : M -> P`,
`OppositeLeviParabolicData p l` records an actual parabolic `q : Q -> G`,
the same Levi scheme `M` with an embedding `lQ : M -> Q`, and a specified
geometric unipotent radical `rQ : U -> Q`. Its fields certify parabolicity,
the rational Levi predicate, the radical predicate used by the represented
induction and Jacquet functors, and the isomorphism of Levi-first
multiplication. They also certify the exact ambient equality
`lQ q = l p` and the equality of rational-point subgroups
`P(k) intersect Q(k) = M(k)` in `G(k)`.

`oppositeLeviParabolic` constructs these data. The published parabolic
dynamics and geometric radical theorems supply a single cocharacter `chi`
whose dynamic parabolic is the original `P` and whose dynamic centralizer
is the original embedded `M`. The affine representative of the dynamic
parabolic of the opposite cocharacter is `Q`; its affine unipotent
representative is `U`. Reversing the cocharacter preserves its full
centralizer functor, so the original `M` represents that centralizer and
has a canonical inclusion into `Q`. The canonical unipotent inclusion,
the geometric radical theorem and the represented dynamic multiplication
isomorphism give the radical and Levi certificates. Dynamic parabolic
recognition proves parabolicity. Finally the all-test equality
`P(chi) intersect P(-chi) = Z(chi)` proves the required equality on
rational points.

This is derived internal content: it assembles existing algebraic-group
theorems into the exact actual maps and certificates required by the
representation-theoretic application. Its use of classical choice to select
`chi` makes the data noncanonical. It proves existence, and asserts no
uniqueness of opposite parabolics. It supplies no second adjunction,
identity-support equivalence, regularity, finite-length preservation or
Langlands classification result.

Motivating source: David Renard, *Représentations des groupes réductifs
p-adiques*, version dated 9 July 2026, VII.4.2 (i), printed p.243 / PDF p.249;
registered as `renard-2026-representations-groupes-reductifs-padiques`,
SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
