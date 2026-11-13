# Maximal p-subgroups over finite fields

Worker 302 isolates the finite reductive-group prerequisite used in the
proof of Kaletha–Prasad Proposition 13.5.2. This pair states a proposition;
it does not prove it.

`FiniteFieldSylowBorelStatement` ranges over every finite field `k` and
every connected reductive `k`-group `G`, at arbitrary universe `u`. Put
`p = ringChar k`. A subgroup `H` of the actual rational-point group `G(k)`
is a maximal `p`-subgroup precisely when there are a field-defined geometric
Borel subgroup `i : B ⟶ G` and its represented ground-field unipotent radical
`j : U ⟶ B` such that

`H = (rationalPoints.map (j ≫ i)).range`.

Maximality is expressed explicitly as `IsPGroup p H` together with
equality of every `p`-subgroup containing `H`. In this finite setting it
is the usual Sylow condition. The image is the range of the map on actual
`k`-points. There is no assumption that points of an arbitrary scheme
quotient lift.

The predicates `IsGeometricBorelSubgroup` and `IsUnipotentRadical` are the
existing Library predicates. The former requires the smooth connected
solvable closed subgroup to be maximal both over `k` and after base change
to an algebraic closure of `k`. Ground-field maximality alone would allow
an anisotropic maximal torus in a split rank-one group and would make
the reverse implication false. The latter predicate specifies a smooth
connected normal unipotent closed subgroup greatest under containment
of its images on all test schemes. The statement quantifies over
representatives, so it makes no choice of a radical.

The provenance is derived from the finite-field step in the proof of
Kaletha–Prasad Proposition 13.5.2, printed p.477 / PDF p.508. There the
maximal `p`-subgroup in a connected reductive residue group is identified
with the points of a Borel unipotent radical. The Library theorem
`finiteFieldQuasiSplit` already supplies a field-defined geometric Borel
for any connected reductive group over a finite field. The present formulation records the
two directions of this standard finite-field classification independently
of any building, integral model or pro-`p` topology. It is not asserted
to be a separately numbered theorem in KP.

The 1 November 2024 corrections, PDF p.49, replace the ambient local group
in Proposition 13.5.2(1) by its zero subgroup. This does not alter the
finite-field classification isolated here. Proving this statement and
applying it to the supplied reductive quotient remain separate
obligations.
