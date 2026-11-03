# Some Borel has proper homogeneous quotients

Workers 1334, 1293 and 898. The statement and common-interface design reuse
the draft of Workers 1293 and 898.

`Langlands.GroupScheme.SomeBorelQuotientProperStatement.{u}` is a
proposition-valued definition. For every algebraically closed field
`k : Type u` and actual group scheme `G` over `S = Spec (CommRingCat.of k)`
with `Smooth G.X.hom`, `IsAffineHom G.X.hom` and
`ConnectedSpace G.X.left`, it asks for an actual group scheme `B` and
homomorphism `i : B ⟶ G` satisfying the existing `IsBorelSubgroup i`,
together with the following property.

For every supplied `Q : Over S` and `q : G.X ⟶ Q`, assume:

- `IsSeparated Q.hom`, `LocallyOfFiniteType Q.hom` and
  `QuasiCompact Q.hom`;
- `Smooth q.left`, `Surjective q.left` and `QuasiCompact q.left`;
- for every `T : Over S` and `g h : T ⟶ G.X`,
  `g ≫ q = h ≫ q ↔ g⁻¹ * h ∈ (SubgroupFunctor.range i).carrier T`.

The conclusion is `IsProper Q.hom` for that same supplied `Q`. These are
exactly the quotient-model conditions of the existing
`SmoothSubgroupQuotientExistenceStatement`. The last condition uses right
cosets `gB` and quantifies over all relative test schemes, including
nonaffine and nonreduced tests. The same chosen embedding `i` is used for
every model. The existing `IsBorelSubgroup` includes closed immersion,
smoothness, connectedness, solvability and maximality; it is unchanged.
The universe and characteristic are arbitrary, and no reductivity
hypothesis is imposed.

The proposition chooses some Borel with this property. Existence of a
quotient is the separate `SmoothSubgroupQuotientExistenceStatement`
target. This file supplies no proof of either proposition.

The source is J. S. Milne, *Algebraic Groups: The Theory of Group Schemes
of Finite Type over a Field* (2017), registered as
`milne-2017-algebraic-groups`, SHA256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`.
Section 17b assumes a connected group variety over an algebraically closed
field. Definition 17.6 and its following remark, printed pp.353–354
(one-based PDF369–370), give Borels and existence by largest dimension.
Theorem 17.9(a) and its proof, printed p.354 (PDF370), give the relevant
flag-orbit route: choose a Borel of maximum dimension, realize it as a line
stabilizer using 4.27, and use Lie–Kolchin 16.30 to obtain a maximal flag
with that stabilizer. The dimension argument and 1.66 make its orbit
closed; flag completeness from 7.29–7.30 then yields a complete quotient.
Inclusion maximality alone does not justify this minimum-orbit-dimension
step. The proposed route must retain a largest-dimension witness or prove
an adequate replacement.

This universal-model interface is derived from that argument, rather than
a verbatim sentence of the original. The route uses the
maximum-dimension part of the proof before its subsequent conjugacy
argument. Formalizing flag geometry and the orbit construction remains
necessary. For a possibly nonreduced flag stabilizer, the finite map from
the quotient by its reduced identity component to the orbit, and transfer
of properness along that map, remain actual proof obligations. Relating a
constructed quotient to every supplied `Q` also requires the effective
quotient-sheaf comparison and transport of properness along the resulting
isomorphism.

The complete registered official errata snapshot
`milne-2017-algebraic-groups-errata-2026-11-02` was read; it lists no
correction to 17.9. This statement proves no Borel existence, conjugacy,
quotient existence, comparison or properness theorem. The general Borel
and parabolic quotient targets remain separate; field and properness
descent for the latter remain proof obligations.
