# Borel maximality from a proper solvable homogeneous quotient

Authors: Worker 1438 and Worker 1293.

`ProperSolvableQuotientBorelStatement.{u}` states the implication from a
proper solvable homogeneous quotient to Borel maximality. The module also
proves a reduction to the separately stated
`SolvableProperFixedPointStatement.{u}`. It does not prove either proposition
unconditionally.

## Statement and actual quotient

The universe is arbitrary. The field `k` is algebraically closed, and `G` is
a smooth connected affine group scheme over `Spec k`. The map `i : H ⟶ G`
is a closed immersion, and `H` is smooth, connected and solvable in the
published sense. In particular, solvability means solvability of the group
of geometric points over `AlgebraicClosure k`.

The quotient is an actual scheme `Q` over `Spec k`, with an actual map
`q : G.X ⟶ Q`. The structure map of `Q` is proper. The map `q` is smooth,
surjective and quasi-compact. On every test scheme `T`, including
nonreduced and non-affine schemes, the equality `g ≫ q = h ≫ q` is
equivalent to membership of `g⁻¹ * h` in `SubgroupFunctor.range i`.
These are the usual right-coset fibers. Pointwise surjectivity on every
test scheme is not assumed.

The conclusion is the unchanged `IsBorelSubgroup i`. Its maximality
quantifies over every smooth connected solvable closed subgroup of `G`
through which `i` factors, and requires the factor to be an isomorphism.
No reductivity, splitting, characteristic or cocharacter hypothesis
appears in this general criterion. Existence of a quotient is not asserted.

## Implemented reduction

`IsBorelSubgroup.of_fixedQuotientPoint` takes an existing Borel `b : B ⟶ G`,
the smooth connected solvable closed subgroup `i : H ⟶ G`, an actual
quotient with the stated all-test fibers, and a scheme action of `G` on `Q`
whose action on lifted cosets is left multiplication. Here only local
finite type and surjectivity of `q` are needed. A supplied rational point
of `Q` fixed by `B` is lifted to a rational point `g` of `G`, using the
published rational lifting result over an algebraically closed field.
All-test fixedness and the exact fibers give the actual factorization
of the conjugate of `B` by `g⁻¹` through `H`, via
`factorOfFixedCoset`. Conjugation preserves the Borel property. Its
maximality makes the factor an isomorphism, since `H` is smooth,
connected and solvable. Transport along this source isomorphism proves
that `i` is Borel. This adapts the published
`Absolute/BorelFixedPointConjugacy` construction to a target whose Borel
maximality is a conclusion.

`properSolvableQuotientBorel_of_solvableProperFixedPoint` chooses a Borel
of `G` using the published prime-kernel-height existence theorem. It
constructs the actual scheme action on the supplied quotient using
`Dynamic.flagQuotientSchemeAction`, which descends along the smooth
surjective quasi-compact map. The quotient is nonempty because `G` is
connected and hence nonempty. The supplied general solvable fixed-point
theorem applied to the chosen Borel gives a fixed rational quotient point.
The preceding lemma then proves the criterion. The general fixed-point
theorem remains an explicit, undischarged premise of this reduction.

## Source and provenance

J. S. Milne, *Algebraic Groups* (2017), Proposition 17.19, printed p.357,
zero-based PDF page 372 (one-based PDF page 373), gives the equivalence
between a connected subgroup being Borel and its being solvable with
complete quotient. Registered source: `milne-2017-algebraic-groups`,
SHA-256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`.
The official errata snapshot
`milne-2017-algebraic-groups-errata-2026-11-02` has been read and contains
no correction to Proposition 17.19.

The proposition here is the implication (b) to (a), expressed for smooth
affine group schemes and a supplied actual smooth homogeneous quotient.
Over an algebraically closed field, smooth group schemes give group
varieties, and properness is the scheme form of completeness. The
explicit quotient morphism and its all-test fibers replace the source's
notation `G/H`. The implemented conditional proof uses the fixed-point
theorem and the existing scheme constructions directly, without using
parabolic containment or Borel conjugacy as a premise. Worker 1293
contributed the fixed-point reduction plan; Worker 1438 implemented it.

Applying this criterion to a cocharacter centralizer still requires a
proper quotient, as well as smoothness, connectedness and solvability of
the relevant subgroup. No centralizer intersection theorem follows from
this module alone.
