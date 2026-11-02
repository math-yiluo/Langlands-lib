# Source semigroup realization, cyclic filtration and dynamic comparisons

These are unproved, arbitrary-universe targets over any field k for a smooth
affine k-group G with an actual action of a split k-torus S. G need not be
connected except in the final dynamic halfspace comparison. No hypothesis
requires a realization of the constructed semigroup functor.

The normative source is Conrad–Gabber–Prasad, *Pseudo-reductive Groups*,
second edition (2015), registered as
`conrad-gabber-prasad-2015-pseudo-reductive`, Proposition 3.3.6 and Lemma 3.3.8
with their proofs (printed pp.109–112; PDF pp.135–138), together with the
commutator bound of Proposition 3.3.5 (printed p.109; PDF p.135). Related
statements are KP Propositions 2.11.12–14 (printed p.135; PDF p.166), registered
as `kaletha-prasad-2023-bruhat-tits-new-approach`. The dynamic comparison uses
their Propositions 2.11.1–3 (printed pp.130–132; PDF pp.161–163), and the
weight-characterization and uniqueness of CGP Proposition 3.3.6. The registered
1 November 2024 KP corrections, PDF p.25, repair dynamic notation without
altering these hypotheses or conclusions.

`ActionWeightComparisonStatement` is the internal comparison obligation:
the span used to define the actual-action weight space is exactly its
intrinsic eigenset, and for conjugation it is the Library's original adjoint
weight space. All coefficient algebras and actual dual-number points are
retained in both formulations. This target avoids substituting a chosen
representation or k-point action for the source torus action.

`SemigroupRealizationStatement` concerns the actual generated functor of
`WeightSemigroup`, for any additive subsemigroup A of X*(S), including the
empty one and those containing zero. It requires a smooth connected closed
representative, stability under S, the exact sum of the A-weight spaces as
Lie image, and the source maximality equivalence: a smooth connected
invariant closed subgroup F has all weights in A if and only if F is
contained in the constructed functor. A second clause states uniqueness
among subgroups with that exact Lie image. If zero is absent from A, each
representative is unipotent and has a finite Ga-series over k. This is the
split-unipotence conclusion of CGP Lemma 3.3.8, in addition to the unipotence
assertion of Proposition 3.3.6.

`SemigroupCommutatorStatement` puts every test-scheme commutator of the
A- and A'-subgroups in the subgroup for A+A'. `semigroupSum` is literal
addition of one element from each semigroup; it does not insert zero or
replace this condition with an unrelated closure.

`CyclicWeightFiltrationStatement` uses the tail A_r={n·a : n≥r} for r≥1
and a nonzero. It requires normality of each actual tail functor in the
first, and a represented fppf quotient of each tail by the next. The quotient
admits natural vector coordinates for which S acts by the single actual
character r·a. Such coordinates determine one scalar-multiplication structure:
for any two compatible coordinate systems, pulling back multiplication by
any global scalar c on any test scheme gives the same point. Thus the
statement asserts uniqueness of the equivariant linear structure, not of a
basis. The quotient action and the action on each represented tail must
intertwine the original action and quotient map on every test.

The tail A_r is deliberately distinct from the cyclic semigroup generated
by r·a. For example, A₂ can contain 3a even though 3a is not a positive
integral multiple of 2a. The quotient is an fppf sheaf quotient, using
`IsFppfQuotient` from `RootSubgroupStructureStatement`; no equality between
its T-points and a point-group quotient is asserted.

`CyclicRootFunctorComparisonStatement` identifies the first cyclic tail
under conjugation with the already constructed intrinsic character-orbit
functor Uₐ, for every nonzero character of the split torus. This is the
cyclic construction in the proof of CGP Proposition 3.3.6, with the
implementation-specific intrinsic/descended-action comparison made explicit.

`DynamicSemigroupComparisonStatement` identifies the actual Dynamic
parabolic, centralizer and identity-limit functors with the constructed
semigroup functors for respectively nonnegative, zero and positive character
pairing with an arbitrary cocharacter ν in S. It assumes G smooth, affine
and connected, and S split, and requires no genericity, positivity chamber,
standard-subset presentation, or reductivity. In particular it supports
semistandard cocharacters in the connected reductive specialization. These
are equalities of subgroup functors on all schemes over k.

`WeightSemigroupStatement` is the conjunction of the six focused targets.
The file adds exact statements and supporting predicates, with no proof of
these substantive source or comparison conclusions.
