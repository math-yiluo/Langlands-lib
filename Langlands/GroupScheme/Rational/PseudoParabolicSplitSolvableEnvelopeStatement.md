# The split solvable envelope used in minimal pseudo-parabolic conjugacy

Author: Worker 274.

`Langlands.GroupScheme.PseudoParabolicSplitSolvableEnvelopeStatement.{u}`
isolates the split solvable subgroup construction at the start of the proof
of Theorem C.2.5 in Conrad–Gabber–Prasad, *Pseudo-reductive groups*, second
edition (2015), printed p.595 (PDF p.621). The registered source is
`conrad-gabber-prasad-2015-pseudo-reductive`, SHA-256
`1b77af44c90211db9a3efa50896a3722f4fd2df332b7ce2ec52202eb243e7f54`.
This file defines a proposition and supplies no construction or proof.

For every smooth connected affine group scheme `G` over any field
`k : Type u`, take an actual pseudo-parabolic inclusion `i : P ⟶ G`,
an actual maximal split torus `s : S.toGrp ⟶ P`, and any actual
representative `j : U ⟶ P` satisfying `IsSplitUnipotentRadical j`.
The conclusion supplies an actual group scheme `H` over `k` and a
homomorphism `h : H ⟶ P` such that:

1. `IsSplitSolvableGroupScheme H`.
2. `h` represents the fppf-local product of `SubgroupFunctor.range s`
   and `SubgroupFunctor.range j` on every relative scheme test.

The first condition includes smoothness, connectedness, affineness and
solvability, together with a finite normal series having represented
fppf quotients that are one-dimensional vector groups or copies of the
multiplicative group over `k`. The second condition includes closedness of
`h`. Its membership equivalence permits a factorization after a flat
surjective locally finitely presented relative cover. In particular, the
all-test images of both `s` and `j` are contained in the image of `h`.
Composing with the closed inclusion `i` gives the actual closed split
solvable subgroup of `G` required by Lemma C.2.2.

The source writes this group as the semidirect product
`H := S ⋉ R_us,k(P)` and states that it is split solvable.
The formal target retains its represented product and split-solvable
properties, which are exactly the properties used in the subsequent
conjugacy argument. It does not assert the additional uniqueness or
universal property of a semidirect-product construction.
It quantifies over every supplied representative of the split radical,
using the existing all-test normality and greatestness predicate.
Existence of that representative is a separate prerequisite, already
expressed by `SplitUnipotentRadicalExistenceStatement`. No radical is
assumed to be equal to the possibly nonsplit unipotent radical in the
pseudo-parabolic definition.

This is a derived interface for the cited construction rather than a new
mathematical assertion about an arbitrary subgroup product. Proving it
requires constructing the product and establishing its actual split
series; merely knowing that each factor is split does not discharge the
target. There is no reductivity, pseudo-reductivity, perfection,
infinitude or characteristic restriction. All objects and relative tests
are in the arbitrary universe `u`.
