# Exact semigroup products and actual relative-root radical products

This file states three unproved targets, in an arbitrary universe and over any
field. The final target uses the actual all-test `Dynamic.unipotent` functor
and the intrinsic root functors from `Rational.RootSubgroup`. Existence of
representatives is a conclusion.

The main original source is Conrad–Gabber–Prasad, *Pseudo-reductive Groups*,
second edition (2015), registered as
`conrad-gabber-prasad-2015-pseudo-reductive`, Theorem 3.3.11 and its proof
(printed pp.114–116; PDF pp.140–142). Kaletha–Prasad, *Bruhat–Tits Theory:
A New Approach* (2023), registered as
`kaletha-prasad-2023-bruhat-tits-new-approach`, Theorem 2.11.15 (printed
p.135; PDF p.166), gives a stronger sufficient hypothesis. Its general-field
root-group structure is in section 2.6.8 (printed p.95; PDF p.126), before the
quasi-split assumption 2.6.10. The registered 1 November 2024 corrections,
PDF p.25, change section 2.11 notation without changing these product passages.

`SemigroupOrderedProductStatement` retains exactly CGP's disjoint partition
of the actual action weights, including zero when it occurs. For each pair
of distinct blocks it requires

\[
\Psi_i\cap\langle\Psi_j\rangle=\varnothing.
\]

Here the brackets mean positive additive semigroup generation:
`AddSubsemigroup.closure`, without inserting zero. The target does not
require the generated semigroups themselves to be pairwise disjoint. The
stronger hypothesis printed in KP implies CGP's hypothesis, but does not
replace it in this target. Smoothness, connectedness, affineness, solvability
and a split acting torus are retained. Solvability is the uniform all-test
derived-series predicate in `WeightSemigroup`; its meaning in this smooth
connected affine setting is explained there.

The conclusion supplies smooth connected closed representatives of the actual
generated semigroup functors and requires the ordered multiplication morphism
to be an isomorphism in the category of schemes over the field. It does not
claim that multiplication is a group homomorphism. The actual map is
`RelativeRoot.orderedMultiplication`: the projections followed by their
inclusions, multiplied in `Fin n` order. Every ordering is covered by the
universal choice of the indexed partition.

The remaining targets specialize the same method to connected reductive groups
and a maximal split torus, retaining non-split groups and nonreduced relative
root systems. `indivisibleRoots i` consists of actual relative roots which
cannot be written as `m • b`, for another actual root b and an integer m≥2.
This is indivisibility within the root set; it does not require a primitive
character in the full character lattice. `indivisiblePositiveRoots i ν`
selects those having strictly positive pairing with the cocharacter ν.

`RelativeRootRayDecompositionStatement` requires a finite enumeration of this
set, disjointness of the positive integral semigroups of distinct indexing
roots, and that an actual root is positive exactly when it belongs to one
of these rays. These are derived root-system consequences of KP sections
2.6.2 and 2.6.7 (printed pp.93–95; PDF pp.124–126); the target assumes no
root-system realization or finiteness conclusion. The rays may contain
characters that are not roots, so the last equivalence quantifies only over
actual roots.

`DynamicRootOrderedProductStatement` says that every enumeration without
repetition of the indivisible positive actual roots gives an ordered
multiplication isomorphism onto a smooth connected closed split-unipotent
representative of the actual Dynamic radical. More precisely, the supplied
scheme isomorphism e satisfies

\[
e.\mathrm{hom}\mathbin{\gg}j_U=\operatorname{orderedMultiplication}(j).
\]

The target also supplies smooth connected closed split-unipotent
representatives of every factor. Thus equality with the Dynamic functor
holds on every test scheme, and the product is a scheme isomorphism over k.
For a multipliable indivisible root a, the factor is the full U_a, with
U_{2a} retained inside it as in the structural target. No extra factor is
inserted for 2a. The empty index set is permitted.

This last target is a derived application of CGP Theorem 3.3.11 to the
unipotent Dynamic subgroup, using its actual weight halfspace comparison,
the relative-root ray decomposition, and the root-group realization and
uniqueness targets. CGP Corollary 3.3.12 (printed p.116; PDF p.142) explains
the same method in its pseudo-split setting; the present target uses the
general relative roots of KP section 2.6.8 and does not impose the
pseudo-split hypothesis from that corollary. Every cocharacter is allowed,
including zero and nongeneric cocharacters used in semistandard settings.

`RootProductStatement` is the conjunction of these three targets. This file
publishes statements and indexing predicates; it proves none of the
substantive product or realization assertions.
