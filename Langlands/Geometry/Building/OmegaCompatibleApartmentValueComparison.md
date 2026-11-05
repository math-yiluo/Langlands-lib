# Valuation values from equivariant affine apartment comparisons

This internal comparison lemma implements the rank-one identification step of
Kaletha–Prasad, *Bruhat–Tits theory: a new approach* (2023), Proposition 6.2.6,
printed p.216 (PDF p.247), using the actual reflection action of Proposition
6.2.1. It does not prove existence of opposite factor pairs or equality of
apartment classes. The registered 2024 corrections, Chapter 4 pp.28–29 and
Chapter 6 p.32, leave this rank-one identification unchanged.

`ValuationBuildingData.rootForm_reflectionElement_vsub` assumes a nonidentity
rational point `g` in an actual relative-root subgroup and a supplied actual
opposite factor pair. For every apartment point `x`, it proves

`rootForm α (m(g) • x -ᵥ x) = -2 * reflectionFunctional α g x`.

The implemented proof substitutes the published affine-reflection action of
the pair, whose displacement is the negative value of the functional times
the pair coroot, and applies the published equality that the root takes value
two on that coroot. No additional apartment axiom is used.

`KPApartmentData.value_eq_of_equivariant_affineEquiv_of_oppositeFactorPair`
compares two actual apartment classes over a nonarchimedean local field in
arbitrary universe `u`. The hypotheses are connected reductivity, an actual
maximal split torus with monomorphic inclusion, a common actual centralizer,
full omega compatibility of both classes, and an affine equivalence with
identity derivative intertwining their original normalizer actions. For each
nonidentity point of an actual root subgroup with a supplied opposite factor
pair, it proves that the equivalence preserves the original valuation value.

The two classes are bundled separately as `ValuationBuildingData`. The affine
equivalence preserves their normalizer displacements because its derivative
is the identity. Applying the same root to those equal displacements and
using the preceding lemma gives equality of twice the two real functional
values. Cancelling the nonzero real scalar gives equality of the functionals;
their published evaluation theorem then identifies the original values in
`WithTop ℝ`. This proof uses no AS 5, V 7, Tits-system premise or assumed
apartment-uniqueness proposition. Pair existence remains explicit.

`OmegaCompatibleApartmentValueComparisonStatement` is the `Prop`-valued
statement definition quantifying the displayed value-preservation assertion
over all the data and hypotheses above in arbitrary universe `u`.
`omegaCompatibleApartmentValueComparison` proves it by introducing those
data and applying the pointwise comparison theorem. This statement and its
supporting proofs are an intermediate unit; they do not prove the unconditional
apartment-class uniqueness target.
