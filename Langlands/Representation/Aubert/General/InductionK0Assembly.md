# Finite assembly on actual exact Grothendieck groups

This internal adapter implements the finite rearrangement after Aubert
1995, equation (1.8), on the actual exact finite-length Grothendieck groups.
It is a conditional intermediate construction. It does not prove
`RationalInductionCompatibilityStatement`.

`inducedLeviAlternatingTerm` composes the actual alternating term inside the
closed subgroup `M J` with actual normalized induction from `M J` to `G`.
The internal families are the literal `subgroupOf` restrictions of the
ambient families, at `leviIndex J K`, with labels `Finset J`.
`sum_inducedLeviAlternatingTerm` distributes induction over their signed
sum and identifies the result with induction composed with the published
`leviAlternatingOperator`.

`inducedGeometricTerm` composes the actual `geometricTermK0` with actual
normalized induction from its target Levi. Its definition retains the
actual source and target intersection decompositions and the four visible
finite-length/exactness premises. It supplies no identification of the
source intersection with a standard Levi.

`alternatingOperator_comp_induction_eq_geometricSum` uses the explicit
`GeometricK0ExpansionStatement` input, distributes composition over finite
sums, and obtains the signed sum of induced geometric intersection terms.
This theorem does not prove its geometric-lemma input.

`inductionCompatibility_of_geometricExpansion` additionally takes a
termwise reduction input. This input equates each actual induced
intersection term with the induced restricted-Levi term indexed by the
intrinsic Coxeter intersection subset, read in `J`. The proof applies the
published finite-Coxeter `signedIntersectionSum_eq_sum_subtype` to the
abelian group of integer-linear maps between the actual Grothendieck
groups. The ambient-to-subtype-to-ambient indexing preserves the subset
and its cardinality, so the resulting sum is exactly induction composed
with the literal restricted-Levi operator.

The construction has independent root-label, group and carrier universes.
It allows every standard subset and empty root types. The maps use the
published saturated carrier universe `max uG uV` and all actual
short-exact-sequence relations. No rank sign or new representation family
is introduced.

The unproved inputs remain substantive obligations: actual-root Coxeter
realization, actual intersection decompositions and finite-length
preservation, the actual geometric expansion, and the term reduction
using normalized transitivity and Weyl conjugacy. They are not added to
the rational-point target. This conditional helper supplies no final
evidence for that target before those inputs are proved at its scope.
It uses no classification, character independence, adjointness or
cuspidal-support proof; the geometric lemma appears solely as an explicit
input to the two conditional laws.

Provenance: an internal assembly of the published actual map/operator
constructors and the finite-Coxeter signed-sum theorem, motivated by
registered source `aubert-1995-duality`, printed pp.2181–2182, especially
equation (1.8) and its subsequent regrouping. Aubert Proposition 3.2 is
not used.
