# The subquotient of a maximal weight of multiplicity one

This module strengthens `Reductive/HighestWeightSubquotientRepresentation`.
That module handles the subquotient `X/Y` of a weight `ν` that dominates every
weight of the ambient representation. Here `ν` only needs to be maximal: no
weight of the representation lies strictly above it. This is the
multiplicity-one maximal-weight case of Tits (*Représentations linéaires
irréductibles d'un groupe réductif sur un corps quelconque*, J. reine angew.
Math. 247 (1971), Proposition 3.4, pp. 204–205), which is the case used in
this development. It is needed to compute Tits classes from representations,
such as exterior powers of the adjoint representation, in which the relevant
weight is maximal but not the largest.

Tits's Proposition 3.4 is more general. He assumes a star-fixed weight of
the dominant lattice with multiplicity one, and allows strictly higher
weights in the ambient representation. His conclusion is an absolutely
simple subquotient containing the weight, whose highest weight is congruent
to the given weight modulo the root lattice. For example, for split `SL₂`
over `ℚ`, the zero weight of `Sym² V` is dominant of multiplicity one while
the highest weight is `2ω`; Proposition 3.4 applies, but the maximality
hypothesis here excludes this case. Under maximality the conclusion here is
sharper: the highest weight of the subquotient equals `ν`.

## Setting

- `p` is a split pinning of a group `H` over a field `F`, and `ρ` is a matrix
  representation of `H`.
- `D : p.HighestSubquotientData ρ ν` gives coordinates for
  `X = highestGenerated ρ ν`, `Y = highestRadical ρ ν` and the subquotient
  representation `D.quot` on `X/Y`.

## Declarations

- `HighestSubquotientData.incl_injective`, `proj_surjective`: the coordinate
  inclusion of `X` is injective and the coordinate projection onto `X/Y` is
  surjective.
- `weightSpace_sub`, `weightSpace_quot`: the weight spaces of the
  subrepresentation map onto `ρ_μ ∩ X`; those of the subquotient are the
  images of those of the subrepresentation.
- `weightSpace_ne_bot`: every weight of the subquotient is a weight of `ρ`.
- `finrank_weightSpace_quot`: if `ρ_ν` is a line, so is the `ν`-weight space
  of the subquotient.
- `isIrreducible`: if `ρ_ν` is a line, the subquotient is irreducible. This
  is the irreducibility half of `HighestSubquotientData.isHighestWeight`,
  extracted with the same proof: a stable subspace of `X/Y` pulls back to a
  stable subspace between `Y` and `X`, which is `Y` or `X` by
  `eq_highestRadical_or_eq_highestGenerated`.
- `isHighestWeight_of_maximal`: suppose `ρ_ν` is a line and `ν` is maximal,
  that is, every weight `μ` of `ρ` with `μ - ν ∈ Q⁺` equals `ν`. Then the
  subquotient has highest weight `ν`.
  1. By the published split classification `splitHighestWeightClassification`
     (part three), the irreducible
     subquotient has a dominant highest weight `ν'`.
  2. `ν` is a weight of the subquotient, so `ν' - ν ∈ Q⁺`.
  3. `ν'` is a weight of the subquotient, hence of `ρ`. Maximality gives
     `ν' = ν`.
- `isDominantWeight_of_maximal`: under the same hypotheses, `ν` is dominant.
  The same argument applies, since `ν'` is dominant.
- `MaximalWeightSubquotientStatement` packages both conclusions for all
  fields, groups, pinnings and representations. `maximalWeightSubquotient`
  proves it, using the published classification.
