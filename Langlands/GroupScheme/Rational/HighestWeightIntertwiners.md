# Intertwiners, weight spaces and the positive-root order

Author: Worker 900.

This module collects elementary facts about actual intertwiners
(`MatrixRepresentation.Intertwines`, module `Lie.RepresentationSubquotient`) and
the highest-weight predicate `SplitPinning.IsHighestWeight` (module
`Rational.FundamentalRepresentations`). They are used in the classification of
simple representations by highest weight.

## Inverse intertwiners

- `MatrixRepresentation.exists_mul_eq_one_of_bijective`: a matrix `C : Matrix m n k`
  whose linear map is bijective has a two-sided inverse `N` with `N * C = 1` and
  `C * N = 1`. `N` is the matrix of the inverse linear equivalence.
- `MatrixRepresentation.Intertwines.exists_inverse`: if `C` intertwines `ρ` with `σ`
  and is bijective, there is a bijective `N` that intertwines `σ` with `ρ`. The
  intertwining property comes from the Library's `Intertwines.of_mul_eq_one`, and
  bijectivity from the two inverse equations.

## Weight spaces under intertwiners

- `SplitPinning.mulVec_mem_representationWeightSpace`: an intertwiner maps the
  weight space of `ρ` at `μ` into the weight space of `σ` at `μ`. The proof restricts
  the intertwiner to the torus and checks the character equation on every affine
  test with `mem_characterSpace_iff_affine`.
- `SplitPinning.finrank_representationWeightSpace_le_of_intertwines`: for an
  injective intertwiner, `finrank` of the weight spaces can only increase.
- `SplitPinning.finrank_representationWeightSpace_eq_of_intertwines` and
  `SplitPinning.representationWeightSpace_ne_bot_iff_of_intertwines`: a bijective
  intertwiner, together with its inverse intertwiner, preserves weight
  multiplicities and the set of occurring weights.
- `SplitPinning.IsHighestWeight.of_intertwines`: if `ρ` has highest weight `lam` and
  `C` is a bijective intertwiner from `ρ` to `σ`, then `σ` has highest weight `lam`.
  The four components of `IsHighestWeight` are obtained as follows:
  - irreducibility from `Intertwines.isIrreducible_of_bijective`;
  - spanning by weight spaces from `iSup_representationWeightSpace_eq_top`, which
    holds for every representation;
  - the multiplicity-one condition from the equality of multiplicities;
  - the weight bound from the equality of the occurring weights.

## The positive-root order

- `SplitPinning.latticePairing_positiveCocharacter_of_mem_positiveRootMonoid`: on
  `p.positiveRootMonoid`, the pairing with `p.positiveCocharacter` is nonnegative and
  vanishes only at `0`. This is proved by closure induction. On a simple root the
  pairing is positive by `latticePairing_root_positiveCocharacter_pos_iff`, because
  simple roots have height one.
- `SplitPinning.eq_of_sub_mem_positiveRootMonoid`: if `lam - mu` and `mu - lam` both
  lie in `p.positiveRootMonoid`, then `lam = mu`. Their pairings with the positive
  cocharacter are negatives of each other and both nonnegative, so both vanish.

## Highest weights are dominant and unique

- `SplitPinning.IsHighestWeight.isDominantWeight`: a highest weight is dominant. Fix a
  simple root `a`. By `finrank_representationWeightSpace_simpleReflection` (module
  `Rational.PathFundamentalWeights`), the weight space at the reflection `s_a lam`
  has the same dimension as the one at `lam`, namely one. So `s_a lam` occurs, and
  hence `lam - s_a lam = ⟨lam, a∨⟩ a` lies in the positive-root monoid. Pairing with
  the positive cocharacter, which is positive on `a`, gives `⟨lam, a∨⟩ ≥ 0`.
- `SplitPinning.IsHighestWeight.eq`: two highest weights `lam` and `mu` of the same
  representation are equal. Both weight spaces are nonzero, so each weight lies below
  the other, and the order is antisymmetric.

## Provenance

These are internal lemmas. Dominance and uniqueness of the highest weight correspond
to Milne, *Algebraic Groups* (2017, registered as `milne-2017-algebraic-groups`),
Proposition 22.17 and 22.3 (printed pp. 464–467). Milne obtains dominance from the
weights of a simple representation being stable under the Weyl group. The Lean proof
uses only the simple reflections.
