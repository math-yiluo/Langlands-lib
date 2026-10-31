# Association preserves the factors of cuspidal induction

Author: Worker 242.

`Langlands.CuspidalSupport.associatedCuspidalInductionFactorsTheorem` proves
the published `AssociatedCuspidalInductionFactorsTheorem.{uF,uV,uW}` from
`AssociationForwardStatement`. The field universe and the two inducing
carrier universes are independent. The theorem has the exact target type and
introduces no additional hypotheses.

For every prime, actual finite p-adic extension, compatible topological data
and positive rank, take two block shapes and irreducible smooth
Levi-cuspidal representations of their standard Levis that are associated
(`RepresentationsAssociated`: some permutation conjugates the source Levi onto
the target Levi, and the transported source representation is equivalent to
the target representation). Then their canonical normalized inductions have
the same Jordan–Hölder factors in the sense of the published
`HaveSameJordanHolderFactors`: actual finite composition series and a
permutation matching their irreducible quotient representations by actual
equivalences. Multiplicities are retained. The block count is arbitrary.

## Proof

After introducing the prime, field, topological data, rank and positivity,
the proof applies the published reduction
`associatedCuspidalInductionFactors_of_adjacent` from `AssociationReduction`.
Its four theorem inputs are discharged by published proofs:

- `adjacentBlockSwapCuspidalInductionFactorsTheorem.{uF,uV,uV}` and
  `adjacentBlockSwapCuspidalInductionFactorsTheorem.{uF,uV,uW}` from
  `AdjacentSwapProof`, specialized to the fixed prime, field, topological
  data, rank and positivity, supply the adjacent block-swap step with target
  carrier universe `uV` and `uW` respectively.
- `haveSameJordanHolderFactors_trans` from `JordanHolderComparisonProof`, at
  the field `ℂ` and the group `GeneralLinear n F.Carrier`, supplies
  transitivity of factor matching for the two universe patterns the reduction
  needs: all three representations in `max uF uV`, and the last one in
  `max uF uW`.

The imported reduction proceeds as follows. If the source has fewer than two
blocks, both inductions are irreducible and are compared directly
(`associatedCuspidalInductionFactors_of_length_lt_two`). Otherwise the
associating permutation is written as a minimal conjugating representative
`v` times an element of the source block Weyl group, which changes the
transported source representation only up to equivalence. Let `e` be the
block permutation induced by `v`. By induction over products of adjacent
block transpositions (`factors_of_blockMap`), the adjacent step at target
carrier universe `uV` and transitivity in `max uF uV` give factor matching for
every block permutation, with targets in the source carrier universe.
Writing `e` as `(e * s₀) * s₀` for the first adjacent transposition `s₀`, one
last adjacent step (`factors_step`) at target carrier universe `uW`, with the
mixed transitivity, reaches the given target representation.

The proof assumes neither `CuspidalInductionAssociationTheorem` nor any
finite-length, admissibility or existence-of-series hypothesis beyond the
target statement. The target statement pair and its imported pairs are
unchanged.

## Provenance

This is an internal deduction from three published modules and introduces no
new construction or literature transcription. It is the arbitrary-rank part of
Bernstein–Zelevinsky, *Induced representations of reductive p-adic groups I*
(1977), Theorem 2.9(a), implication (i) to (iii), printed page 448/PDF page 9,
whose proof passes through elementary maps in section 2.16(2) and identifies
them with adjacent block transpositions for general linear groups in
section 2.17, printed page 450/PDF page 11. Registered source:
`bernstein-zelevinsky-1977-induced-i`, SHA-256
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`. As in
the source, the general case is reduced to adjacent steps chained by
transitivity of factor equality.
