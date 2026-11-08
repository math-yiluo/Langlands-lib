# Hom bounds on the unitary Jacquet module from a supplied gluing

Author: Worker 1597. This is internal derived support for the generic
irreducibility argument of Waldspurger, *La formule de Plancherel pour les
groupes p-adiques d'après Harish-Chandra*, 2003, III.7.3 (printed p.276), and
its multiplicity count via the unitary geometric filtration of III.3.3
(printed p.268). The construction combines two published Library interfaces:
`exists_leviUnitaryJacquetInductionFiltration_of_isGluedFrom` from
`LeviUnitaryFiltration` and `HomSpace.length_le_sum` from
`Filtration.HomBounds`.

`sum_le_one_of_le_one_of_unique` is elementary. A finite sum in `ℕ∞` is at most
one if every term is at most one and at most one term is nonzero.

`eq_of_doubleCoset_representative_mem` concerns an equivalence
`c : Fin m ≃ H \ X / K` and representatives `z i` with
`DoubleCoset.mk H K (z i) = c i`. If two representatives lie in `H`, both
double cosets equal the double coset of `1`, so injectivity of `c` makes the
indices equal.

`selectedPieceHomLength` records, for supplied functors `pieces`, a
representation `ρ` of `M(F)` and a target representation `τ` of `L(F)`, the
module length over `ℂ` of the space of intertwiners. The source is the
zero-normalized-real-part selected part of `(pieces i).obj ρ` for the split
component `aL` of `L`. This is exactly the selected part used by
`exists_leviUnitaryJacquetInductionFiltration_of_isGluedFrom`.

`leviUnitaryJacquetInductionHomLength_le_one_of_isGluedFrom` takes four
inputs:

- a supplied `IsGluedFrom` witness for the published
  `leviJacquetInductionFunctor` with the given pieces;
- admissibility of its value at `ρ`;
- a bound of at most one on every selected-piece Hom length;
- the condition that at most one selected-piece Hom length is nonzero.

From these it proves that the Hom length from the actual
`leviUnitaryJacquetModule` of the actual induction of `ρ` into `τ` is at most
one. The proof takes the published unitary filtration and its permutation `e`.
`HomSpace.length_le_sum` bounds the length by the sum over the actual grades.
Each grade is equivalent to the selected part of piece `e i`, so
`HomSpace.length_congr_left` rewrites the summands. `Equiv.sum_comp` then
removes the permutation, and the elementary sum bound finishes the proof.

`leviUnitaryJacquetInductionHomRank_le_one_of_isGluedFrom` restates this bound
for `Module.rank`, using Mathlib's `Module.length_eq_rank` and
`Cardinal.toENat_le_one`.

`leviUnitaryJacquetInductionHomRank_le_one_of_doubleCosets` uses the output
shape of the published `RepresentedGeometricLemmaStatement`. It takes an
enumeration `c` of the actual double cosets `P(F) \ G(F) / Q(F)`,
representatives `z`, intersection data `D` and the gluing by the pieces
`(D i).pieceFunctor`. Its per-piece hypotheses are that every selected-piece
Hom length is at most one, and that it is nonzero only when `z i` lies in the
point image of `P`. The double-coset lemma supplies the uniqueness condition.

The field universe `u`, the inducing carrier universe `v` and the target
carrier universe `w` are independent. The two parabolic triples are arbitrary;
they are not assumed equal. All inputs are explicit:

- the gluing witness;
- admissibility of the Jacquet-induction value;
- both per-piece conditions.

This file does not prove the geometric lemma or any admissibility. It also does
not identify any selected piece with an induced unitary piece or bound its Hom
length. It does not use square-integrability, temperedness, normalizer
regularity or irreducibility.
