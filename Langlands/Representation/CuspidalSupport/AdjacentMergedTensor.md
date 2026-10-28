# Actual merged tensors for an adjacent block swap

This is an internal construction prerequisite for the adjacent cuspidal
induction-factor comparison. It constructs both actual inner tensors and both
induction-in-stages equivalences. It proves no Jordan–Hölder matching assertion.
The entry is `Langlands.CuspidalSupport.adjacentReverseTensorStagesEquiv`.

Fix a block shape `B` of rank `n` and `j + 1 < B.length`. Write `D` for
`B.adjacentMerge j hj`, `S` for `B.adjacentRefinement j hj`, and `e` for
`B.adjacentBlockEquiv j hj`. Thus `e` identifies the consecutive outer and
inner block labels with the labels of `B`. The inner shape has length two at
the merged slot and length one elsewhere.

## Reversed labels and exact coordinates

`BlockShape.adjacentBlockEquiv_rev` proves

```text
e (m, Fin.rev k) = B.adjacentSwap j hj (e (m,k)).
```

The proof uses the published value formula for `e`, the value of `Fin.rev`,
and the two possible inner lengths. It splits according to whether the original
label is either swapped label and closes the resulting natural-number
identities with arithmetic. It expresses these arithmetic facts without
rewriting the dependent types of the labels.

`BlockShape.adjacentReverseRefinement` defines `R m := (S m).permute Fin.revPerm`
as a refinement of the same `D`. The size law `adjacentReverse_size` follows
by applying `B.size` to the label identity. In particular its right-hand side
is the size in `B.permute (B.adjacentSwap j hj)` at the consecutive label `e (m,k)`.
`adjacentReverse_index` applies the published `index_index_eq_of_lex` to that
size law and to `adjacentBlockEquiv_lt_iff`. It gives equality of the actual
standard coordinate indices, including the required `Fin.cast` on the inner
coordinate. No identification of shapes from their cardinalities is assumed.

## Actual tensor objects and their transports

Let `F` be any supplied `p`-adic field with topological data `T`. The field
universe `uF` and original factor-carrier universe `uV` are independent. Given
actual supercuspidal representations `A i` on the blocks of `B`,
`adjacentInnerTensor F T B j hj A m` is `FiniteTensor.externalSmoothObject`
of the factors `A (e (m,k))`. The corresponding `adjacentReverseTensor` uses
`A (e (m, Fin.rev k))`. Their groups are the actual Levis of `S m` and `R m`.
Their ranks agree definitionally with the ranks in the factor types.

`adjacentReverseTensorFactors_eq` identifies the target family produced by
`orderedRefinementTensorFactors` with this actual reversed family. This is an
equality of bundled smooth objects, including their carriers and actions.
The private `family_rankCast_eq` proves, by equality elimination, that a
rank-transported member of a dependent family is the member at the equal label.
Applying it to the reversed-label identity supplies the factorwise equality;
function extensionality and congruence of `externalSmoothObject` supply the
equality of inner families.

`adjacentInnerTensors_cuspidal` applies the published `glCuspidalTensor` twice
at each positive merged-block rank. It proves that both displayed tensors are
irreducible and Levi-cuspidal; the latter predicate also retains admissibility.
`adjacentInnerTensorTransportEquiv` applies the published
`blockPermutationTensorEquiv` to `Fin.revPerm`. Its source is the actual
`transport` along the canonical inner block permutation, with actual
`conjugatesLevi_blockPermutation`; its target is the reversed inner tensor.

## Both induction-in-stages equivalences

`adjacentTensorOuterInduced` names outer normalized induction from the external
tensor of the normalized inductions of the source inner objects.
`adjacentReverseTensorOuterInduced` names the analogous action for the reversed
objects. Both use `RefinedInductionTensor.externalRepresentation`, so their
inner carriers are the actual normalized induced-function spaces, rather than
arbitrary representations of the same ranks.

`adjacentTensorStagesEquiv` specializes the published
`orderedRefinementTensorInductionEquiv` with `D`, `S`, `e`,
`adjacentBlock_size`, and `adjacent_index`. Its source is the normalized product
of the original `A i`. Its target is definitionally
`adjacentTensorOuterInduced`: the source rank equalities are reflexive, so
`orderedRefinementTensorFactors` is definitionally `adjacentInnerTensor`.

The entry `adjacentReverseTensorStagesEquiv` specializes the same published
equivalence to the swapped global shape, `D`, `R`, `e`,
`adjacentReverse_size`, and `adjacentReverse_index`. Its source is the
normalized product on `B.permute (B.adjacentSwap j hj)` of the factors
`A (B.adjacentSwap j hj i)`. Its target is definitionally
`adjacentReverseTensorOuterInduced`. The private `stagesFactorsCast` transports
the generic equivalence along `adjacentReverseTensorFactors_eq`. This helper
retains the source module structures from its input equivalence and proves the
transport by equality elimination. Inferred definition types avoid repeated
elaboration of the large induced carriers; they do not alter the comparison.

The construction uses the published algebraic and normalized-induction
interfaces by their Lean names and introduces no new transcription from
external literature. It adds no finite-length, factor-matching, or parent
association hypothesis. It supplies neither the full two-block matching theorem
nor finite length of cuspidal induction. Those separate inputs remain necessary
for the planned adjacent factor-matching proof, which this module does not claim.
