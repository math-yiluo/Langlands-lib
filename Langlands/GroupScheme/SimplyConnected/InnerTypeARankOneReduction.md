# Conditional rank-one reduction for inner type A

Author: Worker 165.

`Langlands.GroupScheme.exists_binary_model_of_innerTypeA.{u}` proves the
family-(i) model conclusion from two explicit structural hypotheses:

- `Langlands.GroupScheme.InnerTypeANormOneStatement.{u}`;
- `Langlands.GroupScheme.CentralSimpleUnits.MatrixNormOneSplitRankStatement.{u}`.

For any field `K : Type u`, the remaining inputs are an affine locally
finite type group scheme `G` over `Spec K`, actual `d : TitsIndexData G`,
a natural number `n`, simple connectedness and absolute almost-simplicity
of `G`, `d.HasInnerTypeA n`, and `splitRank G = 1`. The type condition
compares every actual Cartan entry with the rank-`n` type-A matrix and
requires the full absolute Galois star action to be trivial. It contains
no model presentation.

The conclusion supplies a finite-dimensional central division algebra
`D : Type u` over `K` and an actual group-scheme isomorphism
`G ≅ CentralSimpleUnits.BinaryRoot.groupScheme K D`. This is precisely
the model and the division-algebra witnesses in family (i) of the
published local rank-one classification. This result works over arbitrary
fields and in every characteristic; it requires no valuation, topology,
or local-field hypothesis.

`BinaryNormOnePresentation K G` stores this output as a division algebra
with its actual algebraic instances and an isomorphism of group schemes.
The noncomputable `innerTypeABinaryPresentation` constructs such data by
classical choice from the proved existential conclusion. The presentation
is a result of the construction, with no additional input hypothesis.

## Implemented proof and internal provenance

Apply the supplied inner-type-A statement to obtain a central simple
algebra `A : Type u` and an actual norm-one presentation
`G ≅ CentralSimpleUnits.normOne K A`. Its reduced-degree equation is not
needed for this consequence. Apply the published
`CentralSimpleUnits.exists_binary_model_of_normOne_presentation` with
this isomorphism, the supplied matrix-rank statement and the split-rank-one
equation. That theorem constructs a division-matrix presentation by
Wedderburn--Artin, transports the actual norm-one group through the
algebra equivalence, and uses rank invariance and the supplied rank
formula to force matrix size two. Thus the proof uses constructed
isomorphisms, rather than assigning a type label to the group.

This is an internal composition of the two published statement interfaces
and the published division-model reduction. No additional external
classification assertion is introduced. The Lean imports are
`Langlands.GroupScheme.SimplyConnected.InnerTypeANormOneStatement` and
`Langlands.GroupScheme.CentralSimpleNormOneDivisionModel`.

The theorem does not prove either structural hypothesis. It also does
not prove that an arbitrary local rank-one group has inner type A, or
handle the other classical families or exceptional and trialitarian
exclusions. The final classification still needs those obligations and
a closing theorem with no additional premise.
