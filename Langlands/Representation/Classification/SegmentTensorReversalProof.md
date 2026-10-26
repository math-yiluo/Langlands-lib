# Association of the two actual segment tensors

Author: Worker 495.

This proof supplies
`Langlands.Classification.segmentTensorReversalAssociation.{uF,uV} F T`
of `Langlands.Classification.SegmentTensorReversalAssociation.{uF,uV} F T`.
Its outer telescope is `{p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
(T : F.TopologicalData)`, with no additional theorem-valued premise.
The direct helper is
`Langlands.Classification.segmentFactors_associated_segmentFactorsDown`.
For every supplied p-adic field and topological data, every nonnegative
number of factors, every positive factor rank, and every actual smooth
representation of that rank, the increasing and decreasing segment
external tensors are associated in the existing
`CuspidalSupport.RepresentationsAssociated` sense. Field and carrier
universes remain independent. Neither irreducibility nor cuspidality of
the factor is required.

The uniform block shape is unchanged when its blocks are permuted.
The proof uses its actual `blockPermutation Fin.revPerm` coordinate
permutation. The published `conjugatesLevi_blockPermutation` proves that
this permutation conjugates the whole embedded Levi onto itself.
The published `leviConjugation_symm_blockPermutation_apply` identifies
the inverse Levi action with the inverse coordinate reindexing.

The private definition `blockPermutationTensorEquiv` constructs the actual
representation equivalence for any block shape and block permutation.
It uses `FiniteTensor.reindexEquiv`; its action identity identifies the
transported external action with the external action of the reindexed
factor sequence. Explicit reindexed module instances keep the dependent
carrier families aligned.

For the uniform segment shape, compose this equivalence with the identity
linear equivalence of the underlying tensor space. On pure tensors its
intertwining identity reduces to one identity for each factor. The formula
`Fin.val_rev`, followed by natural subtraction arithmetic, identifies that
factor with the existing `T.segmentFactorsDown` factor. Pure tensors span
the whole tensor space, so the identity intertwines the whole action.
This gives an actual equivalence of the transported tensor actions.
The same construction includes the empty tensor. The exact wrapper
installs the supplied topology, introduces the rank, length and actual
smooth factor, and applies the direct helper. Its objects are
definitionally the tensor actions in the published proposition.

This is an internal derivation from finite tensor reindexing and block
permutation conjugation. It makes no assertion about induced
representations, a nonzero induction map, or segment constituents.
A recursive audit of all 101 project modules in this module's import
closure, including this module, found no missing modules, unpaired Lean
files or excluded higher classification input.
Apart from the present proof and its statement, the classification branch
consists only of `Segments`, `ConstituentRelations`, `Supercuspidal`,
`SupercuspidalTwist`, and the supercuspidal contragredient statement and
auxiliary algebra. In
particular, the imported `AssociationReduction` supplies the actual block
conjugation formula; its conditional adjacent-swap reduction is not used
to infer a classification theorem. Its geometric-piece branch proves
individual full-Levi comparisons without assuming a geometric filtration.
Other branches provide block and Weyl combinatorics, actual normalized
induction and Jacquet definitions, smooth transfer, finite tensors and
local-field normalization.

The argument therefore remains directly and transitively independent of
individual segment head/socle existence, segment analytic classification,
generic segment-product uniqueness, special-head product irreducibility,
ordered head/socle existence, multisegment exhaustion, coverage or
conversion, tempered uniqueness, square-integrable classification or
exhaustion, and regular exhaustion. The imported geometric-lemma and
induction interfaces do not supply any proved filtration or induced-map
premise to this tensor argument.
