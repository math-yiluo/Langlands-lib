# Reversal association for segment tensors

Author: Worker 495.

`Langlands.Classification.SegmentTensorReversalAssociation.{uF,uV} F T`
is an internal proposition about the actual Levi representations used to
induce a segment. It keeps the field universe `uF` and representation-carrier
universe `uV` independent, for every prime, supplied p-adic field `F`, and
compatible topological data `T`.

For every positive rank `r`, every natural number `m`, including zero, and
every actual smooth complex representation `A` of `GL_r(F)`, let
`B = BlockShape.uniform m r hr`. The proposition asserts
`CuspidalSupport.RepresentationsAssociated B B` for the actual external
tensors of the two existing families:

- `T.segmentFactors A m hr`, whose factors are `A, νA, …, ν^(m-1)A`;
- `T.segmentFactorsDown A m hr`, whose factors occur in the reverse order.

Here `ν = |det|` uses the existing residue-normalized determinant character.
Each external tensor carries the factorwise action of the actual product
Levi `B.Levi F.Carrier`. Association means that some coordinate permutation
conjugates the whole embedded Levi onto itself and that the increasing
tensor, transported by the inverse of this actual Levi conjugation, is
equivariantly isomorphic to the decreasing tensor. The proposition uses
the existing definition of association and does not require the permutation
to be minimal. It asks for an actual representation equivalence, beyond
an equality of multisets of classes.

No irreducibility, admissibility, cuspidality, distinctness or positive-length
hypothesis is imposed on `A` or the sequence. When `m = 0`, the same
proposition concerns the empty external tensor on the empty product Levi.

The provenance is internal. This interface isolates the finite reversal
calculation in the proposed individual segment constituent proof. Its
constructions are already defined in `Segments`, `LeviDefinitions` and
`Tensor.Finite`. A proof can use the actual uniform block reversal and
tensor reindexing; that proof is a separate obligation. No original
literature theorem is being translated or cited as establishing this
interface.

This statement makes no assertion about parabolic induction, an
intertwining map between induced representations, Jacquet filtrations,
or segment constituents. Its imports require no individual segment
head/socle existence, segment analytic classification, generic segment
product uniqueness, special-head product irreducibility, ordered
head/socle existence, multisegment exhaustion, coverage or conversion,
tempered uniqueness, square-integrable classification or exhaustion,
or regular exhaustion.

This file defines the proposition only. It does not prove association or
complete the parent segment-existence task.
