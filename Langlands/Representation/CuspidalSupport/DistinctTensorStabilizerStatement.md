# The self-stabilizer count for distinct cuspidal tensor factors

Author: Worker 495.

`Langlands.CuspidalSupport.GLDistinctCuspidalTensorStabilizerStatement`
is a proposition definition, with independent field and carrier universes
`uF` and `uV`. It takes any prime `p` with `Fact p.Prime`, an actual
`F : PadicField.{uF} p`, and the supplied compatible topological data `T`.
After installing `T.topology`, it quantifies every natural total rank `n`,
every actual `B : GeneralLinear.BlockShape n`, and every family of actual
supercuspidal representations `A i` of rank `B.size i`.

Associate to block `i` the actual cuspidal datum
`⟨B.size i, B.positive i, (A i).isoClass⟩`.
The sole additional premise is injectivity of this sequence. Thus equal
ranks are allowed when their actual supercuspidal isomorphism classes are
distinct, and unequal ranks are allowed without any further comparison.
The conclusion states that the natural cardinality of
`AssociatingPermutations B B ρ ρ` is exactly one, where `ρ` is the actual
external tensor action of the representations `(A i).obj.representation`.

The existing `AssociatingPermutations` counts minimal coordinate
permutations of the ambient `Fin n` that conjugate the entire embedded
source Levi onto the target Levi and whose actual inverse-conjugation
transport of `ρ` is equivalent to `ρ`. It counts these permutations
themselves, retaining the existing Weyl minimality condition. It does not
count every conjugating permutation or just isomorphism classes of
representations. The formula also covers the empty shape at rank zero:
the factor-injectivity premise is vacuous, while the count still asserts
one minimal self-associating permutation.

The provenance is internal and derived. This isolates the finite
self-association calculation needed when all inducing cuspidal data are
distinct. The definitions of block shapes, actual supercuspidal objects
and classes, external tensors, inverse-conjugation transport and minimal
associating permutations are reused without changes. No new literature
claim is attached to this internal interface.

There is no Jacquet-filtration, induction, freeness, central-character,
semisimplicity or classification premise. The statement imports only
the existing segment and supercuspidal definitions, Levi-association
definitions, and finite tensor constructions. In particular it neither
assumes nor asserts segment head or socle existence, segment analytic
classification, segment-product uniqueness, ordered heads or socles,
multisegment exhaustion or coverage, tempered uniqueness, square-integrable
classification or exhaustion, or regular exhaustion.

This module states the cardinality assertion and proves none of it. A
proof successor requires this statement's independent acceptance and
Library publication. It supplies no proved input to the parent
segment-existence task.
