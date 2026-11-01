# Quasicuspidal reversed Jacquet classes of the Aubert image

This derived helper proves `QuasicuspidalJacquetExchangeStatement` from the
published actual Jacquet compatibility of the unadjusted Aubert operator and
the published quasicuspidal eigenvalue of its product-Levi operator. It is an
intermediate result for segment exchange and does not prove the general
segment socle-to-special-head theorem.

For an arbitrary block shape `B` of rank `n`, `reversedJacquetObject` is the
actual normalized upper Jacquet module for `B.reverse`, pulled back along
the continuous product-label reversal `outerReverseLeviEquivContinuous B`.
The published conjugation calculation identifies this with transport to `B`
by inverse conjugation with `B.reversePermutation`. Its action is literally
the reversed Jacquet action composed with `leviReverseEquiv B`. Actual
Jacquet restriction and continuous group transport preserve finite length,
which supplies the finite-length witness used by its canonical exact class.

If the actual upper Jacquet module for `B.reverse` is quasicuspidal, the
upper `B` Jacquet class of the Aubert image is
`(-1)^(n - B.length)` times this transported object's class. The proof
evaluates the published equality of maps on the canonical class, computes
the actual Jacquet image, applies the product-Levi eigenvalue, and computes
the actual transported class. All exact sequence relations, including
nonsplit ones, remain those of the existing Grothendieck group.

The statement retains arbitrary primes, supplied fields and topologies,
independent field and carrier universes, saturated carriers, every natural
rank, and every block shape. It assumes quasicuspidality of the displayed
Jacquet object; it establishes neither that hypothesis for segments nor
irreducibility, effectivity, or an identification with a segment head.

The uniform-block helpers also construct actual maps. Reversing equal-sized
blocks preserves the block shape, and `uniformJacquetObject_reverse_eq`
identifies the corresponding bundled upper Jacquet objects. Keeping this
comparison at the object level avoids unfolding and comparing their
coinvariant carriers. The tensor-reversal equivalence identifies the
increasing tensor, pulled back along product-label reversal, with the
decreasing tensor. Pullback keeps a supplied intertwiner's linear map, so
it keeps that map nonzero. Composing with the tensor equivalence also
preserves nonzeroness, by injectivity. Thus
`exists_reversedJacquet_to_segmentTensorDown_ne_zero` takes any nonzero map
from the actual full uniform upper Jacquet module to the increasing tensor
and constructs one from `reversedJacquetObject` to the decreasing tensor.
These map lemmas require neither irreducibility nor finite length.

The substantial imported inputs have the following scope. The published
`jacquetCompatibility` intertwines actual upper Jacquet restriction with
the reversed product-Levi Aubert operator and actual inverse-conjugation
transport on every virtual class. The published
`alternatingOperatorOnLevi_quasicuspidal` kills all proper refined Jacquet
terms and evaluates the whole refinement, leaving the sign
`(-1)^(n - B.reverse.length)`. The published transport calculation
`leviConjugation_outerReverse_symm` identifies that inverse conjugation with
reversal of product labels. These are independently proved lower inputs;
no segment or multisegment classification conclusion is asserted here.
The published `Classification.segmentTensorReverseEquiv` uses actual tensor
reindexing and the equality between the reversed exponent and the
decreasing exponent; its scope is every supplied smooth factor. The map
construction uses that equivalence without a classification premise.
No new claim from the original literature is made.
