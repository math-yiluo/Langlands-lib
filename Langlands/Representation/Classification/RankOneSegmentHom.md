# Actual geometric pieces of matched rank-one segment products

This internal module assembles published full segment Jacquet formulas with the
uniform geometric-piece tensor transport. It retains actual segment-socle and
minimal-matching hypotheses. It does not assert sphericality or a final quotient.

`rankOneDatum` associates the actual cuspidal class to a rank-one supercuspidal
object. `factor_iso_of_twist_eq` turns equality with a real-twisted cuspidal class
into an isomorphism with the corresponding actual segment factor; its type
includes the rank-equality transport. `index_val_of_size_eq_one` identifies the
coordinates of a singleton block shape with the block numbers.

`pieceEquivOfMatching` assumes a product of rank-one segment socles and a minimal
representative matching each source segment member to the given actual target
supercuspidal class. For any actual intersection refinements it constructs an
equivalence between the geometric piece and the external tensor of the target
objects. Every source refinement size is one. The singleton-coordinate identity
and the matching identify each increasing segment factor with its target object.
The published full normalized segment Jacquet formula therefore supplies the
blockwise tensor equivalences. The uniform geometric-piece constructor composes
these with the actual Weyl transport and tensor reindexing.

`inductionMapOfMatching` constructs an actual nonzero intertwiner from the
segment-socle product to the normalized induction of the matched rank-one
supercuspidal objects. Segment socles and their external tensor are admissible.
The target tensor is irreducible and cuspidal. Thus the geometric-piece
identification above feeds the existing geometric-lemma, cuspidal constituent
and Frobenius constructor. Finally `inductionMapOfContent` chooses the minimal
matching from equality of cuspidal content and weakly decreasing target
scalar-uniformizer norms. Neither constructor needs the source multisegment to
be unlinked; irreducibility of the source is not claimed. Repeated target values
and equal norms are allowed.
