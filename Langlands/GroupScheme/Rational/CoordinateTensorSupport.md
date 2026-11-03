# Literal tensor support for actual pointed affine coordinates

This internal adapter derives the literal sum support bound for the tensor of
the two actual augmentation ideals from explicit decompositions of the actual
input augmentation eigenspaces. Actual product-coordinate decomposition supplies
independence after transporting through the actual tensor coordinate equivalence.
The decomposition premises remain hypotheses. The intended source step is
Conrad–Gabber–Prasad, *Pseudo-reductive Groups*, second edition (2015),
Lemma 3.3.4, printed pp. 108–109 / PDF pp. 134–135. The constructions and
conditional lemmas here are internal adapters for that argument.

All constructions use a field `k : Type u`, the actual character lattice of
the acting commutative group scheme `S`, actual pointed actions on affine
schemes `V` and `W` over `k`, and their coordinate algebras. The eigenspaces
come from `PointedCoordinateAction` and impose the eigenfunction equation
on every coefficient algebra and every point.

`tensorSupportSpan a b` is the supremum of the actual tensor eigenspaces
whose characters lie in `Set.image2 (· + ·) (support a) (support b)`.
Thus every selected character is a sum of one augmentation support
character from each factor. No zero character is inserted into either set.

`augmentation_le_degreeSpan_support` assumes that the augmentation
eigenspaces form an internal direct sum. The proof maps their supremum
along the augmentation inclusion. Each nonzero summand element witnesses
membership of its character in the augmentation support; a zero element
belongs to the selected span directly.

`tensor_weightSpace_compatible` applies the pure-tensor character-addition
law to the bilinear image of two weight spaces.
`tensorWeightSpace_iSupIndep` assumes an internal direct-sum decomposition
of the actual product coordinate algebra. It transports independence
along `tensorCoordinates`.

`tensor_augmentation_le_sum_degreeSpan` assumes the two augmentation
decompositions and combines the factor span bounds with the bilinear
compatibility. It concludes that the range of the tensor of the two
augmentation inclusions lies in `tensorSupportSpan`.
`weight_mem_sum_of_identity_slices` additionally assumes the product
coordinate decomposition. If a nonzero tensor eigenfunction is killed by
both actual identity slices, the common-kernel theorem places it in the
augmentation tensor range. Independence then forces its character to
belong to the literal sum set.

These lemmas do not establish the decomposition hypotheses from splitness,
the image support bound, the comparison with Lie weights, or the full
`SemigroupCommutatorStatement`. The decomposition inputs remain explicit
for consumers to supply.
