# Ideal-valued primitives for function Čech coboundaries

Let `f` be a separated morphism to `Spec R` with a supplied affine open
cover, and let `I` be an ideal of `R`. Suppose global functions on the
actual base change to `Spec (R ⧸ I)` are pulled back from that affine
base. The theorem `exists_ideal_primitive_of_cechD_mem` takes a degree-zero
function cochain whose Čech coboundary belongs on every overlap to the
extended ideal. It gives a new primitive for the same coboundary with
all chart values in the extended ideal.

On affine overlaps the kernel of reduction is the extended base ideal.
Consequently the reductions of the original primitive agree on overlaps
and glue to a global function on the reduced scheme. The assumed
surjectivity makes this function a constant. Lift that constant to `R`
and subtract it on each thicker chart. The resulting cochain vanishes
on reduction, and the Čech differential of the subtracted cochain is
zero because all the restrictions commute with scalar maps.

This is an internal consequence of the actual section-ring comparison
`quotientReductionMap_appLE` and the sheaf gluing axiom. It is used in
the converse degree-one morphism criterion of Kai-Wen Lan,
*Arithmetic compactifications of PEL-type Shimura varieties*, revised
14 March 2021, Proposition 2.1.6.9, printed p. 136 (PDF p. 164). The retained
source is `lan-2008-pel-thesis-revision-2021`, SHA-256
`a7a454f5d0735f4bf11f00a8afc14c361c5fc2cefd691d7466f7620ab4c3a079`.
