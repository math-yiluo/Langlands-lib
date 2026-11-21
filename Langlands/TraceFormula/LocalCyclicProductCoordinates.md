# Cyclic coordinates of the finite-place local algebra

`localCyclicProductCoordinates` proves `LocalCyclicProductCoordinatesStatement`.
For a cyclic extension of number fields `L/K` of degree `l`, and a finite
place `v` of `K`, the statement gives cyclic product coordinates on the
actual `LocalBaseChangeAlgebra K L (.inr v)`. Each factor is the completion
of `L` at one place `q` above `v`. Its cyclic automorphism has degree `d`,
and `l = (m + 1) * d` for the number of factors `m + 1`. The actual
local generator `localGalois` acts by the coordinate shift and the
field automorphism at the wraparound.

The proof applies `exists_cyclicProductFieldCoordinates` to
`finiteTensorMap`, which is bijective by the completed tensor comparison.
The cyclicity premise on the completed tensor algebra comes from
`isCyclicAlgebra_localGalois`. The local tensor algebra and the field
factors have the module topology over the base completion. The resulting
algebra isomorphism and its inverse are therefore continuous.

The local subring `localIntegers K L v` corresponds under the cyclic
coordinates to the product of the completed integer ring at `q`.
For an element of `localIntegers`, all its powers lie in that compact
subring. Their images under each continuous coordinate map all lie in a
compact set. In a completed field, an element with powers in a compact
set has norm at most one, since larger norm would make the powers
unbounded. Conversely, if every cyclic coordinate is integral, the
powers of the coordinate tuple stay in a compact product of integer
rings. Transporting them through the inverse coordinates and projecting
by `finiteTensorMap` shows that every actual completion coordinate has
powers in a compact set. `mem_localIntegers_iff_finiteTensorCoordinates`
then gives membership in `localIntegers`.

This internal comparison implements the local cyclic product presentation
of Henniart–Lemaire, I.2.1 and I.6.1, printed pp. 10–11 and 39
(PDF pp. 18–19 and 47), together with the order identification needed by
I.3.2, pp. 25–26 (PDF pp. 33–34). The coordinate result applies at every
finite place. Passage to the unit orbital integrals uses the p-adic
packaging of these completions and the normalized Haar measures.
