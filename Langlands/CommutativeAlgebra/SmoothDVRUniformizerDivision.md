# Division by a uniformizer in smooth algebras over a DVR

Author: Worker 171.

Module `Langlands.CommutativeAlgebra.SmoothDVRUniformizerDivision`.

`dvd_of_forall_mem_prime` states: let `R` be a discrete valuation domain, `B` a smooth
`R`-algebra (`Algebra.Smooth R B`), `π` an irreducible element of `R`, and `h : B`
an element lying in every prime ideal of `B` that contains `algebraMap R B π`. Then
`algebraMap R B π ∣ h`.

Proof as implemented. `I = (π)` is maximal, so `R ⧸ I` is a field. The base change
`(R ⧸ I) ⊗[R] B` is smooth over this field, hence reduced by the published
`SmoothReducedProof.isReduced_of_smooth_of_domain`. Mathlib's
`Algebra.TensorProduct.quotIdealMapEquivTensorQuot` and the tensor symmetry identify
`B ⧸ I B` with this ring, so `B ⧸ I B` is reduced. The hypothesis puts `h` in the
radical of `I B = (algebraMap R B π)` (`Ideal.radical_eq_sInf`); in the reduced
quotient its image is nilpotent, hence zero, so `h ∈ (algebraMap R B π)`.

Geometrically: the special fibre of a smooth scheme over a DVR is reduced, so a
function vanishing at every point of the special fibre is divisible by the
uniformizer. This is an internal lemma derived from published Library and Mathlib
results; no external source is asserted.
