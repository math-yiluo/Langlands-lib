# Matrix norms in cyclic product coordinates

An algebra coordinate isomorphism `E ≃ₐ[F] (Fin (m + 1) → L)` with both
directions continuous induces `cyclicProductGLCoordinates` on general
linear groups. It applies the algebra isomorphism to every matrix entry,
then uses `splitGLCoordinates` to pass to the matrices on the factors.
The scalar extension of a base matrix has the same base change in every
coordinate.

Suppose `σ` shifts to the following coordinate at each nonfinal index
and acts by `τ` on the zeroth coordinate at the wraparound. Let `y` be the
ordered product of the components of `x ∈ GL_n(E)`. The zeroth component
of `cyclicNorm σ ((m + 1) * d) x` is `cyclicNorm τ d y`. The proof follows
the first coordinate through each factor in one cycle, then through the
successive whole cycles. The wraparound applies another power of `τ` to
the product of the components in each whole cycle.

When `σ ^ ((m + 1) * d) = 1`, the cyclic shift identity makes every
component of the full norm conjugate to its zeroth component. The conjugator
from the zeroth component to the component at index `i` is the zeroth
component of the prefix `cyclicNorm σ i x`, with conjugation written
`a⁻¹ * N * a`. Thus a norm association in the product projects to a norm
association in the field coordinate. Conversely, an associated conjugator
for `y` lifts by composing with these prefix conjugators in the individual
coordinates. Finally, every `y` is the product of a tuple with `y` in the
first coordinate and identity matrices in the rest. This gives the equivalence
of `IsNorm` in `cyclicProductGLCoordinates_isNorm_iff`, as well as the
fixed-element `IsNormAssociated` equivalence.

These internal lemmas give the norm calculation for the unit comparison
in Henniart–Lemaire, I.2.1–I.2.2, printed pp. 10–12 (PDF pp. 18–20).
The product coordinates and their shift laws are supplied as input.
