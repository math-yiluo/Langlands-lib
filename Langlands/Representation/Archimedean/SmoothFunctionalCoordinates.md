# Finite derivative coordinates of a smooth Hilbert functional

`SmoothFunctionalCoordinatesStatement` concerns a supplied representation
`π : G →* (E →L[ℂ] E)` of a real Lie group on a complex Hilbert space `E`.
It has independent universes for the model vector space, the model
manifold, `G`, and `E`. If a complex-linear functional `L` on
`smoothVectors I π` satisfies `IsContinuousOnSmoothVectors I π L`, then
there is a finite set `J` of words and a vector `a i : E` for each `i : J`
such that for every `v : smoothVectors I π`,

\[
L(v) = \sum_{i \in J} \langle a_i,\; \operatorname{iteratedLieDerivative}(I,\pi,i,v)\rangle_{\mathbb C}.
\]

The inner product is linear in its second argument. Neither the word set
nor the test vectors depend on the vector being evaluated.

## Proof and provenance

`exists_eq_sum_inner_iteratedLieDerivative` implements the proof.
Starting with the finite word bound with witnesses `S` and `C`, it takes
`J = insert [] S`. The complex-linear map `j` with these derivative
coordinates takes values in the finite product `J → E`; the empty word
records the original vector, making `j` injective. Each selected
coordinate norm is bounded by the product sup norm. Thus the induced
functional on the range of `j` is bounded by `max C 0 * S.card` times
that norm.

Mathlib's `StrongDual.exists_extension` extends this range functional to
the whole product by Hahn–Banach. The finite sum of coordinate injections
recovers each product vector. Restricting the extension to each injection
and applying `InnerProductSpace.toDual` in reverse gives the Riesz test
vectors in `E`, and evaluating the sum at `j v` gives the formula.
`smoothFunctionalCoordinates` packages the result at the exact proposition.

This is an internal consequence of the published genuine word-derivative
continuity criterion (`IsContinuousOnSmoothVectors`, with its topological
interpretation in `SmoothDerivativeTopology`) and Mathlib's Hahn–Banach
and Riesz theorems. The formula by itself asserts neither covariance nor
Whittaker uniqueness.
