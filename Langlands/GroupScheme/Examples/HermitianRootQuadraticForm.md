# The base-field quadratic form of a diagonal Hermitian form

This derived algebraic construction associates an actual `k`-valued quadratic
form to the published diagonal Hermitian form for a separable quadratic field
extension `L/k`. The fields and finite index type have independent universes.
No characteristic restriction is imposed.

The construction `extensionQuadraticMap` is a sum of products of `k`-linear
coordinate maps with their conjugates, weighted by the original diagonal
coefficients. Its value at `x` is exactly `H.pairing x x`. Each product is a
quadratic map over `k`, as is their weighted sum.

The existing element `SU3Root.traceOne k L`, supplied by separability, defines
the `k`-linear map `traceOneRetraction`: multiply by this element, then take the
field trace. On an element fixed by the quadratic conjugation, the composite
with `algebraMap k L` is the identity, since the sum of the trace-one element
and its conjugate is one. This argument does not divide by two.

The actual base-field `quadraticForm` is the composite of this linear
retraction with `extensionQuadraticMap`. The theorem `algebraMap_quadraticForm`
identifies its values with the Hermitian self-pairing. Injectivity of
`algebraMap k L` then shows that its zero vectors and its anisotropy agree
exactly with those of `H`. Its underlying vector space has base-field
dimension `2 * Fintype.card ι`. The quadratic polar bilinear form maps under
`algebraMap` to `H.pairing x y + H.pairing y x`.

If every Hermitian weight is nonzero, `quadraticForm_polar_separatingLeft`
shows that this polar form has zero left radical, in every characteristic.
For a nonzero coordinate `x i`, the proof chooses a vector supported at `i`
whose pairing with `x` is the trace-one element: its coordinate is the
conjugate of `(H.weight i * x i)⁻¹ * traceOne k L`. The two cross-pairings
therefore sum to one, contradicting vanishing of the polar pairing against
every vector. The empty index case is included.

The provenance is internal algebra from the published Hermitian pairing,
the actual quadratic involution and trace-one construction, and Mathlib's
quadratic-map operations and finite-product dimension formula. This file
proves no local-field isotropy theorem or bound on the dimension of
anisotropic forms. Such an arithmetic input is still required to bound the
middle Hermitian dimension in the rank-one classification.
