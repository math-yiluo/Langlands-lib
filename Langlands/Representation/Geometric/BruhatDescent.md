# Descent from Weyl double cosets to matrix double cosets

Author: Worker 176.

This internal construction provides `weylToParabolicDoubleCoset`, the actual map
from `W_C \\ S_n / W_B` to `P_B \\ GL_n(R) / P_C` induced by
`w ↦ permutation(w)⁻¹`. It works for any commutative ring and every finite rank,
including zero. It asserts no bijectivity over a ring or a field.

A block-preserving permutation matrix belongs to its upper block parabolic:
below the diagonal, a nonzero permutation entry would identify coordinates
whose block indices differ. The proof uses the published entry formula and
`BlockShape.mem_parabolic_iff`, together with the shared `blockIndex_index`
identity in `WeylDefinitions`. If `w = c * v * b` with `c ∈ W_C` and `b ∈ W_B`,
then its inverse matrix is `permutation(b)⁻¹ * permutation(v)⁻¹ *
permutation(c)⁻¹`. The two outside factors lie in `P_B` and `P_C`, respectively.
This proves well-definedness of the quotient lift. The value on quotient
representatives is definitional, as is `parabolicDoubleCoset_factorization`,
which identifies the existing minimal-representative map with this map composed
with `weylDoubleCoset`.

The construction reuses the published `WeylDefinitions`, `Blocks` and `Maps`
modules. Its internal provenance is a quotient descent justified by the group
laws and the entrywise definitions in those modules. It preserves the inverse
convention documented in `WeylDefinitions.md`; it supplies no new claim from
external literature. Existence of permutation representatives and reflection
of equality from matrix classes to Weyl classes remain separate obligations,
as does existence and uniqueness of minimal Weyl representatives.
