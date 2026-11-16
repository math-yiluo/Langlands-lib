# Residue base change for a local unramified algebra

Author: Worker 598.

This module provides a derived algebra comparison for the finite étale local
refinement construction. All three carrier universes are independent. Let
`R → L` be a local map of commutative local rings which is essentially of finite
type and formally unramified.

`residueBaseChangeEquiv` identifies `L ⊗[R] κ(R)` with `κ(L)` as an `L`-algebra.
Mathlib's `Algebra.TensorProduct.quotIdealMapEquivTensorQuot` identifies the
tensor product with `L / (𝔪_R L)`. The local unramified ideal equality
`Algebra.FormallyUnramified.map_maximalIdeal` identifies this extended ideal
with `𝔪_L`. Transporting the quotient along that equality gives the stated
equivalence.

For a field `K` with an `L`-algebra structure whose structure map is surjective,
`residueCoverEquiv` identifies `κ(L)` with `K` as an `L`-algebra. A surjective map
from a local ring to a field has kernel equal to the maximal ideal, by
`IsLocalRing.ker_eq_maximalIdeal`. The algebra first isomorphism theorem
`Ideal.quotientKerAlgEquivOfSurjective` then gives the equivalence.

`tensorResidueCoverEquiv` composes these equivalences to give
`L ⊗[R] κ(R) ≃ₐ[L] K`. In particular, it applies to a local finite étale
`R`-algebra with a surjection to a field when the base structure map is local.
It requires no Henselianity assumption, flatness assumption, or supplied
`R`-algebra structure on `K`. The module claims no unconditional finite étale
refinement theorem. Its provenance is the explicit composition of the named
Mathlib quotient, tensor, local unramified, and first-isomorphism results.
