# The whole rational division-algebra action on a formal atlas

For an actual formal atlas `X` over an `𝒪[K]`-algebra, let `E` be an action
of the integer order in the finite-dimensional central division `K`-algebra
`D`. `atlasRationalAction` extends it to a `K`-algebra map from `D` to the
whole rational composition algebra `K ⊗[𝒪[K]] Hom X X rfl`.
For an integral element `a`, the image is `1 ⊗ E.endomorphism a`, using
the original compatible family of integral formal maps.

The original integral family gives a ring homomorphism by equality of
integral atlas maps on test charts. Tensor balancing identifies the base
integer scalars, and scalar extension through `integerTensorEquiv` gives
the map on `D`. Evaluation on a test chart gives the existing coordinate
`rationalAction` for the order action extended to that test algebra.
Coefficient extension of the atlas commutes with the whole action as well.
Both identities are equalities of algebra maps out of `D`, proved by checking
agreement on the actual integer order that spans `D`.

This internal construction supplies the whole atlas maps for the inverse
division-unit term in Drinfel'd, *Coverings of p-adic symmetric regions*
(1976), §2 A, printed p. 109.
