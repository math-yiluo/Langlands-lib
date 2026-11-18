# Reflecting regular coboundaries through a surjective base change

Let `R → K` be a surjective map of commutative rings in the same universe, let `H` be any group scheme over `Spec R`, and let `M` be an additive module over both rings with the compatible scalar tower. No affineness, flatness or smoothness assumption is imposed on `H`, and no finiteness or flatness assumption is imposed on `M`.

`coefficientEquiv` is the canonical `R`-linear equivalence `K ⊗[R] M ≃ M`, sending `k ⊗ m` to `k • m` and with inverse `m ↦ 1 ⊗ m`. Surjectivity of the scalar map proves the inverse law on pure tensors. For an original test algebra `A`, `extensionTest` is the actual algebra `K ⊗[R] A` over `K`. `extensionPoint` first extends a point of `H(A)` along the right-factor inclusion and then applies the actual point equivalence for the scheme pullback of `H`. The module proves that these extended points are natural in `A`.

`reflectionEquiv` identifies

`(K ⊗[R] A) ⊗[K] (K ⊗[R] M) ≃ A ⊗[R] M`.

It uses the canonical coefficient rearrangement from `ElementaryKernelTensor`, followed by `coefficientEquiv`. Its pure tensor formula sends `(k ⊗ a) ⊗ (l ⊗ m)` to `a ⊗ ((k*l) • m)`. The equivalence commutes with every map of original test algebras. Its inverse is the usual coefficient extension along `A → K ⊗[R] A`, with the scalar cancellation used in `Cohomology.BaseChange`.

`reflectionEquiv_action` proves compatibility with the base change of any `ModuleRepresentation M H`, at the canonically extended source points. The proof reduces to the inverse formula for `reflectionEquiv` and the original action's naturality along the right-factor inclusion. `reflectionEquiv_oneValue` and `reflectionEquiv_twoValue` similarly recover the original values of any base-changed regular one- or two-cochain.

`reflectOneCochain` pulls an arbitrary regular one-cochain on the changed base back to the original base using these points and equivalences. Its naturality follows from the two naturality statements. The theorem `one_isCoboundary_of_baseChange` sends a base-changed one-coboundary primitive through `coefficientEquiv` to an actual element of `M`. The theorem `two_isCoboundary_of_baseChange` pulls a base-changed one-cochain primitive back by `reflectOneCochain`. Applying the compatible coefficient equivalences to their defining equations proves the original coboundary equations.

Finally, `lowDegreeCoboundaries_of_baseChange` assumes `HasVanishingLowDegreeCohomology` for the actual base change of `H` to `K`. For each representation on the specified module `M`, every original regular one- or two-cocycle is a coboundary. It base-changes the cocycle, invokes the supplied vanishing, and applies the two reflection theorems. In particular this applies when `K = R/I` and the ideal `I` annihilates `M`, using its compatible quotient module structure.

This is an internal derived result from tensor equivalences, actual affine-point base change and the existing regular-cochain definitions. The implementation introduces no new literature assertion. It proves neither the supplied vanishing hypothesis nor vanishing for arbitrary original modules without a quotient-base structure. It also makes no assertion about identifying group-valued reduction kernels on arbitrary test algebras and does not prove the homomorphism lifting statement.
