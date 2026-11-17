# Additive structure of affine square-zero reduction kernels

Let `G` be an affine group scheme over `Spec R`, let `A` be any commutative `R`-algebra, and let `I` be an ideal of `A` with `I² = 0`. This module proves that `SquareZero.kernelDerivationEquiv` from the companion `SquareZeroKernel` module carries multiplication in the actual kernel `ker(G(A) → G(A/I))` to addition of ideal-valued augmentation derivations.

`idealDerivationLift` sends an augmentation derivation into `I` to an algebra map into the split formal extension `A ⊕ I`. `formalPoint` uses the actual affine-point coordinates to obtain a point of `G(A ⊕ I)` with that infinitesimal part. Its constant projection is the identity. The algebra homomorphism `collapse` sends `(a,i)` to `a+i`; square-zero multiplication of the actual ideal makes it multiplicative. Collapsing the formal point recovers the prescribed actual kernel point.

The main group-law argument uses two independent infinitesimal directions. For two formal points trivial under the constant projection, place the first in the first summand of `I × I`, place the second in the second summand, and multiply the resulting points over `A ⊕ (I × I)`. Projection to the two summands recovers the original points. Projection by addition gives their product. Naturality of actual coordinate evaluation therefore shows that the infinitesimal coordinate of that product is the sum of the two original coordinates. Applying `collapse` and subtracting the actual augmentation yields `kernelDerivationEquiv_mul` for the original kernel.

Injectivity of the derivation comparison then gives `kernel_mul_comm`. `kernelAddEquiv` expresses the result as an additive equivalence between the actual kernel written additively and the derivation group. For a smooth affine `G`, `kernelTensorAddEquiv` composes this equivalence with the identity cotangent universal property and the finite-projective dual-tensor-Hom comparison to give

`Additive(ker(G(A) → G(A/I))) ≃+ I ⊗[R] Additive(lieKernel G R)`.

There is no flatness, freeness, projectivity or finite-generation assumption on `A` or the actual coefficient ideal `I`. Smoothness is used only for the final Lie-tensor comparison. This module does not compare conjugation actions, identify an extended base ideal with a tensor product on nonflat tests, or extend the kernel equivalence to a nonaffine target.

This is an internal derived construction. It generalizes the Library's independent-infinitesimal-direction proof for dual-number Lie kernels to arbitrary actual square-zero ideals, using actual affine-point coordinates, the previously constructed ideal-valued derivation comparison, and functoriality of split square-zero extensions. Every claimed identity and equivalence is proved in Lean; no new literature assertion or homomorphism lifting theorem is introduced.
