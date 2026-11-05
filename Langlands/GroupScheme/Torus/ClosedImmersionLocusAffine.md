# Closed-immersion neighbourhoods over affine bases

For an actual homomorphism from the standard diagonal Hopf spectrum to an
affine group scheme over `Spec R`, the diagonal coordinate map is obtained
from the fully faithful Hopf spectrum functor. Its spectrum is exactly the
given homomorphism followed by the inverse affine-coordinate isomorphism
of the target.

After any base change `R → A`, closed immersion of the actual homomorphism
is equivalent to surjectivity of its diagonal scalar-extension map. This
follows from the natural tensor-spectrum comparison and cancellation of the
base-changed target-coordinate isomorphism.

When the additive degree group is finitely generated and the map is a closed
immersion at a specified field point, the algebraic coefficient-product
certificate supplies an element with nonzero image at that point.
The principal localization at this element is an actual open subscheme of
`Spec R`, and the field point factors through it using the localization
universal property. The scalar-extension criterion proves that the restricted
actual group homomorphism is a closed immersion.

For an arbitrary supplied split torus, choose its isomorphism with a finite
product of multiplicative groups. The standard diagonalizable group with
character group `ℤ^I` is isomorphic to that product. Transporting the source
along this actual group-scheme isomorphism reduces to the diagonal case;
its base changes are isomorphisms, so the closed-immersion condition is
preserved in both directions. Any supplied field-valued point of `Spec R`
is the spectrum of its ring map, which supplies the scalar algebra structure
used above. The final affine theorem retains the exact factorization of
that original point.

This is an internal affine implementation of the closed-immersion
neighbourhood step. It uses arbitrary commutative base rings and makes no
smoothness, finite-presentation, or noetherian assumption on the target.
