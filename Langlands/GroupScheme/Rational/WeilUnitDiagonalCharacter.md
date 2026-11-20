# The diagonal character of Weil-restricted units

For a finite projective commutative algebra `B` over a commutative
ring `A`, `WeilGm.diagonalCharacter A B` is a morphism over `Spec B`
from the base change of `Res_{B/A} Gₘ` to `Gₘ`. On a test scheme over
`Spec B`, the pullback adjunction gives a point over `Spec A` with
unit coordinates in `B ⊗[A] Γ(T)`. Multiplying the left tensor
factor into the `B`-algebra `Γ(T)` gives the character value. This
family commutes with restriction on test schemes and defines the
actual group-scheme homomorphism.

When `A`, `B` and the test algebra `R` are fields, with compatible
algebra structures, `diagonalCharacter_affine` identifies the value
in `Rˣ` with evaluation of the original `B ⊗[A] R` unit. The affine
section isomorphisms over the two base fields have the same
underlying ring isomorphism. The restriction-of-scalars test
comparison induces the identity on the spectrum. Naturality of
multiplication of the tensor factors then gives the formula in
affine coordinates.
