# Additivity of the actual dual-kernel character

This internal adapter proves additivity of the particular intrinsic beta
constructed in `DualKernelCharacter`. It applies to an actual abelian-scheme
homomorphism `f : A → B`, with the existing chosen dual witnesses, Picard-zero
pullback stability, six further explicit dual-constructor propositions,
and actual inverse line bundles and tensor evaluation isomorphisms at both
endpoints. These are the inputs of the constructed dual group schemes and
their dual homomorphism. No character or additivity law is supplied as data.

`dualKernelPointCharacter_mul` ranges over every test scheme `T` over the
base and every pair of points `x,y` of the actual scheme-theoretic kernel
of the dual homomorphism. It proves

```
beta(x * y) = beta(x) + beta(y).
```

The points are written multiplicatively because they are points of a group
object. The Cartier character presheaf is written additively: addition of
characters means multiplication of their values in the multiplicative group.

The proof is split through `dualKernelCharacter_tensor_of_class`. This
helper takes three ordinary dual points, their three explicit origin
equations, and equality of the third Picard-zero class with the tensor of
the first two classes. It takes the actual Poincaré representatives `L`
and `K`. The existing `dualKernelPullbackModuleIso` gives a trivialization
of each pullback along `f_T`. The published tensor-character construction
provides a trivialization of the pullback of `L ⊗ K`.

Three small comparison lemmas keep these steps explicit.
`dualPointFamily_tensor_class` follows from the published formula for tensor
on quotient representatives and `dualPointFamily_class`.
`hasTrivialHomPullback_rigidified_tensor` and
`trivialHomPullbackCharacter_rigidified_tensor` apply the existing
line-bundle tensor laws after forgetting rigidification. The helper compares
each of the three beta values with its representative character using
`dualKernelCharacter_eq_of_family_class`, then uses this tensor law.

The actual-kernel specialization composes each kernel point with the
dual-kernel inclusion and uses the existing origin equations. It invokes
this helper after proving its tensor-class equation.

The inclusion is a group-scheme homomorphism.
`dualCommGroupSchemePointMulEquiv` identifies multiplication of the included
dual points with tensor of their actual Picard-zero classes. After forgetting
membership, the rigidified tensor representative has exactly the class of
the product point. `dualKernelCharacter_eq_of_family_class` therefore allows
beta of the product to be computed using this tensor representative.
`trivialHomPullbackCharacter_tensor`, with the proved
`universalGlobalFunctions A`, gives the displayed equation. Its orientation
is the original ordinary-to-translated action convention, with no inversion.

`dualKernelPointCharacter_one` derives the zero-character value at the
identity from that equation and cancellation in the character group.
`dualKernelPointCharacterAddHom` packages exactly the original beta function
as an additive homomorphism from the additive notation for actual
dual-kernel points. `dualKernelPointCharacter_inv` follows by preservation
of negatives and says that the inverse point gives the negative character.

The provenance is internal composition of the actual dual-point tensor
classification, intrinsic character independence on representatives, and
the tensor law of the transported kernel action. The base may be arbitrary;
this module adds no finiteness or invertibility hypothesis and asserts no
bijectivity, effective descent, Cartier duality, perfectness, or finite Weil
pairing law. Those remain separate obligations.
