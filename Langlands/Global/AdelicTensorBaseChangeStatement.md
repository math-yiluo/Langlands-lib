# Bijectivity of the canonical full adelic tensor maps

This module states the arithmetic tensor identity underlying the natural
set identification at the start of Brian Conrad, *Weil and Grothendieck
approaches to adelic points* (December 31, 2011), Example 4.2, printed
pp.9–10. The registered source is
`conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
On p.10 Conrad also uses the canonical local tensor decomposition into
the product of completions above a place.

The full ring identity is `L ⊗[K] A_K ≃ A_L`. Its forward map sends
`a ⊗ x` to the principal adele of `a` times the image of `x` under the
literal inclusion `A_K → A_L`. These are exactly the already constructed
algebra homomorphisms `numberFieldAdeleTensorMap` and
`curvePlaceAdeleTensorMap` in `AdelicTensorBaseChange`. Each is an
`L`-algebra homomorphism, with the usual left-factor action on its tensor
source. Bijectivity therefore gives an algebra equivalence without
requiring a further ring-compatibility assertion.

`NumberFieldAdeleTensorMapBijectiveStatement` quantifies arbitrary
number fields `K` and `L` in a common arbitrary universe and their given
`Algebra K L`. This extension is automatically finite. It asserts
`Function.Bijective (numberFieldAdeleTensorMap K L)`. Both adele rings
include every infinite place, as well as the finite restricted product.
This is a full-adele target; the existing finite-adele tensor equivalence
has a different domain and does not by itself prove this statement.

`CurvePlaceAdeleTensorMapBijectiveStatement` quantifies a finite field
`k`, fields `K` and `L` over `k`, a compatible algebra structure
`K → L`, a rational-function presentation of `K` over `k`, and
`FiniteDimensional K L`. The upper rational-function algebra and scalar
towers are derived by composition. Finiteness over `RatFunc k` then
follows by transitivity. Only the lower presentation is an input.
The conclusion is bijectivity of the actual map on full curve-place
adele rings. No separability hypothesis is imposed on `L/K`. The
curve-place rings range over all the places trivial on the finite
constant field; no place is discarded by choosing a rational-function
presentation.

`AdelicTensorBaseChangeStatement` is the conjunction of these two
proposition definitions. The names, conjunction, formulation by
bijectivity and internal derivation of the upper presentation are
derived packaging of the source's arithmetic identity. This module
contains statements only. It does not prove the tensor identity, give
a tensor topology, or prove a scheme- or algebraic-space point
homeomorphism; those are separate results.
