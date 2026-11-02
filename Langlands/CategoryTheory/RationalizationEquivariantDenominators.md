# Exactly equivariant integral representatives

This is an internal consequence of `RationalizationDenominators`, integer
linearity, and a finite integer basis. It applies to any preadditive category;
it does not assume that its integral Hom groups inject into their
rationalizations.

`exists_common_zsmul_eq` takes finitely many pairs of integral morphisms
whose rationalizations are equal. For each equality the localization criterion
provides a nonzero integer making the integral equality exact. Their product
is nonzero and is divisible by each multiplier, so it makes every equality
exact simultaneously. The empty index type is allowed, with product one.

`IntegralIsoData.rescale` multiplies the supplied forward and inverse
representatives by independently chosen nonzero integers `r` and `s`, and
multiplies their corresponding denominators by the same integers.
Bilinearity of composition preserves both exact integral inverse identities:
the two composites equal multiplication by the product of the new
denominators on the respective identity morphisms. The identities recording
the rationalizations are also preserved.

For integral actions `a : O →+* End X` and `a' : O →+* End Y`,
`intertwines_of_basis` extends the equations
`a (b i) ≫ f = f ≫ a' (b i)` from an integer basis `b` to every `x : O`.
Its proof expresses the two sides as integer-linear maps out of `O` and
uses basis extensionality. This result does not require the basis to be finite.

`EquivariantIntegralIsoData a a' e` extends the existing `IntegralIsoData e`
for a rational isomorphism `e` by the exact integral equations

```
a x  ≫ hom = hom ≫ a' x
a' x ≫ inv = inv ≫ a x
```

for every order element `x`. Thus it retains nonzero forward and inverse
denominators, their rationalization equations, and both exact integral
inverse-multiple identities.

`nonempty_equivariantIntegralIsoData` proves such data exist whenever `O`
has a finite integer basis and the rational forward map of `e` intertwines
the actions. First, the rational inverse intertwines by cancellation with
the forward isomorphism. Start with the published existence of integral
representatives with exact inverse-multiple identities. Their basis
commutators vanish rationally. Apply `exists_common_zsmul_eq` separately
to the forward and inverse basis commutators and rescale both representatives.
The basis equations are then exact integrally; `intertwines_of_basis`
extends them to every order element. `equivariantIntegralIsoData` chooses
data from this proved nonemptiness.

These are algebraic representative results. They assert no geometric
isogeny property, no existence of an integral action for an arbitrary
rational action, and no moduli representability.
