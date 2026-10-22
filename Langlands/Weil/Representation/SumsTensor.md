# Binary sums and tensor products

Worker 17 authored this construction module. It imports the published
`Langlands.Weil.Representation.Basic` foundation at Library commit
`843c574c920aa9926ab56adf662c74b3cd4ed0e1`.

`sum A B` realizes the binary direct sum on the actual product carrier
`A × B`; `tensor A B` uses the actual tensor product over the coefficient
field with the diagonal group action. Both reuse Mathlib's existing
representation constructors and finite-module instances.

`sumMap` is the product of the underlying linear maps, with equivariance
proved componentwise. `tensorMap` uses Mathlib's intertwiner tensor
product. `sumFunctor` and `tensorFunctor` are functors from the product
category. Their identity and composition equations are proved on vectors
and pure tensors respectively. Applying these functors to product
isomorphisms gives `sumEquiv` and `tensorEquiv`. Those equivalences supply
the well-definedness proofs of `sumClass` and `tensorClass` on genuine
isomorphism classes.

No topology, semisimplicity, or positive-rank hypothesis is imposed.
Zero-dimensional carriers are supported. The coefficient, monoid and
carrier universes are explicit; both output carriers use the maximum
of the two input carrier universes. The linear map constructors also allow independent
source and target carrier universes.

These are the ordinary representation operations underlying the pair
operations in Tate, *Number theoretic background*, Corvallis Part II,
printed page 20, §§4.1.2 and 4.1.5. The categorical and quotient laws are
intrinsic algebraic implementation proofs. Source ID
`tate-1979-number-theoretic-background`, retained PDF SHA-256
`c890894fe19783890cc4def2c5bf92a18d71619acf8ba7005aefce4984fe70d6`.
The pinned Mathlib implementations are `Representation.prod`,
`Representation.tprod`, `Representation.IntertwiningMap.tensor`, and
the tensor-product finiteness instances, at commit
`5ed2965256430c3649e86755f9576b54eca72435`.
