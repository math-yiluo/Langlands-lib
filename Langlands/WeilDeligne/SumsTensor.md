# Binary sums and tensor products of pairs

Worker 17 authored this construction module. It imports
`Langlands.WeilDeligne.Basic` and `Langlands.Weil.Representation.SumsTensor`.

For two pairs with the same coefficient field, group and norm character,
`sum A B` has the product carrier, componentwise action, and componentwise
monodromy. Given nilpotence exponents `m` and `n`, exponent `m+n` kills
both components. The proof transports this fact through Mathlib's
product-endomorphism ring homomorphism. Covariance holds componentwise.

`tensor A B` has the tensor carrier, diagonal group action, and the exact
monodromy formula `N tensor 1 + 1 tensor N'`. The two summands commute.
Each is nilpotent because its powers are the tensor maps of the
corresponding powers, so the sum is nilpotent by Mathlib's commuting
nilpotent-sum theorem. Covariance expands into two terms; the original
covariance equations and cancellation of the group inverse actions
give the same norm character on both terms. The proof does not assume
semisimplicity or characteristic zero.

`sumMap` and `tensorMap` use the actual sum and tensor of the linear
intertwiners and prove their monodromy squares. `sumFunctor` and
`tensorFunctor` prove the bifunctor laws. Transport of product
isomorphisms gives `sumEquiv` and `tensorEquiv`, which certify the
quotient operations `sumClass` and `tensorClass`.

These algebraic constructions allow arbitrary finite ranks including
zero, independently universed carriers, and nonzero monodromy. They
do not assert preservation of an unstated topology or inertia predicate.
Open-inertia subtype constructors for these operations are not part of
this module; they belong to a separate later parameter-operations
contribution. Other preservation statements remain separate theorem work.

Source correspondence: Tate, *Number theoretic background*, Corvallis
Part II, printed page 20, §4.1.5 explicitly gives the tensor monodromy
formula. Binary sums use the componentwise pair construction from
§4.1.2. Nilpotence, covariance, map, functor and quotient fields are
proved as intrinsic obligations, not included as unproved assumptions.
Source ID `tate-1979-number-theoretic-background`; retained Part II PDF
SHA-256 `c890894fe19783890cc4def2c5bf92a18d71619acf8ba7005aefce4984fe70d6`.
