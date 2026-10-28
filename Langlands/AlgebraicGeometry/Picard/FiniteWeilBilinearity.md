# Bilinearity of the actual finite Weil pairing

This internal adapter proves the dual-variable laws for the existing
`finiteWeilValue` and actual product-scheme morphism `finiteWeilPairing`.
It retains their quasi-separated base, actual abelian scheme `A`, chosen
dual witness, seven explicit dual-constructor propositions, and actual
inverse line bundle with tensor evaluation isomorphism. The parameter is
any natural number `n`, including zero. No new character, pairing, or
bilinearity hypothesis is supplied as data.

For every scheme `T` over the base, `dualTorsionCharacter_mul` proves
that the existing intrinsic character associated to `y * y'` in actual
dual `n`-torsion is the sum of the characters associated to `y` and `y'`.
The inverse of `relativeDualMultiplicationKernelIso` is a group-object
homomorphism, so composition with it preserves multiplication.
The proved `dualKernelPointCharacter_mul` then supplies the equation.
The identity law follows in the same way. These laws package the original
function as `dualTorsionCharacterAddHom`; preservation of negatives gives
the inverse law.

Applying `Cartier.muEvaluation_zero`, `Cartier.muEvaluation_add`, and
`Cartier.muEvaluation_neg` proves the unit, multiplication and inverse
laws of `finiteWeilValue` in its dual variable. Thus, in multiplicative
notation for group-object points,

```
e_n(x, y * y') = e_n(x, y) * e_n(x, y').
```

The existing point formula for the actual product-scheme morphism
transfers the unit and multiplication laws to `finiteWeilPairing` on
every test scheme. Together with its published primal-variable laws,
these are bilinearity laws for this particular scheme morphism.
`finiteWeilBilinearMap` packages exactly the same pointwise evaluation
as a curried additive homomorphism in both variables. Its additive
notation only changes the notation of the three groups of points.

The provenance is internal composition of the intrinsic dual-kernel
character additivity, the actual comparison of the dual multiplication
kernel with dual torsion, the root-valued Cartier evaluation laws, and
the representing pairing's point formula. The evaluation order remains
`beta(y)(x)` throughout. No roots of unity or Tate twist are trivialized.
This module asserts no effective descent, kernel-duality bijectivity,
Cartier-duality isomorphism, perfectness, polarization, alternation,
transition compatibility or inverse-limit pairing. Those are separate
obligations.
