# The canonical polynomial-action exact sequence

This is an internal construction from Mathlib's polynomial modules, tensor
products and short complexes of modules. Let `R : Type u` be any commutative
ring. Let `M : Type v` be an additive commutative group with specified `R` and
`R[X]` module structures and `IsScalarTower R R[X] M`. The universes are
independent. There is no finiteness, domain or Noetherian hypothesis.

The entry definition `polynomialActionShortComplex` is the actual complex

```text
PolynomialModule R M --difference--> PolynomialModule R M --evaluation--> M
```

in `ModuleCat R[X]`. The polynomial variable in the induced modules shifts
coefficients, while its action on the final module is the specified action.
`polynomialActionShortComplex_shortExact` proves this complex is short exact.

The map `polynomialCoefficientAction` applies the specified action of `X` to
each coefficient; Mathlib's compatibility of coefficientwise maps with the
polynomial action makes it `R[X]` linear. The map
`polynomialActionDifference` subtracts that coefficientwise action from
multiplication by the polynomial variable. On a coefficient monomial it is

```text
single n m |-> single (n + 1) m - single n (X • m).
```

The map `polynomialActionEvaluation` uses the tensor-product identification
`R[X] ⊗[R] M ≃ PolynomialModule R M` and the base-change lift of the identity
on the restricted `R` module. It sends `single n m` to `X^n • m`. Thus it
respects the given action on `M`. Polynomial-module induction and this
monomial formula prove that evaluation annihilates every difference.

For injectivity, the coefficient of degree `n + 1` in the difference of `p`
is `p.coeff n - X • p.coeff (n + 1)`. If a nonzero `p` had zero difference,
choose the largest index `d` in its finite coefficient support. The coefficient
at `d + 1` would then be the nonzero coefficient at `d`, a contradiction.
This proves `polynomialActionDifference_injective`.

For exactness, induction on `n` shows
`single n m - single 0 (X^n • m)` is in the difference map's range. The
successor step adds the difference of `single n m` to the preceding relation
for `X • m`. Additive induction then proves
`polynomialActionEvaluation_remainder_mem_range`: for every `p`, the element
`p - single 0 (polynomialActionEvaluation p)` lies in that range.
If evaluation of `p` is zero, this gives `p` itself in the range. Together
with annihilation, it proves `polynomialActionDifference_range_eq_ker`.
Evaluation is surjective because it sends `single 0 m` to `m`.
These three results establish short exactness of the displayed actual complex.

This construction is intended as infrastructure for later polynomial
dimension arguments. It asserts no projective-dimension bound, polynomial or
smooth-algebra coherence, or scheme-level line-bundle extension.
