# Scalar rigidity of root parametrizations over arbitrary rings

This is derived internal content for the arbitrary-local-ring Isomorphism
Theorem. It combines natural operations on coefficient algebras, polynomial
substitution, the actual root-subgroup representation, and the all-test
conjugation law in `LocalSplitCell.IsRootParametrization`. It does not appeal
to the Isomorphism Theorem or to equality detection by field points.

All rings, index types and schemes retain universe `u`. The generic results
require only a commutative base ring. The final root-datum specialization
requires a local ring and an affine ambient group, as required by the
existing `IsFibrewiseRootDatumOf` interface. There is no reducedness,
noetherian, henselian or characteristic assumption.

## Natural operations and positive Laurent weights

`NaturalLine.Operation R` is a family of functions on commutative
`R`-algebras, natural under algebra homomorphisms. Additivity is not part of
this definition. `powerEvaluation d` is the algebra homomorphism from
`R[X]` to `LaurentPolynomial R` sending `X` to `T^d`.
`powerEvaluation_injective` proves injectivity for a positive natural
integer `d` by factoring it through polynomial expansion and the standard
injective map from polynomials to Laurent polynomials.

`Operation.eq_mul_of_laurent` says that a natural operation `F` is
multiplication by `F_R(1)` if

```
F_(R[T,T^-1])(T^d) = T^d * C(F_R(1)).
```

For its proof, put `P = F_(R[X])(X)`. Naturality under substitution
`X -> T^d` and its injectivity imply `P = C(F_R(1)) * X`. Naturality under
`X -> a` then proves the claimed formula on every coefficient algebra and
every element. This is an exact polynomial argument over the original ring.

## From additive-group maps to scalar multiplication

`LocalSplitCell.scalarOperation q` sends a coefficient `a` to the coordinate
of the point obtained by applying `q : Ga R -> Ga R` to the scalar point
with coordinate `a`. Its naturality follows from the naturality of the
canonical global-sections isomorphism for `Spec A` and of vector-group
coordinates.

`eq_scaleHom_of_scalarOperation` proves that a multiplication formula for
this operation on all coefficient algebras determines `q = scaleHom c`.
It tests the formula on the coordinate of the identity point over the
coordinate algebra of `Ga R`, and then uses vector-group point extensionality.
`gamma_baseScalar` computes a base scalar over `Spec A`.
`scalarOperation_scaleHom` computes the operation of an existing scaling
map, and `scaleHom_injective` tests this computation at one over `R`.

`exponentValue_laurent` evaluates the torus point with coordinates
`(T^1)^(nu j)` under the character with exponent vector `m`. Its value is
exactly `T^(sum_j m j * nu j)`, including negative exponents.

`exists_scaleHom_of_weight` applies the natural-operation argument to an
endomorphism commuting, on every scheme test, with the character action
of `m`. Its hypotheses include a cocharacter exponent vector `nu` and a
positive natural integer `d` with integer dot product `m * nu = d`.
Evaluating equivariance at the preceding Laurent torus point and parameter
one gives the required Laurent-weight identity. Naturality along the
structure homomorphism from `R` identifies the value at one with the image
of its base-ring value. The conclusion is `q = scaleHom c` for some `c : R`.
Neither locality nor a unit hypothesis on `d` is used.

## Comparison of actual root parametrizations

`IsRootParametrization.exists_scalar` compares two actual parametrizations
`u` and `v` of the same root subgroup with the same torus character. It
requires the preceding positive integer pairing. Their representation
properties give an isomorphism `e : Ga R ≅ Ga R` with `e.hom >> v = u`.
Cancelling the monomorphism underlying `v` in the two all-test conjugation
identities shows that `e.hom` commutes with the character action.
`exists_scaleHom_of_weight` therefore gives

```
u = scaleHom c >> v.
```

`IsRootParametrization.scaleHom_comp_injective` proves that composing a
scaling map with a root parametrization detects its scalar, by cancellation
of the represented monomorphism and `scaleHom_injective`.
`IsRootParametrization.existsUnique_unit` applies scalar comparison in both
directions. The composition identity for scaling maps and this injectivity
give `c * b = 1`; commutativity supplies the other inverse identity. Thus
there is a unique unit `c : Rˣ` with the displayed comparison formula.

`IsRootParametrization.existsUnique_unit_of_rootDatum` specializes this
result to a root `alpha` of an actual fibrewise root datum over a local
ring, with affine ambient group. The coroot supplies `nu`. The residue-field
pairing comparison in `IsFibrewiseRootDatumOf.pairing` and
`RootDatum.root_coroot_two` give the positive integer degree two. The integer
two is not inverted, so the result includes residue characteristic two.
`IsRootParametrization.comparisonUnit` selects this unique unit and
`comparisonUnit_spec` proves its exact comparison formula.

The module does not construct a Weyl-normalized opposite-root pair or glue
an isomorphism between two reductive groups. Those steps, and the full host
Isomorphism Theorem, remain separate proof obligations.
