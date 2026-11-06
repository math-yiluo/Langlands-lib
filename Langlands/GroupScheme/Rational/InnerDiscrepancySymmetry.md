# Symmetry of actual inner discrepancies

This internal construction proves symmetry of actual inner discrepancies.
It first works over an arbitrary scheme `S` in universe `u`, with group
schemes `G`, `H`, `A`, `B`, a cover object `U`, local families
`e : LocalGroupIso G H U` and `d : LocalGroupIso A B U`, and actual
automorphic actions `a` of `A` on `G` and `b` of `B` on `H`.
The equivariance input is the equality

```text
e(c)(a(x, g)) = b(d(c)(x), e(c)(g))
```

for every relative test scheme, cover point `c`, acting point `x` and group
point `g`. The fields of `LocalGroupIso` retain naturality on every relative
test and actual multiplicative equivalences of its group-valued points.

`LocalGroupIso.RepresentsDiscrepancy.symm_of_equivariant` proves that a
representing point `x` for `e` at cover points `c,c'` gives a representing
point `d(c)(x⁻¹)` for `e.symm` at the same ordered pair. The existing
representation predicate includes every further refinement of the test
scheme. At a refinement `t`, naturality of `d` and preservation of inverses
identify the pullback of `d(c)(x⁻¹)` with
`d(t followed by c)((t followed by x)⁻¹)`.

The proof applies the injective equivalence `e(t followed by c)` to the
desired inverse discrepancy equation. The forward discrepancy equation,
evaluated at `e(t followed by c')⁻¹(h)`, expresses `h` as

```text
e(t followed by c)(a(t followed by x, e(t followed by c')⁻¹(h))).
```

Substituting this expression into the target action and using equivariance
reduces the equation to the inverse-action law
`a(x⁻¹, a(x, g)) = g`. This verifies the claim on all refinements.

`HasInnerDiscrepancy.symm_of_equivariant` applies that construction to the
representing point supplied for each ordered pair of cover points. When `b`
is faithful on all refinements, `innerCocycleSymm` applies the existing
canonical-cocycle constructor to the inverse family's innerness. The
constructor derives naturality and the cocycle identity from uniqueness;
neither is an additional input here.
`innerCocycleSymm_hasDiscrepancy` supplies the actual discrepancy equation.
If `a` is also faithful, `innerCocycleSymm_toFun` identifies each value as
`d(c)(ξ(c,c')⁻¹)`, where `ξ` is the forward canonical cocycle. This comparison
uses uniqueness of representing points for `b` and the first symmetry lemma.

The `IsAdjointQuotient` section specializes these constructions to arbitrary
same-universe fields `k`, `K` and a `k`-algebra structure on `K`. It takes
supplied full-centre adjoint quotient maps `q : G ⟶ A`, `p : H ⟶ B`, and a
local family `e` over `Spec K → Spec k`. The induced family
`hq.localIso hp e` supplies `d`; its proved actual inner-action equivariance
supplies the equivariance input. Thus `hasInnerDiscrepancy_symm` needs only
forward innerness as its additional input. Faithfulness of the actual
adjoint inner action supplies the hypothesis for `symmInnerCocycle`.
The associated discrepancy theorem and all-test value formula are the
specializations described above.

The provenance is internal: the module combines the existing
all-refinement discrepancy predicate, canonical cocycle construction,
actual induced adjoint local family and inverse-action laws. No new
external structural result is asserted. The supplied-quotient hypotheses
do not construct the initial quotient, quasi-split model or inner local
isomorphism required by unconditional quasi-split inner-form existence.
