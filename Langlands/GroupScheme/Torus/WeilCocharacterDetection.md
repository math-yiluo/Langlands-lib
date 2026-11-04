# Detection of finite-Galois cocharacter transfer

Let `k` and `K` be fields in an arbitrary common universe, with a
`k`-algebra structure on `K`. Let `Z` be a commutative group scheme over
`Spec k` whose underlying scheme is affine. Write `Z_K` for its actual
scheme base change. For a finite Galois extension `K/k`, this module proves
that an actual cocharacter `nu : Gm_K ⟶ Z_K` is zero whenever the actual
morphism `WeilGm.cocharacterTransfer k K Z nu : Res_{K/k}(Gm) ⟶ Z`
is zero. Consequently every nonzero cocharacter has nonzero transfer.
No smoothness, finite type, characteristic, perfectness or cardinality
hypothesis is imposed on `Z` or on the fields.

## Tensor embedding coordinates

For a commutative `K`-algebra `A`, with its compatible `k`-algebra structure,
`transferCoordinate tau` maps `c tensor a` to `tau(c) * a`, using the scalar
map from `K` to `A`. The map `transferMultiply` is `K`-linear and restricts
to the coordinate for the identity embedding. These definitions require
neither finiteness nor the Galois hypothesis.

For finite Galois `K/k`, `transferUnitsEquiv` uses the canonical embedding
decomposition of `K tensor_k A` and the equivalence between units of a
product and products of units. Its value at each embedding is the unit map
of `transferCoordinate`. The unit `identitySupportedUnit t` is defined by
inverting this equivalence on the tuple that is `t` at the identity
embedding and `1` at every other embedding. The coordinate formula holds
for every commutative `K`-algebra `A`, including nonreduced algebras.

## Recovering a cocharacter value

Suppose an automorphism `sigma` of `K/k` extends to a semilinear
`k`-algebra automorphism `q` of `A`. The map
`untwistedTransferCoordinate q` sends `c tensor a` to `c * q.symm(a)`
and is `K`-linear. Composing its scalar restriction with `q` gives
`transferCoordinate sigma`. Naturality of the actual cocharacter therefore
implies that its point value maps to `1` in this coordinate whenever the
tensor unit has coordinate `1`.

`transferPoint_eq_prod_coordinates` applies the multiplication coordinate
to the extension formula for the tensor-valued norm. It identifies the
transfer point with the product of all embedding-coordinate point values.
If every automorphism of `K/k` has a compatible semilinear lift to `A`,
`transferPoint_identitySupportedUnit` evaluates this formula on the unit
supported at the identity: all other factors are `1`, and the identity
factor is exactly `cocharacterValue nu A t`.

Every automorphism has such a lift on `A = LaurentPolynomial K`: apply it
to each coefficient. `laurent_semilinear` constructs this lift with
`AddMonoidAlgebra.mapAlgEquiv`; it needs neither a finite nor a Galois
extension. `transferPoint_identitySupportedLaurentUnit` specializes the
recovery formula to this Laurent algebra.

## Detecting the actual morphism

`transferPoint_eq_one_of_transfer_eq_zero` uses the published affine-point
formula and the source corepresentation to show that a zero transfer takes
every tensor unit to `1`, over every commutative `k`-algebra. Applying this
to the identity-supported unit built from the universal Laurent coordinate
shows that the original cocharacter has value `1` at the universal
multiplicative point. The actual base-change point equivalence is
injective, and `Gm.hom_ext_universalPoint` then gives `nu = 0`.
This proves `cocharacter_eq_zero_of_transfer_eq_zero`; its contrapositive
is `cocharacterTransfer_ne_zero`.

This is internal infrastructure derived from tensor embedding
decomposition, the constructed tensor norm, actual cocharacter naturality,
and affine corepresentation. It is not a proof of the arbitrary-field
no-torus unipotence theorem. In particular, no finite field of definition
for a cocharacter over an infinite algebraic extension is constructed here.

The local instances have explicit module-specific names to avoid generated-name
collisions when these developments are imported together. Their types, bodies
and local scope are unchanged.
