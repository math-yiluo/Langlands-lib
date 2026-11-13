# The combined binary quaternionic spin homomorphism

This internal construction combines the separately constructed SL₂ and
quaternionic norm-one homomorphisms into the same supplied spin cover. It retains
the explicit premise
`CentralSimpleUnits.DegreeTwoNormOneSimplyConnectedStatement`, asserting simple
connectedness of the actual norm-one groups of dimension-four central simple
algebras over fields.

The general theorem `FirstKindInvolution.IsSpinCover.commute_of_comp` applies
over a field `K` with a finite-dimensional division `K`-algebra, a first-kind
involution `σ`, a quadratic form `q` on a finite index type, and an arbitrary
supplied `π : S ⟶ σ.isometryGroup q` satisfying `σ.IsSpinCover q π`.
It says that two homomorphisms from connected reductive groups to `S` commute
on every test scheme if their composites with `π` commute on every test scheme.
The proof uses the central isogeny from `S` to the isometry identity component
supplied by `IsSpinCover`. Monomorphy of the identity-component inclusion permits
checking commutation there, and `commute_of_finiteKernel` then lifts commutation
to `S`.

In the namespace `BinarySpinLift`, `first_second_commute` proves that the two
factor inclusions into the actual product `SL₂ × SL₁(D)` commute on all test
schemes. The proof uses their coordinate formulas `(g,1)` and `(1,b)` and the
actual product point equivalence. `factor_decomposition` gives the corresponding
decomposition of every test point as the product of its two included coordinates.
Here `D` is central over `K`.

For the remaining constructions `K` is infinite, `D` has dimension four, the
symmetric subspace of `σ` has dimension three, and
`h : σ.IsHyperbolicPair q e f` is supplied. Simple connectedness of `SL₂` and
`SL₁(D)` is obtained from the explicit simple-connectedness premise using the
preceding lift module. Their ambient images commute because they arise from
the two product factor inclusions followed by
`AmbientBinaryScheme.isometryHom`. The general commutation theorem therefore
gives `specialLinear_normOne_commute` for the actual separately constructed
spin lifts.

The construction `productHom` is the resulting group-scheme homomorphism
`SL₂ × SL₁(D) ⟶ S`, using the existing
`commutingSubgroupMultiplicationHom`. On every relative test scheme its point
formula `productHom_points` is exactly the product of the separate lifted
coordinate points. The theorem `productHom_comp` identifies its composite
with the given `π` as `AmbientBinaryScheme.isometryHom`. The proof substitutes
the two separate composite identities and applies `factor_decomposition`.

Finally `productHom_ambient_points` computes the entire ambient matrix on every
test scheme `T` over `Spec K`: it is
`HyperbolicScheme.extendUnits h R` of
`BinaryScheme.pointMatrix σ hdim hsym T z`, where
`R = BinaryScheme.coefficients T` has its structural `K`-algebra structure.
The formula follows directly from the composite identity and the ambient
binary action formula.

All constructions allow arbitrary characteristic. Their provenance is internal:
they combine the existing separate lifts, finite-kernel commutation, actual
product point equivalence, and multiplication of commuting homomorphisms.
The module constructs the combined lift and its action formulas. It supplies
no injectivity statement for the combined lift and no elementary-generation
theorem.
