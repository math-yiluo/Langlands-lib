# Separate binary quaternionic spin lifts

This internal construction gives homomorphisms into an arbitrary supplied
quaternionic spin cover and identifies their ambient matrices on every relative
test scheme. The binary constructions assume the proposition
`CentralSimpleUnits.DegreeTwoNormOneSimplyConnectedStatement`: simple connectedness
of the actual reduced-norm-one group of every central simple algebra of dimension
four over a field. That proposition remains an explicit premise throughout.

For a field `K`, a finite-dimensional division `K`-algebra `D`, a first-kind
involution `σ`, a quadratic form `q` on a finite index type, and a supplied
`π : S ⟶ σ.isometryGroup q` satisfying `σ.IsSpinCover q π`,
`IsSpinCover.existsUnique_liftHom` states that every homomorphism from an
algebraically simply connected group `C` to the isometry group has a unique
homomorphism lift to this same `S`. The proof factors the homomorphism through the
identity component using the connectedness included in simple connectedness.
It then uses `SimplyConnectedHomLift.liftHom` for the central isogeny supplied by
`IsSpinCover`. Cancellation through that central isogeny proves uniqueness.
`IsSpinCover.liftHom`, `liftHom_comp`, and `liftHom_unique` package the chosen
lift, its composite, and its uniqueness.

The namespace `BinarySpinLift` first transfers the stated simple-connectedness
premise to actual `SL₂` using
`CentralSimpleUnits.binaryMatrixNormOneIso` and the dimension-four computation
for the binary matrix algebra. The constructions `firstFactor` and `secondFactor`
are the actual group-scheme homomorphisms from `SL₂` and `SL₁(D)` to their product.
Their point formulas identify these inclusions with `(g,1)` and `(1,b)` on every
test scheme.

For the remaining constructions `K` is infinite, `D` is central of dimension
four, the symmetric subspace of `σ` has dimension three, and
`h : σ.IsHyperbolicPair q e f` is supplied. The maps `specialLinear` and `normOne`
lift these two factor inclusions followed by
`AmbientBinaryScheme.isometryHom`. Their composite identities are
`specialLinear_comp` and `normOne_comp`. The cocharacter `scalar` is
`SpecialLinear.BinaryRoot.upperCocharacter` followed by `specialLinear`;
`scalar_comp` computes its composite with the given `π`.

The theorems `specialLinear_points` and `normOne_points` compute the full ambient
matrix of each composite on any `T` over `Spec K`. In the section algebra
`R = BinaryScheme.coefficients T`, they are the previously defined
`HyperbolicScheme.extendUnits h R` applied to
`BinaryAction.normOneAction σ hdim hsym R (g,1)` and to the same action at `(1,b)`,
respectively. The coefficients use their structural `K`-algebra structure.

The theorem `diagonal_normOne_action` restricts the binary action to
`(diag(t,t⁻¹),b)` and identifies it with the hyperbolic Levi matrix
`diag(a,σ(a)⁻¹)`, where `a = normCoverScalarUnits K D R t * b.val`.
It follows from `BinaryAction.diagonal_action_eq_levi` and the proved
norm-one conjugation identity. Consequently `scalar_points` gives the extended
Levi matrix of the scalar unit, and `normOne_levi_points` gives the extended
Levi matrix of `b.val`. These formulas hold on all relative test schemes,
with unrestricted characteristic.

The provenance is entirely internal: the identity-component factorization,
central-isogeny homomorphism lifting, actual split norm-one comparison, ambient
binary action, diagonal cocharacter, and concrete Levi matrix identities are
imported Library constructions. The module proves these conditional lift and
action formulas. Determining the kernel of the combined lifted action and
proving elementary generation of the spin group's rational points remain
separate obligations.
