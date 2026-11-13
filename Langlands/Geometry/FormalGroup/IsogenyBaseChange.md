# Base change of affine isogenies and scalar divisibility

This module proves preservation under an arbitrary O-algebra homomorphism
φ : R → S of the affine point-functor conditions defined in `FiniteKernel`
and `PiDivisible`. R, S, and the test and kernel algebras share one
universe; O may lie in another universe.

`coefficientLiftAlgebra φ A B ψ` equips an R-algebra B lying over the
restricted S-algebra A with the S-action S → A → B. The accompanying
`coefficientLiftMap` is ψ as an S-algebra map. Both constructions retain
the original underlying ring and ring homomorphism.

`Hom.IsFppfLocallySurjective.map` constructs the required lift. For an
S-algebra A and a point y of the target, first view A as an R-algebra
and use `coefficientPointEquiv` to regard y as a point of the original
target. The original lifting condition supplies an R-algebra B, a
faithfully flat finitely presented map ψ : A → B, and a lifted point x.
Equip the same underlying B with its S-algebra structure through
S → A → B. Then ψ is an S-algebra map with the same underlying ring
homomorphism, so faithful flatness and finite presentation are unchanged.
The R-structural map of B equals the composite R → S → B by the
R-linearity of ψ. Composition of coefficient maps therefore identifies
the new formal-map evaluation at x with the original evaluation.
The lifted point satisfies the required equation.

`Hom.IsIsogeny.map` combines this lifting construction with the tensor
construction of the actual finite kernel in `FiniteKernelBaseChange`.
`Hom.HasHeight.map` also uses that construction's stalk-rank pullback.
Thus an isogeny of constant kernel rank q^h retains that height after
coefficient extension.

`scalarHom_map` proves that coefficient extension commutes with the
scalar endomorphism, using O-linearity of coefficient extension on Hom
and preservation of the identity. `IsPiPowerTorsion.map` transports the
annihilating scalar-power equation through the actual O-linear point
equivalence. `IsPiDivisible.map` combines this with preservation of
nilpotence under φ, scalar affine lifting, and all scalar-power finite
kernels. `HasPiHeight.map` additionally transports every prescribed
scalar-power rank q^(n*h).

The provenance is internal: these are direct consequences of the actual
point comparison, tensor kernel construction, and the existing affine
isogeny and scalar-divisibility definitions. This module proves no
converse, descent, comparison with a sheaf-theoretic isogeny condition,
height additivity, rational height construction, local gluing, or
moduli representability.
