# The reduction kernel in split dual-number units

This internal construction supports the direct rigidified deformation route.
It concerns units in the actual split rings `DualNumber R` for arbitrary
commutative rings `R`, without a field or nontriviality assumption.

The unit `1 + εa` is obtained by specializing the published
`GeneralLinear.DualNumber.matrixUnit` to rank one and applying Mathlib's
`Matrix.uniqueRingEquiv` to units. Thus the square-zero unit construction
and its multiplication law reuse the existing matrix result.

`reduction` is the map on scalar units induced by the actual augmentation
`TrivSqZeroExt.fstHom`. `Kernel R` is its group kernel.
`kernelEquiv` identifies the additive group of `R`, written multiplicatively,
with this actual kernel. The inverse extracts the second coordinate.
The inverse law uses the first-coordinate equality to one supplied by kernel
membership and extensionality of dual numbers.

`Coordinates.kernelMap` uses the published coefficient-change map on both
coordinates. It commutes with `kernelEquiv` and satisfies identity and
composition. `Coordinates.kernelScale` uses the published algebra map
`ε ↦ rε`; under `kernelEquiv` it is multiplication by `r`, including `r = 0`.
The proofs inspect the values of the actual units.

`kernelAddEquiv` expresses the same equivalence using additive notation for
the kernel. `kernelFunctor` sends commutative rings to these additive abelian
groups and sends ring maps to `Coordinates.kernelMap`. Its functor laws follow
from the coordinate identity and composition lemmas. `ringAdditiveFunctor`
is the composite of Mathlib's existing forgetful functors through `RingCat`.
The componentwise equivalences form `kernelFunctorIso`; its naturality is
exactly `Coordinates.kernelMap_equiv`.

For an actual scheme `X`, `kernelPresheaf X` applies `kernelFunctor` to every
structure-sheaf section ring and restriction map. `kernelPresheafIso X`
identifies this presheaf with the additive underlying presheaf of the actual
structure sheaf. The sheaf condition is transported through this isomorphism:
after forgetting the additive groups, the latter presheaf is definitionally
the underlying presheaf of types of `X`'s structure sheaf. Mathlib's sheaf
criterion for the forgetful functors proves `kernelPresheaf_isSheaf`.
`kernelSheaf X` bundles that presheaf with this proof.

This is a split section-ring construction and a sheaf of abelian groups.
It does not identify a scheme base change with a split ring presheaf and does
not prove a deformation classification, a derived cohomology comparison,
or a sheaf tangent comparison.
