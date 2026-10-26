# Bundled transport of Whittaker functionals to the smooth dual

This internal adapter packages the published construction
`explicitSmoothDualFunctional` into the published GL Whittaker-functional
submodules. It constructs no Gelfand–Kazhdan equivalence and assumes no
multiplicity-one assertion.

Let `F` be a commutative topological ring, let the matrix rank be `n + 1`, and
let `rho` act on a complex vector space `V`. The field/ring carrier and `V`
have independent universes. For a bundled unitary additive character `psi`,
supply an actual complex linear equivalence

`E : V ≃ₗ[ℂ] SmoothDual rho`

and its equivariance law

`E (rho (inverseTranspose (n + 1) F g) v) = smoothContragredient rho g (E v)`.

The construction `smoothDualFunctionalTransport psi rho E hE` is the complex
linear map from `glFunctionals psi n rho` to
`glInverseFunctionals psi n (smoothContragredient rho)` defined by

`ell ↦ (phi ↦ ell (rho (weylLong (n + 1) F) (E.symm phi)))`.

Its underlying algebraic functional is exactly
`explicitSmoothDualFunctional rho E ell.val`. The output functional itself
is not assumed to be a smooth vector; its domain is the actual smooth dual.
No topology on `V`, admissibility or irreducibility hypothesis is required.
Rank one is included by `n = 0`.

The membership proof first pulls the smooth-dual action back through `E.symm`
using the supplied equivariance. It then applies the covariance of the
published `dualFunctional`, which is long-Weyl translation of `ell` for the
inverse-transpose pullback representation. That construction already proves
that the standard character becomes its inverse. The new map is linear by
pointwise linearity in `ell`; both displayed evaluation laws are definitional.
Nonvanishing follows from the published
`explicitSmoothDualFunctional_ne_zero`, using invertibility of `E` and the
long-Weyl involution.

The provenance is this elementary restriction of existing Library
constructions (`GenericDualTransport`, `DualTransform`, `GeneralLinear` and
the actual smooth-contragredient definitions). There is no new literature
claim. Existence of the supplied equivariant `E`, distribution invariance and
Whittaker multiplicity one remain separate proof obligations.
