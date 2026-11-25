# Uniform scalar torsion on represented kernels

This module supplies two elementary inputs to the construction of
integral scalar-power dual isogenies for the local quasi-isogeny inverse
problem. It uses actual formal-module points on all coefficient
algebras and the existing affine fppf lifting condition.

The coefficient ring O and the base O-algebra R are commutative rings.
Their universes may differ. The coordinate types are finite, and the
distinguished scalar pi is arbitrary. Test algebras are in the universe
of R, as in the finite kernel model and scalar-divisibility definitions.

`Hom.exists_pow_kills_kernel_of_corepresentable` assumes that the source
formal module is scalar-power torsion and that the actual kernel point
functor is corepresented by a coefficient algebra. Apply torsion to the
universal kernel point corresponding to the identity algebra map.
Every other kernel point is its image under the algebra map obtained
from the corepresenting equivalence. Naturality and linearity of this
point map show that the same scalar power kills every such point.
The argument uses corepresentability alone; finiteness and projectivity
of its algebra are not needed.

The specialization
`HasFiniteLocallyFreeKernel.exists_eventually_pow_kills` applies this
argument to an actual finite kernel model and observes that every
larger power also kills the kernel. The isogeny specialization
`IsIsogeny.exists_eventually_pow_kills_kernel` obtains the torsion
hypothesis from the source's scalar divisibility.

`IsFppfLocallySurjective.right_of_comp` uses a lift through a composite
to produce a lift through its left factor on the same faithfully flat,
finitely presented extension. Consequently, an actual map g with
g composed with f equal to a source scalar power has affine fppf
local lifting whenever that source is scalar divisible.

These lemmas construct neither the integral dual map nor a finite
kernel model for it. They establish the common kernel annihilator
and the lifting part that such a dual map will satisfy. Their
provenance is internal point-functor algebra needed by the published
`LocalQuasiIsogenyInverseStatement`, rather than an external source
quotation.
