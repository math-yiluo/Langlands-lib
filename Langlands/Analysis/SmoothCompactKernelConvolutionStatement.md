# Smooth compact group kernels and continuous Banach-valued functions

Worker116 states the internal target
`Langlands.Analysis.SmoothCompactKernelConvolutionStatement`. This file defines
one proposition and contains no proof.

Let `G` be a locally compact Hausdorff topological group with the specified real
smooth Lie-group structure, modelled on the real normed space `V`. Let its
measurable structure be Borel and let `μ` be any measure finite on compact sets.
Let `E` be a complete complex normed space, `w : C(G,E)` be continuous, and
`κ : G → ℂ` be real manifold smooth with compact topological support. The target
asserts integrability for each `p` and real manifold smoothness of the literal
function

`p ↦ ∫ y, κ(y⁻¹ * p) • w(y) ∂μ`.

The group, its model and the Banach target have three independent universes.
Smoothness on `E` uses the real scalar action obtained from its complex action.
The original group operations, topology, charts, measure, function and kernel
are retained. No finite-dimensional model, second-countability, separability,
smoothness or global integrability of `w`, invariant measure, nonzero measure or
unitarity hypothesis is imposed. Local compactness and compact finiteness are
explicit structural assumptions. This is a smoothing statement about continuous
functions; it assumes no smoothness conclusion for the integral.

## Internal proof route and dependencies

This source-free target is an internal consequence of compact manifold
weighted integration. For a fixed parameter `p₀`, choose a compact neighborhood
`D` of `p₀`. If `p ∈ D` and `κ(y⁻¹*p) ≠ 0`, then
`y ∈ D * (tsupport κ)⁻¹`. This is a common compact integration set `K` for all
such parameters. The original measure restricted to `K` is finite. Its comap to
the compact subtype gives a finite Borel integration source, with the original
continuous function restricted as the Banach-valued weight.

The scalar function `(p,y) ↦ κ(y⁻¹*p)` is jointly manifold smooth by the original
Lie-group operations. Compact manifold weighted integration therefore makes
the integral over fixed `K` smooth. The subtype integral equals the integral
restricted to `K`; vanishing off `K` identifies that function with the literal
original integral on the neighborhood `D`. Manifold smoothness is local, so the
original function is smooth at `p₀`. Pointwise integrability separately follows
from continuity and compact support of the actual integrand.

This is a proof plan. The common support set, compact restriction, measure
identities and local equality must be proved in an exact-target proof. The
manifold weighted-integral target is itself a separately staged statement;
neither that definition nor an unreviewed private proof is accepted proof
input. This statement file imports only public Mathlib interfaces.

## Application boundary

For an actual continuous isometric representation, `w(y)` may be the orbit of an
original vector. The displayed convolution has not yet been identified with the
orbit of the corresponding integrated vector: the Haar change of variables and
representation action/integral comparison remain separate obligations. No
smooth-vector density, approximate identity, GH6.1 tensor realization, decay,
trace or spectral assertion follows from this statement publication.
