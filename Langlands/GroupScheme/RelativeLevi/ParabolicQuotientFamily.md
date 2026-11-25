# Actual parabolic families on supplied homogeneous quotients

This is an internal construction from the actual conjugate-family and smooth
matching interfaces. Let `S` be an arbitrary scheme in universe `u`, let `G` be
reductive over `S`, and let `i : P ⟶ G` be an actual relative parabolic subgroup.
There is no affine-base or quasi-compactness restriction.

`conjugateParabolic hG i hi g` is the actual subgroup functor of the pullback of
`i` conjugated by a parameter `g : M ⟶ G.X`. Its relative parabolicity follows
from the published arbitrary base-change theorem and transport by the actual
inner automorphism. `restrict_conjugateParabolic` identifies its restriction
along any `a : T ⟶ M` with the conjugate family of `a ≫ g`, using exact
evaluation of the actual homomorphism.

Suppose `q : G.X ⟶ Q` is smooth and surjective and its fibers on every test
scheme satisfy: `g ≫ q = h ≫ q` implies `g⁻¹ * h` belongs to the full normalizer
of `range i`. The universal conjugate family on `G.X`, with parameter the identity,
is ordinary matching along `q`. Indeed, restriction gives the two conjugate
families, and the published full-normalizer invariance identifies their actual
subgroup functors. `quotientParabolic` applies effective smooth matching descent
to this family. `restrict_quotientParabolic` proves exact recovery along `q`.
`restrict_quotientParabolic_comp` then gives exact evaluation along `g ≫ q` for
every test scheme and every group-valued lift `g`, by functorial restriction.

`homogeneousQuotientParabolic` specializes this construction to any supplied
`HomogeneousQuotient i`. Its smooth and surjective projection has exact
right-coset fibers on all tests. A subgroup functor is contained in its full
normalizer, so those fibers meet the required normalizer condition. No
self-normalizer hypothesis is needed for this construction.

This module constructs an actual parabolic family on a supplied parameter scheme.
It does not construct that scheme, prove the parameterization injective or
surjective onto a local conjugacy type, or prove smooth proper representability
of the complete parabolic functor. Those are separate parts of the proof of
`RelativeParabolicSchemeStatement`, which `ParabolicSchemeProof` proves.
