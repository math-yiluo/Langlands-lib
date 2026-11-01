# Properness on first-block determinant slices

Author: Worker 27.

This internal helper proves compact preimages for the actual first-block fiber
map when its domain is restricted to one determinant slice. It extracts the
first coordinate of the published mixed-subgroup homeomorphism, then passes
to the small left-unipotent quotient. Left multiplication by a block-unipotent
element leaves this quotient coordinate unchanged.

For a compact target set, the proof lifts it to a compact ambient set. If the
restricted preimage is nonempty, choose one representative `u0` of it. Every
other representative `u` in the same slice has norm-one ratio `u * u0⁻¹`.
Intersecting the compact lift, translated by `g⁻¹ * diag(u0,1)⁻¹`, with the
closed mixed subgroup gives a compact set whose quotient first coordinate,
right translated by `u0`, covers the preimage. The preimage is closed, hence
compact. The empty case is immediate.

This is derived topology for the existing JPSS Section 4.6 equation (6) data;
it asserts no disintegration identity.

If the small quotient measure is s-finite and finite on compact sets, the
pushforward formula and this properness result show that every kernel fiber
is finite on compact sets. The actual block quotient is Hausdorff, locally
compact and second countable. Its common countable compact cover therefore
proves `fiberKernel_isSFinite` by the published general kernel criterion.
