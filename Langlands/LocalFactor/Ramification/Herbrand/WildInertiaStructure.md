# Tame inertia quotient and mixed-depth ramification commutators

**Author:** Worker 5163.

This module supplies two finite ramification facts used in the scalar
upper-layer argument for Henniart (1988), Proposition 3.3(i). It concerns the
actual lower and upper groups of the Library, with independently universe-sized
base and extension. The finite inertia structure is that of Serre, *Local
Fields*, Chapter IV, §2 (uniformizer residue character and lower commutator
bound). The module does not yet assert a Weil representation acts by scalars.

## Tame quotient

`tameInertiaCharacter` packages the Library's uniformizer residue character
on the actual inertia group. For an irreducible element `ϖ` generating the
maximal ideal, the value on `σ` is the residue of the factor `u` with
`σ(ϖ) = ϖ * u`, regarded as a unit. The construction uses the published equality
of inertia with the zeroth lower group and the fact that a multiplicative
map out of a group takes unit values.

If the residue character takes value `1`, the automorphism moves `ϖ` by an
element of the square of the maximal ideal. The Library's residue Frobenius
argument then puts the automorphism in the first lower group. This kernel
inclusion suffices: the quotient of inertia by the first lower group is a
quotient of the image of the residue character. It is cyclic and its index
divides the order of the residue unit group. The additive order of `1` is
`p`, so `p` divides the residue field size, but not the size minus one. Thus
the index is coprime to `p`. The module does not need or assert equality of
the kernel with the first lower group.

## Mixed commutators

For two automorphisms at depths `i` and `j`, the difference of the two
compositions on `x` is the difference of their displacements on `g(x)-x`
and `f(x)-x`, respectively. Applying the Library's bound for displacement
on powers of the maximal ideal to each term gives depth `i+j` for the
commutator. The finite field version transports the bound along the
integer-ring automorphism of the inverse of `τ * σ`, yielding the
commutator in the convention `(τ * σ)⁻¹ * (σ * τ)`.

For an element of the upper group at `a > 0`, put `m = ⌈ψ(a)⌉`. Its
commutator with an element of the first lower group is in the lower group
at `m+1`. The upper index `φ(m+1)` for that lower group is strictly above
`a` by strict monotonicity of `φ` and `ψ(a) ≤ m`. This gives a mixed-depth
version of the published same-depth upper-group commutator bound.
