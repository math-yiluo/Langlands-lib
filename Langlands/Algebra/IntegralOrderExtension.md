# Unique rational extension of homomorphisms from a full integer order

This is an internal construction from Mathlib's basis extension for a lattice,
integer-linearity of unital ring maps, and bilinearity of multiplication.
No external geometric result is used.

Let `A` be a unital rational algebra and let `O : Subalgebra ℤ A` be a full
integer lattice in `A`, in the sense of `Submodule.IsLattice ℚ O.toSubmodule`.
Given an integer basis `b : Basis I ℤ O`, Mathlib's `b.extendOfIsLattice ℚ`
is a rational basis of `A` whose vectors are the images of the same `b_i`.
The target `R` is another unital rational algebra. Neither algebra need be
commutative.

For an arbitrary unital ring map `f : O →+* R`, `linear b f` is the
rational-linear map defined by these basis values. Restriction of this map to
the order, considered as an integer-linear map, agrees with `f` on each basis
vector. Basis extensionality proves `linear_coe` on every order element.
This applies in particular to the unit and to every product of basis vectors.
Equality of the multiplication bilinear maps can therefore be checked on both
basis variables, proving `linear_map_mul`. `extend b f` packages the result as
an actual rational algebra homomorphism.

`extend_coe` states that the extension agrees with `f` on the entire order.
`algHom_ext` proves that rational algebra maps agreeing on this order agree on
all of `A`, by extensionality on the extended rational basis. Consequently
`extend_unique` proves uniqueness, and `equiv` gives inverse restriction and
extension operations between `O →+* R` and `A →ₐ[ℚ] R`.
`extend_basis_independent` proves independence of the chosen integer basis.
`extend_natural` proves compatibility with every rational algebra homomorphism
of target algebras.

The codomain `R` in this equivalence is already a rational algebra. In
particular, this result does not assert that a rational endomorphism action
takes values in an actual integral endomorphism ring. It does not construct
an isogenous integral representative, a quotient, or a moduli scheme.
