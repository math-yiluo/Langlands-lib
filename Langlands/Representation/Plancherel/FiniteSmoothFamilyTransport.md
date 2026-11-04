# Coordinate and coefficient changes of finite smooth families

Author: Worker 200.

These are internal algebraic and calculus prerequisites for the coordinate
and base comparisons of Waldspurger, *La formule de Plancherel pour les
groupes p-adiques (d'après Harish-Chandra)* (2003), VI.1, printed
pages 295–296 (PDF pages 61–62). The source uses smooth scalar functions
on the unitary character torus and their algebraic tensor product with the
compact coefficient space. It does not state the generic transport lemmas
in this module separately.

The implementation imports `RationalOrbitBasisInvariance` for integer
monomials and character reconstruction in different integer bases, and
`SmoothTensorFamilies` for the actual finite-sum smoothness condition.
It extends those published scalar constructions to arbitrary complex
coefficient modules.

## Parameters and the finite-sum convention

`J : Type uJ` and `K : Type uK` are independent finite index types.
`V : Type uV` and `W : Type uW` are additive commutative groups with
complex module structures. There is no topology, norm or
finite-dimensionality premise on either coefficient module.

A function `F : (J → Circle) → V` belongs to `finiteSmoothFamilies J V`
precisely when it has a finite expansion

\[
  F(z)=\sum_{i<n} f_i(z)v_i
\]

with `f_i : smoothFiniteTorusFunctions J` and fixed `v_i : V`.
Scalar smoothness means real infinite differentiability after composition
with `finiteTorusExp`. Every transport proof works directly with this
finite expansion using `mem_finiteSmoothFamilies_iff`.

## Integer monomials and bases

`mem_finiteSmoothFamilies_comp_monomial` precomposes each scalar
coefficient by the existing integer Laurent monomial
`finiteTorusMonomial a`, for `a : J → K → ℤ`. Scalar smoothness of
the new coefficients follows from
`IsSmoothFiniteTorusFunction.comp_monomial`. That imported theorem
uses the explicit smooth real linear lift of the monomial.

Let `L : Type uL` be an additive commutative group with its displayed
integer module structure, and let `b : Basis J ℤ L` and
`c : Basis K ℤ L`. The existing `finiteTorusBasisChange b c`
reconstructs the same circle-valued lattice character from its values on
`b` and evaluates it on `c`. Its coordinates are

\[
  T_{bc}(z)_k=\prod_j z_j^{b.\operatorname{repr}(c_k)_j}.
\]

`finiteTorusBasisChangeMulEquiv b c` packages this map as a
multiplicative equivalence. Both inverse identities reuse
`finiteTorusBasisChange_inverse`; multiplicativity follows from the
Laurent formula, multiplicativity of integer powers and of finite
products. Its application and inverse-application theorems give the
literal maps `T_bc` and `T_cb`.

`mem_finiteSmoothFamilies_comp_basisChange_iff` proves

\[
 F\circ T_{bc}\in\mathrm{finiteSmoothFamilies}(J,V)
 \quad\Longleftrightarrow\quad
 F\in\mathrm{finiteSmoothFamilies}(K,V).
\]

One direction precomposes by the forward integer monomial; the other
precomposes by the inverse monomial and uses the inverse identity.
This argument covers finite integer lattice bases. It makes no assertion
about arbitrary abstract group isomorphisms of tori.

## Translation and coefficient transport

`mem_finiteSmoothFamilies_mul_const_iff` proves equivalence of
membership for `F` and `z ↦ F(z*c)`. It translates each smooth scalar
coefficient using the published scalar translation theorem. The reverse
direction translates by `c⁻¹`.

`mem_finiteSmoothFamilies_linearMap` applies a fixed complex linear
map `T : V →ₗ[ℂ] W` to each constant coefficient vector. Linearity
commutes with the finite sum and scalar multiplication.
`mem_finiteSmoothFamilies_linearEquiv_iff` applies this construction
to a linear equivalence and its inverse, proving preservation and
reflection of membership. These are algebraic statements about finite
scalar-smooth families; they do not impose a manifold smoothness
notion on the coefficient module.
