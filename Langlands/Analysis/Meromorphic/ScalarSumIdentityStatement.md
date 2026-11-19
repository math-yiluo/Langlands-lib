# Scalar meromorphic identity with a finite sum in changed coordinates

`Langlands.Analysis.Meromorphic.ScalarMeromorphicSumIdentityStatement` uses
meromorphy in linear coordinates from `LinearCoordinates`. Let `e : X ≃ₗ[ℂ] Y`
be a complex linear equivalence. A scalar meromorphic function `f` on `X` has
holomorphy domain `U`. The finitely many scalar coefficients `coeff i` on `X`
have common domain `V`, and the scalar functions `g i` on `Y` have common
domain `W`. If

`f (c x) = ∑ i, coeff i (c x) * g i (e (c x))`

on a nonempty open set in one linear chart `c` of `X`, the same equality
holds in the original parameters throughout `U ∩ V ∩ e ⁻¹' W`. The sum may
be empty, in which case the hypothesis says that `f` vanishes on the open
patch and the conclusion gives vanishing throughout the requested domain.

This derived statement isolates the scalar continuation argument for
Bernstein–Lapid, *On the meromorphic continuation of Eisenstein series*,
Theorem 2.3 (4). It uses the local holomorphic denominator notion in §3.1,
after evaluating a family of functions at a fixed point. The chart and
linear equivalence allow use of that notion on character-parameter spaces.
Agreement on an open patch is a hypothesis. In the Eisenstein application
this agreement requires the automorphic comparison in §8.6.
