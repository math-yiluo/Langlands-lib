# Kernel, lifting, and naturality of the congruence–Lie homomorphism

The first four statements concern `congruenceLieHom` on a smooth affine
integral model over a commutative local domain. The model has fraction
field `K`, affine generic group `G`, and Lie lattice `L` in `Lie(G)`.
The levels are positive naturals satisfying `n ≤ m ≤ 2n`. Positivity
is part of the congruence tower and the upper bound is the square-zero
condition used to construct the map.

- `CongruenceLieInjectivityStatement` asserts that the kernel is exactly
  the deeper subgroup, viewed inside the level-`n` subgroup. The induced
  map from `G_n/G_m` to `(𝔪ⁿ L)/(𝔪ᵐ L)` is injective.
- `CongruenceLieSurjectivityStatement` adds the `HenselianLocalRing`
  hypothesis. Henselian lifting supplies an integral section for every
  level-`m` point. A lift of a transition-kernel point has level `n`.
  The statement gives surjectivity and bijectivity of the induced quotient
  homomorphism, so that this homomorphism gives the group isomorphism.
  The integers of a nonarchimedean local field and those of its separable
  inertia fixed field are examples of Henselian bases.
- `CongruenceLieFunctorialityStatement` is the commuting square for a
  homomorphism of smooth models lifting the indicated generic map. Its
  group arrow is restriction of `rationalPoints.map f`. Its Lie arrow
  is induced by `GenericLie.map R f`, using `Hom.map_lieLattice_le`.
- `CongruenceLieAdjointEquivarianceStatement` is the commuting square for
  conjugation by an integral point. Normality in the integral points gives
  the conjugation arrow, and `adjoint_mem_lieLattice` gives the adjoint
  endomorphism on the Lie lattice. These induce the specified arrows at the
  congruence level and on the Lie quotient. This is the conjugation case of
  functoriality since the integral point defines conjugation on the model.

`lieLatticeQuotientMap` forms the actual map on the quotient induced by a
semilinear map preserving the two lattices. The maximal-ideal condition on
the scalar map ensures preservation of their powers.

`CongruenceModelLieLatticeStatement` concerns the congruence model of an
affine integral model over a discrete valuation ring. Its hypotheses use
an irreducible element as uniformizer, as in `congruenceModel`. It states
that the Lie lattice of the level-`n` dilatation equals `𝔪ⁿ L` inside the
same generic Lie algebra, including `n = 0`. The flat affine model and
DVR hypotheses suffice for this lattice identity. On dual numbers, the
congruence condition is that the tangent derivation takes values in
`𝔪ⁿ`. Dividing such a derivation by the nonzero generator `ϖⁿ` preserves
linearity and the Leibniz rule over the DVR. Smoothness is used for the
square-zero tensor comparison in the first four statements.

Kaletha and Prasad, *Bruhat–Tits Theory: A New Approach*, Proposition
A.5.19(3) and Remark A.5.20, pp. 642–643 (PDF pp. 673–674), give the
injection, Henselian surjection, and naturality in the group and in flat
coefficient algebras. These statements use the coefficient ring equal to
the base. The Henselian reduction input is Lemma 8.1.3, p. 284 (PDF
p. 315). The congruence model and its lattice identity are Definition
A.5.12 and Lemma A.5.13(4), pp. 636–637 (PDF pp. 667–668), with the
single-dilatation description in Remark A.5.14.
`kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`.
