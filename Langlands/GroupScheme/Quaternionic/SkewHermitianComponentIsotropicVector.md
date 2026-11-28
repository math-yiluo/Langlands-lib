# Isotropic vectors of the symmetric component from isotropic quaternionic vectors

Let `Q` be quaternion coordinates `D = E ⊕ jE` with embedded quadratic field `E = F(x)`,
`x² = c`. Let `B` be a pairing skew-hermitian for quaternion conjugation `Q.bar` and let
`R` be a field extending `E`.
`Langlands.GroupScheme.KneserThree.QuatData.exists_isotropic_component_of_isotropic` assumes
`2 ≠ 0` in `F` and a nonzero vector `t` of `R ⊗[F] V` with `B_R(t, t) = 0`. It gives a nonzero
vector of `R ⊗[E] V` on which the scalar extension of the symmetric component
`Q.symmetricComponent B` vanishes.

Unlike `exists_isotropic_pair_in_symmetricComponent` in
`Quaternionic/SkewHermitianComponentIsotropicPlane`, no partner `s` with `B_R(t, s) = 1` is
assumed. Over a split quaternion algebra an isotropic row need not have such a partner.

## Proof

Write `X` and `J` for left multiplication by `x` and `j` on `R ⊗[F] V`, and `θ ∈ R` for the
image of the root of `E`, so `θ² = c`. Let `p : R ⊗[F] V → R ⊗[E] V` be the projection
`r ⊗ v ↦ r ⊗ v`. As in `SkewHermitianComponentIsotropicPlane`, the extended component at
`p(s), p(s')` is the conjugated second coordinate of `B_R(s, s')`. It therefore vanishes at
`p(s), p(s)` whenever `B_R(s, s) = 0`.

The additive map `R ⊗[E] V → R ⊗[F] V`, `r ⊗ v ↦ (X + θ)(r ⊗ v)`, is well defined: writing
`e = a₀ + a₁·root` in `E`, the identity `X² = c = θ²` gives
`(X + θ)(r ⊗ e v) = (X + θ)(e_R r ⊗ v)`. Composed with `p` it is `X + θ`. So `p(s) = 0` forces
`X s = -θ s`.

Both `t` and `J t` are isotropic, because `B_R(J s, J s') = (1 ⊗ j) B_R(s, s') (1 ⊗ τ j)`. If
`p(t) ≠ 0`, it is the required vector. Otherwise `X t = -θ t`. From `jx = -xj` we get
`(X + θ)(J t) = 2θ J t`. This is nonzero since `θ ≠ 0`, `2 ≠ 0` and `J² = δ ≠ 0`. Hence
`p(J t) ≠ 0`.

The private tensor lemmas (`quaternionMul`, the pair formulas, the projection and the
coefficient map) are restatements of the private lemmas of
`Quaternionic/SkewHermitianComponentIsotropicPlane`.

This is a local step in the projective representation argument of T. A. Springer's appendix
to M. Kneser, *Lectures on Galois Cohomology of Classical Groups* (1969), Proposition 5.3.2,
printed p. 109 (PDF p. 115). The step handles local isotropy without a hyperbolic partner.
