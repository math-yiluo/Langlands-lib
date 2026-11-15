# Greenberg group schemes from a Greenberg ring scheme

Let `X` be an affine group scheme over `R`. Its Greenberg group of level `n` is the
`k`-group scheme corepresenting `B ↦ X(ℛ(B))` (KP §A.4, Greenberg 1961).

- `coordCorep X`: the Library coordinate algebra `Lie.coordinateAlgebra X` (with
  `Lie.coordinateIso`) corepresents `X.affinePointFunctor`
  (`AffineLinearEmbedding.corepresentableBy`).
- `smooth_coordinateAlgebra`: if `X → Spec R` is smooth, so is its coordinate algebra.
  Smoothness is transported along `coordinateIso`; then `Corepresented.smooth_groupScheme_iff`
  applies.
- `CoordPres X`, `nonempty_coordPres`: a surjection `R[x_1, …, x_N] → O(X)`. It exists
  because a smooth algebra is of finite type.
- `pointFunctor ℛ X = ℛ ⋙ X.affinePointFunctor`. `corep` corepresents it by `repAlg`
  (`Represent`).
- `greenbergGroup ℛ X P = Corepresented.groupScheme (pointFunctor ℛ X) (corep ℛ X P)`. It is
  affine, being the spectrum of an algebra. It is smooth when `X` is smooth
  (`smooth_greenbergGroup`), by formal smoothness and finite presentation of `repAlg`.
- `levelPointsEquiv`: a group isomorphism `X(R ⧸ 𝔪ⁿ)` (the rational points of the base
  change along `congruenceBaseMap`) `≃* G_X(k)`. It is the composite of
  `baseChangeBasePointsEquiv`, the identification of the test `Spec(R ⧸ 𝔪ⁿ)` with the
  affine test of `R ⧸ 𝔪ⁿ` (`congruenceTestIso`), transport along
  `levelIso : R ⧸ 𝔪ⁿ ≅ ℛ(k)`, the inverse of `Corepresented.affinePointsEquiv`
  (`greenbergPointsEquiv`) and the base test iso `baseTestIso`.
- `greenbergMap ℛ X P Q h : G_Z ⟶ G_X` for `h : Z ⟶ X`: `Corepresented.groupSchemeMap` of
  the natural transformation `pointNatTrans` (postcomposition with `h` on `X(ℛ(B))`).
- `levelPointsEquiv_naturality`: the square with the level-`n` map of `h` and
  `rationalPoints.map (greenbergMap h)` commutes. Each step of the composite commutes with
  postcomposition by `h`: `baseChangeBasePointsEquiv_comp`, associativity, and
  `Corepresented.groupSchemeMap_affinePoints` (`affinePointsEquiv_symm_comp`).
