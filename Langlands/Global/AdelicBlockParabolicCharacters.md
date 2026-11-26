# Block determinant characters of the scheme block parabolic

Module `Langlands.Global.AdelicBlockParabolicCharacters` constructs, for a block shape `B` of
rank `N` and any commutative ring `R`, the rational characters of the block parabolic subgroup
scheme `blockParabolicScheme (Fin N) R (blockShapeWeight B)` of `GL_N` given by the determinants
of the diagonal blocks, and computes their normalized adelic norms over a number field.

## Declarations

In the namespace `Langlands.GroupScheme.GeneralLinear`:

- `blockParabolicTestPointsEquiv B R T`: the points of the block parabolic scheme with values in a
  test scheme `T` over `Spec R` are the block upper triangular invertible matrices
  `B.parabolic Γ(T, ⊤)`. It composes the point description of the cut-out closed subgroup
  scheme (`Corepresented.pointsEquiv`) with
  `blockParabolicSubgroup_blockShapeWeight`. `blockParabolicTestPointsEquiv_val` says that the
  underlying matrix is the matrix of the point in `GL_N`, and
  `blockParabolicTestPointsEquiv_naturality` that pulling back along `a : T' ⟶ T` applies the
  ring map of global sections entrywise.
- `parabolicBlockPoints B R i T`: on `T`-points, the `i`-th diagonal block
  `B.leviProjection Γ(T, ⊤) (·) i`, as a point of `GL_(B.size i)`. It is a group homomorphism
  because `B.leviProjection` is. `parabolicBlockPoints_naturality` is its naturality in `T`,
  proved entrywise from `B.leviProjection_apply` (the block entries of a block upper triangular
  matrix).
- `parabolicBlockHom B R i`: the morphism of group schemes from the block parabolic to
  `GL_(B.size i)` with these points (`homOfPoints`), and `pointsEquiv_parabolicBlockHom`, its
  value on points.
- `parabolicBlockCharacter B R i`: the rational character `det ∘ parabolicBlockHom B R i` of the
  block parabolic, as `characterRestrict` of `determinantCharacter (Fin (B.size i)) R`.

In the namespace `Langlands.Global.AdelicBlockEisensteinGeometry`, over a field `F` with
`𝕜 = CommRingCat.of F`:

- `affinePointsEquiv_parabolicBlockHom`: for an `F`-algebra `S` and a point `x` of the block
  parabolic with values in `S`, the matrix of `parabolicBlockHom B 𝕜 i` at `x` is the `i`-th
  diagonal block of the block upper triangular matrix `blockParabolicPointsEquiv F B S x`. The
  proof compares entries through the global-sections isomorphism
  (`pointsEquiv_eq_affinePointsEquiv`, used for `GL_(B.size i)` and for `GL_N`), which is
  injective.
- `characterNorm_determinantCharacter`: for `F` a number field, the normalized adelic norm of the
  determinant character of the scheme `GL_b` at an adelic point `g` is
  `determinantNorm F b (adelicHomeomorph F b g)`. The private helper
  `characterUnits_determinantCharacter` evaluates the determinant character on affine points
  through `characterOnAffineMatrices_determinantCharacter`.
- `characterLog_parabolicBlockCharacter`: for an adelic point `q` of the block parabolic, the
  logarithmic functional `characterLog F P q` at `parabolicBlockCharacter B 𝕜 i` is
  `log (blockDeterminantNorm F B i m)`, where `m` is the Levi projection of the block upper
  triangular adelic matrix `blockParabolicPointsEquiv F B 𝔸 q`. It combines `characterLog_map`
  for `parabolicBlockHom`, `characterNorm_determinantCharacter` and
  `affinePointsEquiv_parabolicBlockHom`.

## Provenance

These are internal constructions. On the block Levi scheme the corresponding characters are
`blockDeterminantCharacter` (module `Langlands.GroupScheme.Rational.Characters`), and the
projection to one block is `blockProjectionHom` (module
`Langlands.GroupScheme.Rational.BlockCharacterProof`); the constructions here follow the same
pattern on the block parabolic. They provide the rational characters of `P` in which the twist
`δ_P(g)^(s/N)` of the cuspidal-pair Eisenstein series becomes a parameter in `X^*(P) ⊗ ℂ`
(module `Langlands.Global.Factors.CuspidalPairSchemeSeries`), as in the parametrization of the
Eisenstein series of Bernstein–Lapid, *On the meromorphic continuation of Eisenstein series*,
J. Amer. Math. Soc. 37 (2024), §2.2, (2.1), p. 191.
