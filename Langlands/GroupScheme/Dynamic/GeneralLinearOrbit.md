# Orbit extensions for block matrices in `GL_n`

This module proves that for the diagonal cocharacter `λ = diagonalCocharacter n R e` of the
general linear group scheme over `Spec R`, the dynamic subgroup functors are the block subgroup
functors:

- `parabolic_diagonalCocharacter`: `Dynamic.parabolic λ = blockParabolic n R e`;
- `centralizer_diagonalCocharacter`: `Dynamic.centralizer λ = blockLevi n R e`;
- `unipotent_diagonalCocharacter`: `Dynamic.unipotent λ = blockUnipotent n R e`.

These hold for every finite index type `n`, every `R : CommRingCat` and every `e : n → ℤ`, on all
test schemes over `Spec R`. The module also computes the limit map and the decomposition
`P(λ) = U(λ) ⋊ Z(λ)` on points (CGP, Lemma 2.1.5 and Proposition 2.1.8(2)):

- `hasLimit_diagonalCocharacter_iff`: a point `g` over `T` has limit `l` exactly when `g` is block
  upper triangular for `e` and `l` is its block diagonal part `blockLeviProjection`;
- `leviDecomposition_diagonalCocharacter`: on every test scheme, the points of `U(λ)` form a
  normal subgroup of the points of `P(λ)` with complement the points of `Z(λ)`;
- `hasLimit_blockShapeCocharacter_iff`: the limit computation for an ordered block shape `B`, with
  `B.leviEmbedding (B.leviProjection g)` as the limit.
 The corollaries `parabolic_blockShapeCocharacter`,
`centralizer_blockShapeCocharacter` and `unipotent_blockShapeCocharacter` give the same equalities
for an ordered block shape `B`, with the Library's block subgroups. They rewrite with
`blockParabolic_blockShapeWeight` and its two companions from
`Langlands.GroupScheme.Dynamic.GeneralLinear`. The mathematics is CGP, Example 2.1.1. The proof
below is the one implemented.

## Matrix scaling

`weightScale e s M` multiplies the `(i, j)` entry of `M` by `s ^ (e i - e j).toNat`. The element
`s` need not be a unit.

- `weightScale_one` and `weightScale_mul`: on matrices whose `(i, j)` entry vanishes for
  `e i < e j`, scaling is multiplicative. If `e i ≥ e k ≥ e j`, then the exponents add. Otherwise
  one of the two factors is zero.
- `weightScaleHom e s` is the resulting homomorphism from `blockParabolicSubgroup A e` to `GL n A`.
- `weightScale_units`: for a unit `u`, scaling by `u` is conjugation by `diag(u ^ e i)`.
- `weightScale_zero`: at `s = 0` it gives the block diagonal part `blockDiagonalPart`.
- `weightScale_of_blockLevi`: it fixes block diagonal matrices.
- `map_weightScale`: it commutes with ring homomorphisms.

## Existence of extensions (block subgroups lie in the dynamic ones)

Let `g` be a block parabolic point over `T`. The point `orbitExtension e g hg` of `GL_n` over
`T ×_S 𝔸¹_S` has the matrix `weightScale e s (fst^* g)`, where `s` is the coordinate of `𝔸¹`.

- `isOrbitExtension_orbitExtension`: restricted to `T ×_S 𝔾_m`, the matrix is
  `weightScale e u (fst^* g)`, where `u` is the unit coordinate. By `weightScale_units` this is
  the matrix of the orbit point `λ(u) g λ(u)⁻¹`.
- `pointsEquiv_evalZero_orbitExtension`: at the zero section `s = 0`, the value is the block
  diagonal part of `g`.

These give `blockParabolic_le_parabolic` and `blockUnipotent_le_unipotent`; for the latter, the
block diagonal part is `1`. `blockLevi_le_centralizer` follows directly from `weightScale_units`
and `weightScale_of_blockLevi`.

## Uniqueness on affine test schemes (dynamic subgroups lie in the block ones)

Let `T = Spec A` with any structure morphism `f` to `Spec R`, and let `E` extend the orbit map
of `g`. Over `Spec A`, the module uses two test schemes: `polyScheme f = Spec A[X]` and
`laurentScheme f = Spec A[T, T⁻¹]`.

The Laurent unit and its integer-power formula reuse
`Gm.relativeCoordUnit` and `Gm.relativeCoordUnit_zpow_val` from
[`MultiplicativeLaurent`](../MultiplicativeLaurent.md).

- `polyPoint f` is the point `(Spec A[X] → Spec A, X)` of `Spec A ×_S 𝔸¹`.
- `laurentIncl_polyPoint`: after restriction along `Spec A[T, T⁻¹] → Spec A[X]`, this point
  factors through `𝔾_m`, with unit `laurentUnit f`, the image of `T`.
- `toLaurent_polyPoint_entry`: let `P i j ∈ A[X]` be the entries of `E` at `polyPoint f`. Then
  `toLaurent (P i j) = C (g i j) * T (e i - e j)`. This uses `pointsEquiv_lift_orbit`, the matrix
  of the orbit map at a point `(a, y)`, and the Library's `Scheme.ΓSpecIso` naturality.
- `entry_eq_zero_of_isOrbitExtension`: if `e i < e j`, multiply by `T ^ (e j - e i)`. The
  injectivity of `Polynomial.toLaurent` gives `X ^ k * P i j = C (g i j)` with `k ≥ 1`. The
  constant coefficient then gives `g i j = 0`.
- `entry_eq_zero_of_mem_centralizer`: for a centralizing `g`, the same computation at the Laurent
  point gives `C (g i j) * T m = C (g i j)` with `m = e i - e j`. If `m ≠ 0`, comparing
  monomials gives `g i j = 0` (`eq_zero_of_C_mul_T_eq`).
- `evalZero_entry_of_eq`: if `e i = e j`, then `P i j = C (g i j)`. Evaluation at the point
  `polyZero f` (`X = 0`) shows that the `(i, j)` entry of `evalZero E` is `g i j`.
- `evalZero_entry_of_ne`: if `e i ≠ e j`, then the `(i, j)` entry of `evalZero E` is `0`. If
  `e i < e j`, then `g i j = 0`, so `toLaurent (P i j) = 0` and `P i j = 0`. If `e i > e j`, then
  `P i j = C (g i j) * X ^ (e i - e j)` by injectivity of `toLaurent`, and this vanishes at
  `X = 0`.

## Arbitrary test schemes

`section_ext` says that global sections of `T` agree when they agree on the members of Mathlib's
`affineOpenCover`. For an affine piece `Spec A_k → T`, `affinePieceIncl T k`, the restriction
of a point of `P(λ)`, `Z(λ)` or `U(λ)` lies again in it, by `comp_mem`. Its matrix entries are
the restrictions of those of `g` (`pointsEquiv_comp_apply`). Hence:

- `parabolic_le_blockParabolic`;
- `centralizer_le_blockLevi`;
- `unipotent_le_blockUnipotent`: entries with `e i < e j` vanish by the parabolic case, and
  entries with `e i = e j` equal those of `evalZero E = 1`.

Antisymmetry of the order on subgroup functors gives the three equalities.

## Limits and the decomposition

- `hasLimit_diagonalCocharacter_iff`: if `E` extends the orbit of `g`, then `g` is block upper
  triangular by `parabolic_le_blockParabolic`. On each affine piece of `T`, the entries of
  `evalZero E` are `g i j` for `e i = e j` and `0` otherwise, by `evalZero_entry_of_eq` and
  `evalZero_entry_of_ne`. By `section_ext` this is the block diagonal part of `g`. Conversely,
  for block upper triangular `g` the extension `orbitExtension e g hg` has the block diagonal
  part as its value at zero (`pointsEquiv_evalZero_orbitExtension`).
- `blockLeviProjection_mem`: the block diagonal part is block diagonal.
- `hasLimit_diagonalCocharacter_unique` and `hasLimit_diagonalCocharacter_mem_centralizer`: hence
  limits are unique and lie in `Z(λ) = blockLevi n R e`.
- `leviDecomposition_diagonalCocharacter`: normality is the general
  `Dynamic.unipotent_subgroupOf_parabolic_normal`. The complement statement is
  `Dynamic.isComplement'_unipotent_centralizer` with the two previous facts as hypotheses (module
  `Langlands.GroupScheme.Dynamic.Decomposition`).
- `hasLimit_blockShapeCocharacter_iff`: rewrite `blockShapeCocharacter B R` as the diagonal
  cocharacter of `blockShapeWeight B` and apply `hasLimit_diagonalCocharacter_iff`. The Library's
  `blockParabolicSubgroup_blockShapeWeight` and `leviEmbedding_leviProjection` translate block
  parabolic membership and the block diagonal part into `B.parabolic` and
  `B.leviEmbedding (B.leviProjection g)`.
