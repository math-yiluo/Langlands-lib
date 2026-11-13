# Root-group points acting on the binary form

Author: Worker 10.

Fix a matrix representation `ρ` of a group scheme `G` over a field `F`, a torus
`i : T ⟶ G`, and raising and lowering additive maps `xp, xm : 𝔾ₐ ⟶ G` that
satisfy the rank-one relation with a cocharacter `cor`. Let `e = e_j` be a
coordinate vector fixed by `xp` and lying on the torus character line of
weight `lam`. This module checks, over every field extension `L` of `F`, the
hypotheses of the algebra in `SplitRankOneBinaryForm.md`. As a consequence,
`L`-points of `xp`, `xm` and `T` act on the binary form by `GL₂`-substitutions
(`IsBinarySimilitude`).

## Provenance

This is internal infrastructure for the split rank-one height bound
(`SplitRankOneAdelic.md`); it does not formalize a literature statement. The
rank-one relation is the Library's `RootCell.RelationOver`. On matrices it
reads `xp(s) xm(t) = xm(t/u) · cor(u) · xp(s/u)` with `u = 1 + st`
(`RankOneRootCoefficient.affineMatrix_cell_relation`).

## Definitions

- `gaPoint A t` and `gmPoint A u`: the affine `A`-points of `𝔾ₐ` with
  coordinate `t`, and of `𝔾ₘ` with unit coordinate `u`.
- `CellHyp ρ j i xp xm cor α lam m` (a `Prop` structure) bundles five
  conditions:
  - `cell`: the rank-one relation `RootCell.RelationOver i cor xp xm Z` over
    every `Z`.
  - `equivm`: `xm` is torus-equivariant of weight `-α`.
  - `fixp`: `e_j` is a fixed vector of `ρ` restricted along `xp`.
  - `line`: every affine torus point `τ` acts on `e_j` by the scalar
    `lam(τ)`.
  - `pairing`: `⟨lam, cor⟩ = m`.
- `lowerMat ρ xm L t` and `raiseMat ρ xp L s`: the polynomial matrices
  `univariateMatrix (ρ.restrict xm)` and `univariateMatrix (ρ.restrict xp)`,
  evaluated at `t` and `s` in `L`.
- `wvec ρ j xm L d`: the image in `L` of the degree-`d` coefficient vector of
  the lowering curve `t ↦ xm(t) e_j`.

## Results

Character identities, for points over any `F`-algebra `A`:

- `characterValue_cocharacter`: `χ(cor(u)) = u^⟨χ, cor⟩`.
- `characterValue_add'`, `characterValue_zero'`, `characterValue_neg'` and
  `characterValue_nsmul'`.

Matrices over `L`:

- `lowerMat_eq` and `raiseMat_eq`: these matrices are the affine matrices of
  the `L`-points `xm(t)` and `xp(s)`.
- `lowerMat_add`: `xm(s + t) = xm(s) xm(t)`.
- `lowerMat_zero`: `xm(0) = 1`.
- `coeffVec_zero`: the constant coefficient of the lowering curve is `e_j`.

Consequences of `CellHyp`:

- `CellHyp.raiseMat_mulVec_single`: `xp(s)` fixes `e_j`.
- `CellHyp.coroot_mulVec_single`: `cor(u)` acts on `e_j` by `u^m`.
- `CellHyp.relation`: for `1 + st ≠ 0`,
  `xp(s) xm(t) e_j = (1+st)^m • xm((1+st)⁻¹ t) e_j`.
- `CellHyp.coeffVec_eq_zero` (for `F` infinite): the lowering curve has degree
  at most `m`. This applies `coeffVec_eq_zero_of_relation` with `s = 1`.
- `CellHyp.pairing_nonneg`: `0 ≤ m`, because the degree-0 coefficient `e_j`
  is nonzero.
- `CellHyp.torus_commute`: `τ xm(y) v = xm(α(τ)⁻¹ y) τ v`.
- `CellHyp.torus_mulVec_single`: `τ e_j = lam(τ) e_j`.

With a natural weight `k` (`CellHyp … (k : ℤ)`):

- `CellHyp.relation_nat`: the relation with a natural exponent.
- `CellHyp.lowerMat_mulVec_single`: `xm(t) e_j = binaryForm k (wvec …) 1 t`.

For `F` and `L` infinite:

- `CellHyp.isBinarySimilitude_lower` and `CellHyp.isBinarySimilitude_raise`:
  similitudes with multiplier `1`.
- `CellHyp.isBinarySimilitude_torus`: the torus point `τ` is a similitude with
  multiplier `lam(τ)^2 · (α(τ)⁻¹)^k`.
