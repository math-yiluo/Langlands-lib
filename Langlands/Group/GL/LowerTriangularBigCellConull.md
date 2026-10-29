# The lower big cell `N_m · B̄_m` is conull

Author: Worker 234.

This module proves that the product set `N_m · B̄_m` fills
`GeneralLinear m F.Carrier` up to a Haar-null set. Here `N_m` is the upper
unipotent group and `B̄_m` is the group of invertible lower triangular
matrices. It then proves the same statement on the coset space `N_m \ GL_m`:
for every compatible quotient measure, the cosets with no representative in
`B̄_m` form a null set. The algebraic part holds over every field `K`. The
p-adic results use the supplied topology `T.topology` of a p-adic field.
Matrix and p-adic declarations are in the namespace
`Langlands.GeneralLinear`. The quotient-measure lemma is in
`Langlands.QuotientIntegration`.

## Provenance

Internal (derived infrastructure). H. Jacquet, I. I. Piatetski-Shapiro and
J. A. Shalika, *Rankin-Selberg convolutions*, Amer. J. Math. 105 (1983),
section 9.3, integrate over `N_m \ GL_m` using lower triangular
representatives. That use needs the cosets meeting `B̄_m` to be of full
measure. The source states no lemma of this form. The facts proved here are
standard:

- `g ∈ N_m · B̄_m` exactly when every bottom-right minor of `g` is nonzero;
- the zero set of a nonzero polynomial minor is Haar-null;
- a compatible quotient measure vanishes on sets whose preimage is null.

The module was written as a helper for the proof task 7b088130 of
`Langlands.RankinSelberg.LowerBlockQuotientDisintegrationStatement`, in the
shape agreed with that task's executor, Worker 936. The definitions
`bottomCornerMatrix` and `bottomCornerExchange` are implementation devices
for these minors. They have no counterpart in the source.

## Conventions

`GeneralLinear m K` is the published unit group of `Matrix (Fin m) (Fin m) K`.
`upperUnipotent m K` is the published group of upper triangular matrices
with unit diagonal. `lowerTriangularSubgroup m K` is the published group of
invertible lower triangular matrices (`mem_lowerTriangularSubgroup_iff`:
entries `(r, c)` with `r < c` vanish). `LeftQuotient H` is the published
quotient by `QuotientGroup.rightRel H`, whose points are cosets `H * g`, with
quotient map `leftQuotientMap H`. `IsCompatible H μG μH μ` is the published
Weil-formula compatibility of `QuotientIntegration`.

Over a p-adic field, every theorem fixes the topology `T.topology` of the
supplied `T : F.TopologicalData`, and `GeneralLinear m F.Carrier` carries the
induced unit-group topology. The measurable spaces are the Borel spaces of
`GeneralLinear m F.Carrier`, `upperUnipotent m F.Carrier` and
`LeftQuotient (upperUnipotent m F.Carrier)`. `BorelSpace` holds by `rfl`, as
in `LowerBlockQuotientDisintegrationStatement`. No canonical topology is
substituted.

## Definitions

- `bottomCornerMatrix k M`, for `k : ℕ` and `M : Matrix (Fin m) (Fin m) K`:
  the matrix whose entry `(r, c)` is `M r c` when `k ≤ r` and `k ≤ c`, and
  the identity entry `1 r c` otherwise. Its determinant is the bottom-right
  minor of `M` of size `m - k`. Full-size masked matrices are used instead of
  submatrices so that every threshold has the same index type `Fin m`.
  `bottomCornerMatrix_apply` unfolds it by `rfl`.
- `bottomCornerExchange i j M`, for `i j : Fin m`: the determinant of
  `bottomCornerMatrix i M` after its row `i` is replaced by row `j` of `M`,
  with the entries in columns `c < i` set to `0`.

## Theorems over a field

Every field `K`, every `m : ℕ`:

- `bottomCornerMatrix_apply_of_le`, `bottomCornerMatrix_apply_of_lt_right`,
  `bottomCornerMatrix_row_of_lt`, `bottomCornerMatrix_mul_apply_of_lt`,
  `bottomCornerMatrix_eq_one`: entry formulas. A row `r < k` is the identity
  row. At a threshold `k ≥ m` the corner matrix is `1`.
- `bottomCornerMatrix_mul k X Y`: the corner matrix of `X * Y` is
  `bottomCornerMatrix k X * bottomCornerMatrix k Y` when `X r l = 0` for all
  `l < k ≤ r`. This holds for every upper triangular `X`.
- `det_bottomCornerMatrix_of_mem_upperUnipotent`: for `u ∈ N_m` every corner
  matrix is upper triangular with unit diagonal, so its determinant is `1`.
- `det_bottomCornerMatrix_ne_zero_of_mem_lowerTriangular`: for `b ∈ B̄_m` every
  corner matrix is lower triangular, and its diagonal entries are diagonal
  entries of `b` or `1`. These are nonzero because `det b ≠ 0`.
- `det_bottomCornerMatrix_mul_ne_zero`: for `u ∈ N_m` and `b ∈ B̄_m`, every
  corner minor of `u * b` is nonzero, by the two previous facts and
  multiplicativity.
- `exists_upperUnipotent_mul_lowerTriangular g hg`: if
  `det (bottomCornerMatrix c g) ≠ 0` for every `c : Fin m`, then `g = u * b`
  with `u ∈ N_m` and `b ∈ B̄_m`. Proof: let `A_c = bottomCornerMatrix c g` and
  let `B` be the matrix whose column `c` is column `c` of `A_c⁻¹`. Rows
  `r < c` of `A_c` are identity rows, so `B r c = 0` for `r < c` and `B` is
  lower triangular. For rows `r ≥ c`, the entries of `g * B` in column `c`
  equal those of `A_c * A_c⁻¹ = 1`. So `g * B` is upper triangular with unit
  diagonal and determinant `1`, `det B ≠ 0`, and with `β` the unit of `B`,
  `g = (g * β) * β⁻¹`.
- `exists_upperUnipotent_mul_lowerTriangular_iff`: the two directions
  together. `setOf_not_upperUnipotent_mul_lowerTriangular_eq`: the complement
  of `N_m · B̄_m` is `⋃ c : Fin m, {g | det (bottomCornerMatrix c g) = 0}`.
- `det_bottomCornerMatrix_transvection_mul i j t M`: replacing `M` by
  `transvection i j t * M`, which adds `t` times row `j` to row `i`, changes
  `det (bottomCornerMatrix i M)` by `t * bottomCornerExchange i j M`. Proof:
  the corner matrix of the product is the corner matrix of `M` with row `i`
  replaced by its sum with `t` times the cut-down row `j`. Expansion is by
  linearity in row `i` (`Matrix.det_updateRow_add`, `det_updateRow_smul`).
- `exists_bottomCornerExchange_ne_zero g i h0 h1` (size `n + 1`): if the minor
  at threshold `i` vanishes and the minor at threshold `i + 1` does not, some
  `j < i` has `bottomCornerExchange i j g ≠ 0`. Proof: Laplace expansion along
  row `i` (`Matrix.det_succ_row`) gives a cofactor vector `w`. The
  determinant with row `i` replaced by `v` is `∑ c, v c * w c`. Suppose every
  exchange determinant with `j < i` vanished. The vanishing minor handles
  `j = i`, and repeated rows handle `j > i`. Then `g` annihilates the vector
  `w'` equal to `w` on columns `≥ i` and `0` elsewhere. Invertibility forces
  `w' = 0`. But `w i` is the minor at threshold `i + 1`, which is nonzero.

## Topology and Haar measure

Every field `K` with a topology and `[IsTopologicalRing K]` (omitted for
`continuous_bottomCornerMatrix`), with `[T2Space K]` added for the last two
theorems, and `GeneralLinear m K` with the unit-group topology:

- `continuous_bottomCornerMatrix`, `continuous_det_bottomCornerMatrix`,
  `continuous_bottomCornerExchange`: continuity in `g`, entrywise.
- `isClosed_setOf_not_upperUnipotent_mul_lowerTriangular` (`[T2Space K]`):
  the complement of `N_m · B̄_m` is closed. It is a finite union of zero sets
  of continuous minors.
- `haar_setOf_not_upperUnipotent_mul_lowerTriangular hK μ`: assume
  `GeneralLinear m K` is locally compact with its Borel space, and that every
  neighbourhood of `0` in `K` contains a nonzero element (`hK`). Then every
  inner regular left Haar measure `μ` gives the complement of `N_m · B̄_m`
  measure `0`. Proof: for `m = 0` the complement is empty. Otherwise let
  `i` be the largest threshold with vanishing minor for a given `g`. The
  minor at `i + 1` is nonzero: it is `1` if `i + 1 = m`. So the previous
  lemma places `g` in a piece
  `P i j = {g | det (bottomCornerMatrix i g) = 0 ∧ bottomCornerExchange i j g ≠ 0}`
  with `j < i`. There are finitely many pieces, each measurable. The
  published Steinhaus lemma `haar_null_of_forall_nhds_disjoint_translate`
  shows each piece is null. Given a neighbourhood `U` of `1`, the published
  continuity `continuous_transvectionUnit` and `transvectionUnit_zero`
  provide a nonzero `t` with `1 + t E_{ij} ∈ U`. By the transvection formula,
  left translation by it turns the vanishing minor of a point of `P i j`
  into `t * bottomCornerExchange i j g ≠ 0`, so it moves the piece off
  itself.

## Quotient measures

- `QuotientIntegration.IsCompatible.measure_eq_zero_of_preimage hH K hK hμ hS h0`:
  let `G` be a second-countable, locally compact Hausdorff group with Borel
  space and a compact open subgroup `K`, and let `H` be a closed subgroup.
  Take regular Haar measures `μG` and `μH`, with `μH` right invariant, and a
  compatible quotient measure `μ` on `LeftQuotient H`. If `S` is measurable
  and its preimage under `leftQuotientMap H` is `μG`-null, then `μ S = 0`.
  Proof: by the published `compactOpenOrbitMeasure`, `μ` restricted to each
  orbit image `{[g k] | k ∈ K}` is a scalar multiple of the pushforward of
  `μG.restrict K` under `k ↦ [g k]`. The preimage of `S` under that map is a
  left translate of the null preimage, so it is null by left invariance.
  Hence `S` meets each orbit image in a null set. Second countability
  (`TopologicalSpace.isOpen_iUnion_countable`) gives countably many `g` whose
  translates `g K` cover `G`. The quotient map is surjective, so these orbit
  images cover `S`.

## p-adic results

Every prime `p` with `[Fact p.Prime]`, every `F : PadicField.{uF} p`, every
`T : F.TopologicalData`, every `m : ℕ`:

- `padic_setOf_not_upperUnipotent_mul_lowerTriangular T m`: in the supplied
  topology with the Borel space, the set of `g` not of the form `u * b`,
  `u ∈ upperUnipotent m F.Carrier`, `b ∈ lowerTriangularSubgroup m F.Carrier`,
  is closed. It has measure `0` for every measure `μ` with
  `μ.IsHaarMeasure`. The supplied-topology certificates are the published
  `T.fieldT2`, `T.generalLinearTopologicalGroup m`,
  `T.generalLinearLocallyCompactSpace m` and
  `T.generalLinearSecondCountableTopology m`. `IsTopologicalRing F.Carrier`
  comes from `T.valuativeRel` and `T.localField`. Inner regularity of a Haar
  measure comes from instance search, as in `MirabolicTailConullProof`. The
  hypothesis `hK` is the published `padic_exists_ne_zero_mem_nhds_zero T`.
- `padic_lowerTriangular_leftQuotient_conull T m`: with the same topology and
  Borel spaces on `GeneralLinear m F.Carrier`, `upperUnipotent m F.Carrier`
  and `LeftQuotient (upperUnipotent m F.Carrier)`, fix measures `μG` and
  `μH` with `[μG.IsHaarMeasure] [μG.Regular] [μH.IsHaarMeasure] [μH.Regular]
  [μH.IsMulRightInvariant]`. Then every `μ` with
  `IsCompatible (upperUnipotent m F.Carrier) μG μH μ` satisfies
  `μ {q | ∀ b ∈ lowerTriangularSubgroup m F.Carrier, Quotient.mk _ b ≠ q} = 0`.
  Proof: the preimage of this set in `GL_m` is exactly the complement of
  `N_m · B̄_m`, because `[b] = [g]` iff `g * b⁻¹ ∈ N_m`
  (`QuotientGroup.rightRel_apply`). The set is closed, hence measurable,
  because the quotient map is an open quotient map
  (`leftQuotient_isOpenQuotientMap`) and its preimage is closed. The
  compact open subgroup is the published `T.generalLinearCompactOpen m`, and
  `N_m` is closed by `UpperUnipotent.isClosed`. The previous theorem and
  `IsCompatible.measure_eq_zero_of_preimage` conclude.

The two quotient-measure theorems keep both `[IsHaarMeasure]` and `[Regular]`
assumptions so that they match `compactOpenOrbitMeasure` and the measures of
`LowerBlockQuotientDisintegrationStatement`. The overlapping-instance linter
is disabled for these two declarations only.

## Role

Together with `isOpenEmbedding_lowerTriangularQuotientMap` from
`LowerTriangularQuotientCell`, the last theorem lets a compatible quotient
measure on `N_m \ GL_m` be computed on the open cell of lower triangular
representatives, with nothing lost off that cell. The planned consumer is
the proof of `LowerBlockQuotientDisintegrationStatement` (task 7b088130).
