# Proof of the upper unipotent stability of the two-block cell submodule

Author: Worker 731.

The theorem `Langlands.Whittaker.twoBlockCellUnipotentStability` proves exactly
the published proposition
`Langlands.Whittaker.TwoBlockCellUnipotentStabilityStatement.{uF,uV}`. The
statement module and the modules it imports are unchanged. The theorem uses
only the standard axioms `propext`, `Classical.choice` and `Quot.sound`.

Write `A = a + 1`, `B = b + 1`, `P = twoBlockParabolic F a b` (the standard
upper parabolic of block shape `(A, B)` in `GL_{A+B}`),
`w = Shahidi.blockWeyl A B F.Carrier` and, for a `B × A` matrix `x`,
`n(x) = Shahidi.intertwiningUnipotent A B F.Carrier x`. In the Library,
`n(x) = Shahidi.swapRank A B F.Carrier (Shahidi.upper B A F.Carrier x)`:
`Shahidi.upper B A x` is the block matrix `[[1, x], [0, 1]]` of total rank
`B + A`, and `swapRank` only renames the rank `B + A` as `A + B`, keeping
every entry.

## Route

The source does not prove this property (see the statement's Markdown). The
Lean proof is a direct matrix computation.

Let `u` be upper unipotent in `GL_{A+B}`. Read in rank `B + A`, that is
`u' = swapRank⁻¹ u`, it is still upper triangular, so it lies in the
standard parabolic of the exchanged shape `(B, A)`. Write its blocks as
`u' = [[α, β], [0, δ]]` with `α ∈ GL_B`, `δ ∈ GL_A` and `β` a `B × A` matrix.
Then

```
[[1, x], [0, 1]] u' = diag(α, δ) [[1, y], [0, 1]],   y = α⁻¹ (β + x δ),
```

and, conjugating by `w`,

```
w n(x) u = diag(δ, α) w n(y).
```

The matrix `diag(δ, α)` lies in `P`. Hence:

- the cell `P w n(M_{B×A})` is stable under right multiplication by `u`;
- for `f` in the induced space,
  `f(w n(x) u) = ρ(diag(δ, α)) f(w n(y))`, where `ρ` is the inducing
  representation of `P`. So the restriction of `ξ(u) f` is `ρ(diag(δ, α))`
  applied to the restriction of `f` composed with the affine map
  `x ↦ α⁻¹ (β + x δ)`, which is a homeomorphism.

## Helpers

### Section `Matrix` (commutative ring `R`, block sizes `m, n > 0`)

- `mul_apply_add` (private): an entry of a product in rank `n + m` is the sum
  over the first `n` indices plus the sum over the last `m` indices
  (`Matrix.mul_apply`, `Fin.sum_univ_add`).
- `parabolicDiagonal g`: the pair `(α, δ) ∈ GL_n × GL_m` of diagonal blocks of
  `g` in the parabolic of `Shahidi.twoBlocks n m hn hm`. It is the published
  Levi projection followed by `Shahidi.twoBlockLeviEquiv`.
  `parabolicDiagonal_fst_apply` and `parabolicDiagonal_snd_apply` give its
  entries, from `Shahidi.twoBlocks_leviProjection_first` and `_second`.
- `parabolicCorner g`: the upper-right `n × m` block `β` of `g`.
- `parabolicShift g x = α⁻¹ (β + x δ)`.
- `upper_mul_parabolic`: for `g` in that parabolic,
  `Shahidi.upper n m R x * g = blockSum (α, δ) * Shahidi.upper n m R (α⁻¹ (β + x δ))`.
  The proof compares the four blocks of entries with `mul_apply_add`, the
  published entry lemmas for `Shahidi.upper` and `GeneralLinear.blockSum`, and
  the vanishing of the lower-left block of `g`
  (`Shahidi.twoBlocks_mem_parabolic_iff`). For the upper-right block it uses
  `α (α⁻¹ (β + x δ)) = β + x δ`.
- `blockWeyl_mul_intertwiningUnipotent_mul_swapRank`: for such `g`,
  `w n(x) swapRank(g) = blockSum (δ, α) * (w n(α⁻¹ (β + x δ)))`. It applies
  `swapRank` (a group isomorphism) to `upper_mul_parabolic`, and uses the
  published `Shahidi.blockWeyl_conjugate_blockSum`:
  `w swapRank(blockSum (α, δ)) w⁻¹ = blockSum (δ, α)`.
- `blockSum_mem_twoBlocks_parabolic`: `blockSum (h, g)` lies in the parabolic
  of `Shahidi.twoBlocks m n hm hn`, since its lower-left block is zero
  (`blockSum_apply_right_left`).
- `swapRank_symm_mem_parabolic`: for `u` in
  `GeneralLinear.upperUnipotent (m + n) R`, `swapRank⁻¹ u` lies in the
  parabolic of `Shahidi.twoBlocks n m hn hm`. A lower-left entry has row index
  `n + i` and column index `j < n`, so it lies below the diagonal and vanishes
  by `UpperUnipotent.entry_eq_zero`. Only upper triangularity is used.
- `affineHomeomorph α β δ`: for a topological ring `R`, the map
  `x ↦ α⁻¹ (β + x δ)` as a homeomorphism of `Matrix (Fin n) (Fin m) R`, with
  inverse `z ↦ (α z - β) δ⁻¹`. Continuity of both maps comes from
  `Continuous.matrix_mul`. `affineHomeomorph_apply` records its values.

### Section `Cell` (`F : PadicField p`)

With `m = A` and `n = B`:

- `exchangedParabolic F a b u`: `swapRank⁻¹ u` as an element of the parabolic
  of shape `(B, A)`. `swapRank_exchangedParabolic` says that `swapRank` maps it
  back to `u`.
- `unipotentLeviFactor F a b u`: `blockSum (δ, α)` as an element of `P`.
- `unipotentShift F a b u x`: the coordinate `α⁻¹ (β + x δ)`.
- `twoBlockCellPoint_mul_upperUnipotent`:
  `twoBlockCellPoint F a b x * u = diag(δ, α) * twoBlockCellPoint F a b y`,
  with `y = unipotentShift F a b u x`. This is the matrix lemma above,
  specialized.
- `mul_upperUnipotent_mem_twoBlockCell`: if `g = q w n(x)` lies in the cell,
  then `g u = (q diag(δ, α)) w n(y)` lies in the cell.

## Main proof

The theorem introduces all data of the statement and installs the canonical
field topology `F.canonicalTopologicalData.topology` with its valuative
relation and local field instance, which make `F.Carrier` a topological ring.
Let `f ∈ D`, that is, the support of `f` lies in the cell and its restriction
`x ↦ f(w n(x))` has compact support.

- Support. Suppose `(ξ(u) f)(g) = f(g u) ≠ 0`. Then `g u` lies in the cell.
  By `mul_upperUnipotent_mem_twoBlockCell` applied to `u⁻¹`, which is again
  upper unipotent, `g = (g u) u⁻¹` lies in the cell.
- Compact support of the restriction. By
  `twoBlockCellPoint_mul_upperUnipotent` and the covariance of `f` under `P`,
  `f(p g) = ρ(p) f(g)`, the restriction of `ξ(u) f` equals
  `ρ(diag(δ, α)) ∘ (restriction of f) ∘ φ`, where `φ` is the
  `affineHomeomorph` of `(α, β, δ)`. Composition with a homeomorphism keeps
  compact support (`HasCompactSupport.comp_homeomorph`), and so does
  composition on the left with the linear map `ρ(diag(δ, α))`, which sends
  `0` to `0` (`HasCompactSupport.comp_left`).

## Scope

The proof uses no hypothesis on `π₁` or `π₂`, and none appears in the
statement. Smoothness of `ξ(u) f` is already part of its type, since `ξ(u)`
acts on the smooth induced space.
