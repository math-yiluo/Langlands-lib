# Proof of the actual upper Bruhat cell coordinate homeomorphisms

Author: Worker 779.

`Langlands.GeneralLinear.upperBruhatCoordinates.{u}` proves the published
proposition `Langlands.GeneralLinear.UpperBruhatCoordinatesStatement.{u}` of
`Langlands.Group.GL.UpperBruhatCoordinatesStatement`. Its type is exactly that
proposition. It retains every field `K : Type u`, every topology on `K` with
`IsTopologicalDivisionRing K` and `T2Space K`, every rank `n` including zero,
and every permutation `w : Equiv.Perm (Fin n)`. The statement pair and the
pairs it imports are unchanged. The proof takes no factorization, uniqueness,
surjectivity, quotient-map, local-compactness or countability hypothesis.

Notation follows the statement's Markdown: `B = upperTriangularSubgroup n K`,
`U = upperUnipotent n K`, `N = permutationUnipotentMinus n K w`,
`p = permutation n K w` and `C = UpperBruhatCell n K w`. For a predicate `P`
on `Fin n`, `A_P` denotes the principal block `A.toBlock P P`. All auxiliary
declarations are in the namespace
`Langlands.GeneralLinear.UpperBruhatCoordinates`.

## Proof outline

1. The coordinate map `(b, v) ↦ b * p * v` is injective because
   `B ∩ lowerUnipotent n K` is trivial.
2. It is surjective. Every `b ∈ B` is corrected by a right factor `y ∈ N` so
   that `p * (b * y) * p⁻¹ ∈ B`. The factor `y` is obtained by solving one
   linear system per column.
3. The inverse is continuous. If `g = b * p * v`, the matrix
   `p * v⁻¹ * p⁻¹` is the unique lower unipotent matrix `L` for which
   `(g * p⁻¹) * L` is upper triangular. It is computed column by column with
   the inverses of the bottom-right principal blocks of `g * p⁻¹`. These
   blocks are invertible everywhere on `C`, so `L` is a continuous function
   of `g`. Then `v` and `b = g * v⁻¹ * p⁻¹` are continuous as well.
4. The torus version composes the first homeomorphism with an explicit
   homeomorphism `U × (Fin n → Kˣ) ≃ₜ B`, and moves the diagonal factor across
   `p` with the published `permutation_mul_diagonalUnits`.

## Column solves

For `Q : Fin n → Fin n → Prop` and a square matrix `A`, the definition
`columnSolve Q A` has entry at `(k, c)` equal to

- `-(((A_{Q c})⁻¹ *ᵥ (r ↦ A r c)) k)` when `Q c k` holds, where `r` ranges
  over `{r // Q c r}`;
- `if k = c then 1 else 0` otherwise.

Thus column `c` is the standard basis vector `e c` plus a vector supported
on `{k | Q c k}`. The evaluation lemmas are `columnSolve_apply_of_pos` and
`columnSolve_apply_of_neg`.

- `mul_apply_of_support`: if column `c` of `Y` equals `e c` outside a
  predicate `P` and `¬ P c`, then
  `(A * Y) r c = (∑ k ∈ P, A r k * Y k c) + A r c`.
- `mul_columnSolve_apply`: if `¬ Q c c` and `det A_{Q c} ≠ 0`, then
  `(A * columnSolve Q A) r c = 0` for every `r` with `Q c r`. The proof
  rewrites the restricted sum as `A_{Q c} *ᵥ (-(A_{Q c})⁻¹ *ᵥ a)` and uses
  `Matrix.mul_nonsing_inv`.
- `eq_columnSolve` (uniqueness): suppose `Q` is irreflexive and every block
  `A_{Q c}` has nonzero determinant. If `Y` agrees with the identity matrix
  at every entry `(k, c)` with `¬ Q c k`, and `(A * Y) r c = 0` whenever
  `Q c r`, then `Y = columnSolve Q A`. Column `c` of `Y` restricted to `Q c`
  solves `A_{Q c} x = -a`, so `Matrix.nonsing_inv_mul` identifies it.
- `toBlock_mul_of_support`: if `Y k t = 0` whenever `¬ P k` and `P t`, then
  `(A * Y)_P = A_P * Y_P`. This follows from Mathlib's
  `Matrix.toBlock_mul_eq_add`.
- `det_toBlock_ne_zero_of_upper`: a principal block of an upper triangular
  matrix is upper triangular. If the diagonal entries are nonzero, the block's
  determinant, which is the product of its diagonal entries, is nonzero.
- `diag_ne_zero_of_upper`: an invertible upper triangular matrix has nonzero
  diagonal entries, because its determinant is their product.

Continuity, for a topological division ring `K`:

- `continuous_matrix_inv_of_det_ne_zero`: along a continuous family of
  matrices with nonzero determinants, the matrix inverse is continuous.
  Mathlib's `continuousAt_matrix_inv` needs `Ring.inverse` to be continuous
  at the determinant. Since `Ring.inverse` is field inversion
  (`Ring.inverse_eq_inv'`), this follows from `continuousAt_inv₀` at a
  nonzero point.
- `continuous_generalLinear_of_val`: a map into
  `Langlands.GeneralLinear n K` is continuous once its matrix values are.
  `Units.continuous_iff` also requires continuity of the inverse values.
  These are the matrix inverses (`Matrix.coe_units_inv`), so the previous
  lemma gives their continuity. This is how the proof controls inverse values
  in the units topology.
- `continuous_columnSolve`: if `A x` depends continuously on `x` and every
  block `(A x)_{Q c}` has nonzero determinant, then `columnSolve Q (A x)` is
  continuous. The proof works entry by entry. Entries outside `Q` are
  constant. The other entries are a coordinate of the negated product of a
  continuous inverse block and a continuous vector.

## Injectivity

`eq_one_of_upper_of_lower`: an element of `B ∩ lowerUnipotent n K` lies in
`U`, because its diagonal entries are one. By the published
`upperUnipotent_inf_lowerUnipotent`, it is the identity.

`upperBruhatCellMap_injective`: suppose `b * p * v = b' * p * v'`. Then
`b'⁻¹ * b = p * (v' * v⁻¹) * p⁻¹`. The right side is lower unipotent because
`v' * v⁻¹ ∈ N`; this uses `mem_permutationUnipotentMinus_iff`. The left side
lies in `B`, so it is the identity. Hence `b = b'`, and left cancellation
gives `v = v'`.

## Surjectivity

`exists_minus_conj_upper`: for `b ∈ B`, set
`Q c k := k < c ∧ w c < w k` and `Y = columnSolve Q b`.

- `Y` is upper triangular with unit diagonal. Outside `Q` it agrees with the
  identity, and `Q c k` forces `k < c`. Hence `det Y = 1 ≠ 0`, and
  `y = Matrix.GeneralLinearGroup.mkOfDetNeZero Y` is an actual matrix unit.
- `y ∈ N` by the published `mem_permutationUnipotentMinus_iff_entries`.
  If `w i < w j`, then `Q j i` fails and `i ≠ j`, so `Y i j = 0`.
- `p * (b * y) * p⁻¹ ∈ B`. By `permutation_conjugate_entry`, its entry at
  `(i, j)` is `(b * Y) (w⁻¹ i) (w⁻¹ j)`. Let `j < i`, and write
  `k = w⁻¹ i` and `c = w⁻¹ j`. If `c < k`, the entry vanishes because
  `b * Y` is upper triangular. The case `c = k` is impossible. If `k < c`,
  then `Q c k` holds, because `w c = j < i = w k`. By
  `mul_columnSolve_apply` the entry vanishes; the block `b_{Q c}` is
  invertible by `det_toBlock_ne_zero_of_upper` and `diag_ne_zero_of_upper`.

`upperBruhatCellMap_surjective`: write a cell element as `b₁ * p * b₂` with
`b₁, b₂ ∈ B`. Take `y` for `b₂`, and use the coordinates
`(b₁ * (p * (b₂ * y) * p⁻¹), y⁻¹)`. Their image is
`b₁ * p * b₂ * y * p⁻¹ * p * y⁻¹ = b₁ * p * b₂`, by the `group` tactic.

`cellEquiv` is `Equiv.ofBijective` of the published `upperBruhatCellMap n K w`.
Its forward function is that map by definition (`cellEquiv_apply`).

## Recovery of the coordinates

Fix coordinates `x = (b, v)` and let `g` be their image in `C`. Write
`L = p * v⁻¹ * p⁻¹`.

- `recover_mem_lowerUnipotent`: `L` is lower unipotent, because `v⁻¹ ∈ N`.
- `recover_mul`: `(g * p⁻¹) * L = b` as matrices.
- `det_toBlock_recover_ne_zero`: for every `c`, the bottom-right principal
  block of `g * p⁻¹` on the indices `{k | c < k}` has nonzero determinant.
  `L` has no nonzero entries `(k, t)` with `k ≤ c < t`. By
  `toBlock_mul_of_support`, the block of `b` on these indices equals the
  block of `g * p⁻¹` times the block of `L`. The block of `b` has nonzero
  determinant by `det_toBlock_ne_zero_of_upper`, so the determinant of the
  block of `g * p⁻¹` is nonzero.
- `recover_eq`: `L = columnSolve (fun c k => c < k) (g * p⁻¹)`. This is
  `eq_columnSolve`: column `c` of `L` is `e c` above and on the diagonal, and
  `((g * p⁻¹) * L) r c = b r c = 0` for `r > c`.

These are the rational entry formulas: the entries of `L` are built from
entries of `g * p⁻¹` and the inverses of its bottom-right principal blocks.

## Continuity of the inverse and the first homeomorphism

`continuous_cellEquiv_symm`: let `M g = (g * p⁻¹).val`, which is continuous
on `C`. Applying `det_toBlock_recover_ne_zero` to the coordinates
`(cellEquiv w).symm g` shows that every block of `M g` used by the column
solve is invertible, for every `g ∈ C`. Thus `S g = columnSolve (c < k) (M g)`
is continuous by `continuous_columnSolve`. By `recover_eq`, the matrix value
of `v⁻¹` is `p⁻¹ * S g * p` as matrices. So `g ↦ v⁻¹` is continuous into the
general linear group by `continuous_generalLinear_of_val`. Group inversion
then makes `g ↦ v` continuous, and the subtype embedding makes it continuous
into `N`. Finally `b = g * v⁻¹ * p⁻¹` is continuous into `B`. The pair of
these two maps is the inverse.

`cellHomeomorph` packages `cellEquiv` with the published forward continuity
`continuous_upperBruhatCellMap` and this inverse continuity.
`cellHomeomorph_apply` states that its value is `upperBruhatCellMap n K w x`
by `rfl`. This is the first conjunct.

## Torus coordinates

`diagUnit b i` is the diagonal entry `b i i` of `b ∈ B`, as a unit
`Units.mk0 (b i i) _`.

`torusSplitEquiv : U × (Fin n → Kˣ) ≃ B` has

- forward map `torusSplitFun w (u, d) = u * diagonalUnits (d ∘ w⁻¹)`, which
  lies in `B` by `upperUnipotent_le_upperTriangular` and
  `diagonalUnits_mem_upperTriangular`;
- inverse map
  `torusSplitInv w b = (b * diagonalUnits (i ↦ (diagUnit b i)⁻¹), j ↦ diagUnit b (w j))`,
  whose first component lies in `U` because each diagonal entry is
  `b i i * (b i i)⁻¹ = 1`.

The two inverse laws use `diagUnit_torusSplitFun`, which shows that
`diagUnit (torusSplitFun w (u, d)) i = d (w⁻¹ i)` because `u ∈ U` has unit
diagonal. They also use the
fact that `Iwasawa.diagonalUnits` is a group homomorphism. `torusSplit`
upgrades this equivalence to a homeomorphism. Forward continuity uses
continuity of multiplication and the published `continuous_diagonalUnits`.
Inverse continuity uses `continuous_diagUnit`, which is continuous into
`Kˣ` because `Units.isEmbedding_val₀` identifies the units topology of a
topological division ring with the subspace topology. It also uses continuity
of inversion on `Kˣ`.

`torusHomeomorph` is the composite of the following homeomorphisms:

- `Homeomorph.prodAssoc` (inverted) from `U × ((Fin n → Kˣ) × N)` to
  `(U × (Fin n → Kˣ)) × N`;
- `torusSplit × id`;
- `cellHomeomorph`.

`torusHomeomorph_apply_val` computes its value at `(u, d, v)`:
`u * diagonalUnits (d ∘ w⁻¹) * p * v`. By `permutation_mul_diagonalUnits`,
`p * diagonalUnits d = diagonalUnits (d ∘ w⁻¹) * p`, so the value equals
`u * p * diagonalUnits d * v`, which is the required torus order. This is the
second conjunct.

## Main theorem and scope

`upperBruhatCoordinates` introduces `K`, its instances, `n` and `w`. It
supplies `cellHomeomorph w` with the pointwise equality `rfl`, and
`torusHomeomorph w` with `torusHomeomorph_apply_val w`.

The hypothesis `T2Space K` is part of the statement but is not used by the
proof. Only `IsTopologicalDivisionRing K` is used, through continuity of the
ring operations and of inversion at nonzero points. Rank zero needs no
separate case: every argument above is uniform in `n`. The proof uses only
the axioms `propext`, `Classical.choice` and `Quot.sound`.

## Provenance

The statement's source is Lemma 1.7 of J. A. Shalika, *The multiplicity one
theorem for GLn*, Ann. of Math. (2) 100 (1974), 171–193 (registered as
`shalika-1974-multiplicity-one`, printed pp.175–176), as explained in the
statement's Markdown. Shalika's proof works over local fields and uses local
compactness and the Arens–Pontryagin open-mapping theorem. This Lean proof
follows a different, internal route: explicit column elimination with
principal-block inverses. That route covers every topological field and does
not use local compactness. It follows the recovery plan sketched in the
statement's Markdown. It does not use the separate plus-minus factorization
task.
