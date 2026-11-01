# The Section 4.7 lower block-unipotent quotient and its character

Module `Langlands.Representation.RankinSelberg.TwoBlockLowerUnipotentQuotientData`,
namespace `Langlands.RankinSelberg.TwoBlockLowerUnipotentQuotient`.

Authors: Worker 1179 and Worker 243.

This module is a definitions unit for the right side of JPSS (1983), Section
4.7, equation (1). It constructs the block rotation `C = w'`, the subgroup
`H⁻ = C⁻¹ N C` with its block description, the conjugation isomorphism
`H⁻ ≃* N`, the left quotient `H⁻ \ GL_(t+1)` with its identification
`[g] ↦ [C g]` with `N \ GL_(t+1)`, the character of `H⁻` pulled back from the
standard character of `N`, and the determinant order and slices of the
quotient. These are internal infrastructure for the source objects. They are
not a numbered theorem of the original, and the module does not prove
equation (1) or its convergence.

## Source and conventions

Source: Jacquet, Piatetski-Shapiro and Shalika, *Rankin–Selberg convolutions*
(1983), source ID `jpss-1983-rankin-selberg`, Section (4.7). The printed pages
412–413 are zero-based PDF indices 46–47. No errata note for this source exists
in the project literature.

- On printed page 412, equation (1) of (4.7) has on its right side an integral
  over `H_(t_1,t_2) \ G_r` whose integrand contains
  `W[w_r (w_(t_1) 0; 0 w_(t_2)) g]`.
- On printed page 413, `H_(t_1,t_2)` is the unipotent subgroup of `G_r` of all
  matrices `(n_1 0; x n_2)` with `n_i ∈ N_(t_i)`, and the source writes
  `w' = w_r (w_(t_1) 0; 0 w_(t_2))`.

The correspondence with this module is as follows.

| JPSS | Here |
| --- | --- |
| block ranks `t_1`, `t_2` | `a = m 0 + 1`, `b = m 1 + 1` |
| total rank `r = t_1 + t_2` | `N = t + 1`, with `h : ∑ i, (m i + 1) = t + 1` |
| block shape | `B = succBlockShape m h` |
| `G_r` | `GeneralLinear (t + 1) R` |
| `N_r` | `upperUnipotent (t + 1) R` |
| `w_r`, `w_(t_i)` | `weylLong (t + 1) R`, `weylLong (m i + 1) R` |
| `w' = w_r diag(w_(t_1), w_(t_2))` | `blockRotation h R` |
| `H_(t_1,t_2)` | `lowerBlockUnipotent h R` |
| `H_(t_1,t_2) \ G_r` | `LowerQuotient h R` |

The block ranks `m 0 + 1` and `m 1 + 1` are arbitrary positive numbers, and
`t` is arbitrary. The algebraic constructions hold over an arbitrary
commutative ring `R` in an arbitrary universe. Topological statements assume
only `[TopologicalSpace R] [IsTopologicalRing R]`, and `[T2Space R]` where
stated. The `p`-adic specializations use the canonical topology
`F.canonicalTopologicalData.topology` of a canonical `p`-adic field
`F : PadicField.{uF} p`. The module has no representation, Whittaker-type,
irreducibility or factor-existence premise.

Write `σ = B.reversePermutation`, the published permutation sending
coordinates of the reversed shape `B.reverse` (block ranks `b`, `a`) to
coordinates of `B`. The block ordering is the published `B.index`: block `0`
occupies positions `0, …, a - 1` and block `1` positions `a, …, N - 1`.

## The block rotation (section `Rotation`)

- `blockRotation h R = (B.reverseMatrix R)⁻¹` is the matrix `C`, the inverse of
  the published block-reversing matrix. `blockRotation_eq_permutation`
  identifies it with the permutation matrix of `σ⁻¹`, and
  `blockRotation_apply` gives `C k l = 1` if `σ⁻¹ l = k` and `0` otherwise.
- Source identity: `blockRotation_eq_weylLong_mul_leviEmbedding` proves
  `C = weylLong (t + 1) R * B.leviEmbedding R (fun i => weylLong (m i + 1) R)`,
  that is `w' = w_N diag(w_a, w_b)`. Its proof compares columns, using
  `leviEmbedding_weylLong_apply_index` (column `y` of block `j` of
  `diag(w_a, w_b)` is the unit vector at coordinate `y.rev` of the same
  block) and `reversePermutation_symm_index_eq_rev`
  (`σ⁻¹ (B.index j y) = (B.index j y.rev).rev`).
- Coordinate laws. `val_reversePermutation_symm_index_zero` and
  `val_reversePermutation_symm_index_one` say that `σ⁻¹` sends coordinate `x`
  of block `0` to position `b + x` and coordinate `y` of block `1` to position
  `y`. `reversePermutation_symm_index_zero` and
  `reversePermutation_symm_index_one` state the same in the coordinates of the
  reversed shape, which is `succBlockShape (fun i => m i.rev) (reverse_sum h)`
  (`reverse_succBlockShape`, by `rfl`). `reversePermutation_symm_index_lt`
  says that `σ⁻¹` preserves the order of coordinates inside each block.
  `blockRotation_apply_index_zero` and `blockRotation_apply_index_one` give
  the columns of `C`: column `x` of block `0` is the unit vector at position
  `b + x`, and column `y` of block `1` is the unit vector at position `y`.
  So `C` moves the original first block behind the original second block and
  does not reverse coordinates inside either block. `C` is the inverse of
  `B.reverseMatrix R`, not that matrix itself; the two differ in general when
  `a ≠ b` (this remark is not formalized).
- Inverse laws: `blockRotation_inv` (`C⁻¹ = B.reverseMatrix R`),
  `blockRotation_mul_reverseMatrix`, `reverseMatrix_mul_blockRotation`,
  `blockRotation_inv_apply`, `blockRotation_inv_apply_index_zero` and
  `blockRotation_inv_apply_index_one`.
- Multiplication and conjugation: `blockRotation_mul_apply`
  (`(C g) k l = g (σ k) l`), `blockRotation_conj_apply`
  (`(C g C⁻¹) k l = g (σ k) (σ l)`), `blockRotation_conj_apply_symm`,
  `blockRotation_inv_conj_apply` (`(C⁻¹ n C) k l = n (σ⁻¹ k) (σ⁻¹ l)`) and
  `blockRotation_conj_apply_reverse_index`, which reads `C g C⁻¹` in the
  reversed block coordinates: reversed block `i` is original block `i.rev`.
- `exists_index_eq` says that every coordinate is `B.index i x` for some block
  `i` and coordinate `x`.

## The subgroup `H⁻` (sections `Subgroup`, `Topology`, `Canonical`)

- `lowerBlockUnipotent h R` is the subgroup
  `(upperUnipotent (t + 1) R).comap (MulAut.conj C).toMonoidHom`, so
  `g ∈ H⁻` iff `C g C⁻¹ ∈ N` (`mem_lowerBlockUnipotent_iff_conj`, by `Iff.rfl`).
- Block criterion `mem_lowerBlockUnipotent_iff`: `g ∈ H⁻` exactly when
  1. the upper-right `a × b` block vanishes:
     `g (B.index 0 x) (B.index 1 y) = 0` for all `x`, `y`;
  2. inside each diagonal block, strictly lower entries vanish:
     `g (B.index i x) (B.index i y) = 0` when `y < x`;
  3. the diagonal entries are one: `g (B.index i x) (B.index i x) = 1`.

  The lower-left `b × a` block is not constrained. The two directions are
  `blocks_of_mem_lowerBlockUnipotent` and `mem_lowerBlockUnipotent_of_blocks`.
  The second uses `entry_eq_zero_of_reversePermutation_symm_lt`: a pair of
  block positions that `σ⁻¹` places strictly below the diagonal lies in the
  upper-right block or strictly below the diagonal of a diagonal block.
  `index_zero_one_eq_zero` restates condition 1 for members.
- The displayed form `(n_a 0; X n_b)`. `lowerBlockUnipotent_le_oppositeParabolic`
  places `H⁻` in the published lower block parabolic
  `B.oppositeParabolic R`. `diagonalBlocks h R : H⁻ →* BlockUnipotents m R`
  takes the two diagonal blocks with the published opposite Levi projection,
  as elements of the published product
  `TwoBlockUnipotentQuotient.BlockUnipotents m R` of the block
  upper-unipotent groups (`oppositeLeviProjection_mem_upperUnipotent`).
  `diagonalBlocks_apply` gives its entries.
  `mem_lowerBlockUnipotent_iff_blocks` states: `g ∈ H⁻` iff the upper-right
  block vanishes and the diagonal blocks of `g` are those of some
  `(n_a, n_b) ∈ N_a × N_b`.
- The lower-left block is arbitrary. For every `X : Matrix (Fin b) (Fin a) R`,
  `lowerRadical h R X = C⁻¹ u'(X) C` is the matrix `(1 0; X 1)`, where `u'(X)`
  is the published upper radical matrix `TwoBlockJacquet.upperRadical` of the
  reversed shape. Its four blocks are `lowerRadical_index_one_zero` (`X`),
  `lowerRadical_index_zero_one` (`0`), and `lowerRadical_index_zero_zero` and
  `lowerRadical_index_one_one` (identity). `lowerRadical_mem` proves that it
  lies in `H⁻`.
- `conjugationEquiv h R : lowerBlockUnipotent h R ≃* upperUnipotent (t + 1) R`
  sends `g` to `C g C⁻¹`, with inverse `n ↦ C⁻¹ n C`. The representative laws
  are `conjugationEquiv_apply_val` and `conjugationEquiv_symm_apply_val`.
- `determinant_eq_one_of_mem_lowerBlockUnipotent`: every element of `H⁻` has
  determinant one, since `det (C g C⁻¹) = det g`.

Topology. For a topological ring, `continuous_conjugationEquiv` and
`continuous_conjugationEquiv_symm` give continuity in both directions, and
`conjugationHomeomorph h R : lowerBlockUnipotent h R ≃ₜ* upperUnipotent (t + 1) R`
packages the equivalence (`conjugationHomeomorph_toMulEquiv`). For a Hausdorff
topological ring, `isClosed_lowerBlockUnipotent` proves that `H⁻` is closed:
it is the preimage of the closed group `N` (`UpperUnipotent.isClosed`) under
the continuous map `g ↦ C g C⁻¹`. The canonical `p`-adic specializations are
`canonicalConjugationHomeomorph`, `canonicalConjugationHomeomorph_toMulEquiv`,
`continuous_conjugationEquiv_canonical`,
`continuous_conjugationEquiv_symm_canonical` and
`isClosed_lowerBlockUnipotent_canonical`.

## The quotient `H⁻ \ GL_(t+1)` (sections `Quotient` to `QuotientCanonical`)

- `LowerQuotient h R` is the actual left quotient
  `QuotientIntegration.LeftQuotient (lowerBlockUnipotent h R)`, the quotient by
  `g ~ g'` iff `g' g⁻¹ ∈ H⁻`, with the quotient topology.
- `rightRel_iff_blockRotation_mul`: `g ~ g'` for `H⁻` iff `C g ~ C g'` for `N`.
- `lowerToStandard h R : LowerQuotient h R ≃ LeftQuotient (upperUnipotent (t + 1) R)`
  is left multiplication by `C` on representatives. The representative
  formulas are `lowerToStandard_mk` (`[g] ↦ [C g]`) and
  `lowerToStandard_symm_mk` (`[g] ↦ [C⁻¹ g]`). The inverse laws are
  `lowerToStandard_symm_apply_apply` and `lowerToStandard_apply_symm_apply`.
- Descent: `mk_blockRotation_mul_of_mem` says `[C (u g)] = [C g]` for
  `u ∈ H⁻`, and `lowerToStandard_eq_descend` identifies `lowerToStandard` with
  `QuotientIntegration.descend` of `g ↦ [C g]`.
- Right multiplication: `lowerToStandard_mk_mul` gives
  `lowerToStandard [x g] = [(C x) g]`. For a topological ring,
  `lowerToStandard_rightTranslate` and `lowerToStandard_symm_rightTranslate`
  prove that `lowerToStandard` and its inverse commute with the published
  `QuotientIntegration.rightTranslate` by every `g ∈ GL_(t+1)(R)`. Left
  multiplication by `C` is used, not conjugation of quotients, which would
  change the right action.
- Field case: for a field `K`, `lowerToLeftUnipotentQuotient h K` is
  `lowerToStandard h K` with codomain the published
  `LeftUnipotentQuotient t K` (`lowerToLeftUnipotentQuotient_eq`,
  `lowerToLeftUnipotentQuotient_mk`, `lowerToLeftUnipotentQuotient_symm_mk`).
- Topology: `lowerToStandardHomeomorph h R` is the homeomorphism of the
  quotient topologies obtained from the homeomorphism `g ↦ C g` of
  `GL_(t+1)(R)` (`lowerToStandardHomeomorph_toEquiv`,
  `lowerToStandardHomeomorph_apply`, `continuous_lowerToStandard`,
  `continuous_lowerToStandard_symm`). `t2Space_lowerQuotient` proves that the
  quotient is Hausdorff over a Hausdorff topological ring, by the published
  `leftQuotient_t2Space` and the closedness of `H⁻`.
- Canonical `p`-adic specializations: `canonicalLowerToStandardHomeomorph`
  (codomain `LeftUnipotentQuotient t F.Carrier`),
  `canonicalLowerToStandardHomeomorph_apply`, `t2Space_lowerQuotient_canonical`
  and `lowerToStandard_rightTranslate_canonical`.

## The character of `H⁻` (sections `Character`, `CanonicalCharacter`)

`lowerCharacter h ψ : lowerBlockUnipotent h R →* ℂˣ` is defined by pullback: it is
`(standardCharacter ψ t).comp (conjugationEquiv h R).toMonoidHom`, the standard character
of `N_N` composed with `g ↦ C g C⁻¹`. JPSS (1983), Section 4.7 (printed pages 412-413)
displays no character of `H_(t_1,t_2)`. This character is internal infrastructure. It is
motivated by the factor `W[w' g]` in the integrand of equation (1): for a Whittaker function
`W` one has `W(w' h g) = θ(w' h w'⁻¹) W(w' g)`. That remark is not formalized here. The block
formula below is derived here from the published standard character after conjugation by
`C`. It is not a verbatim theorem of the source.

- `lowerCharacter_apply` and `lowerCharacter_apply_coe` give the evaluation laws. The value
  is `ψ.complex` of the first-superdiagonal sum of `C g C⁻¹`.
- `norm_lowerCharacter` states that every value has norm one.
- `sum_superdiagonal_conj_blockRotation` holds for every `g : GL_N(R)`. It says the
  first-superdiagonal sum of `C g C⁻¹` equals the internal superdiagonal sum of the first
  original block, plus that of the second original block, plus the corner entry
  `g (B.index 1 (Fin.last (m 1))) (B.index 0 0)`. The corner lies in the last row of the
  second block and the first column of the first block. The proof applies the published
  `TwoBlockDeformation.sum_superdiagonal_index` to the reversed shape
  `succBlockShape (fun i => m i.rev) (reverse_sum h)`. It then uses
  `blockRotation_conj_apply_reverse_index`: reversed block `0` is original block `1` and
  reversed block `1` is original block `0`, and coordinates inside a block keep their order.
  If a block has rank one (`m i = 0`), its internal sum is empty. Such blocks are allowed,
  and the formula still holds for them.
- `lowerCharacter_apply_blocks` is this explicit formula for `g ∈ H⁻`, in the
  original `B.index` coordinates.
- `lowerCharacter_eq_of_blocks` and `lowerCharacter_eq_diagonalBlocks` give the block-factor
  form. For `g = [[n_a, 0], [X, n_b]]` the value is
  `θ_a(n_a) · θ_b(n_b) · ψ(X(last_b, first_a))`, where `θ_a = standardCharacter ψ (m 0)`
  and `θ_b = standardCharacter ψ (m 1)`. The first lemma takes any block representatives
  `n : TwoBlockUnipotentQuotient.BlockUnipotents m R` that agree with the diagonal blocks of
  `g` entrywise. The second uses the actual diagonal blocks `diagonalBlocks h R g`.
- When `R` is a topological ring, `lowerCharacterContinuous h ψ` packages the character as
  a `ContinuousMonoidHom` into `ℂˣ`, and `continuous_lowerCharacter` states its continuity.
  The proof composes `standardCharacterContinuous ψ t` with
  `continuous_conjugationEquiv`.

Canonical `p`-adic specialization: for a p-adic field `F`, `canonicalLowerCharacterContinuous F h ψ` and
`continuous_lowerCharacter_canonical F h ψ` specialize the continuous character to the
topology `F.canonicalTopologicalData.topology`. No other topology is introduced.

## Determinant order and slices (section `Padic`)

- `determinant_blockRotation` holds over any commutative ring: `det C` is the sign of
  `B.reversePermutation`, because `C` is a permutation matrix. Hence
  `determinant_blockRotation_mul_self` gives `det C · det C = 1`.
- For a p-adic field `F` with its canonical structure `T = F.canonicalTopologicalData`,
  `ord_determinant_blockRotation` proves `T.ord (det C) = 0`, using `ord_mul` and
  `ord_one`. Then `normalizedAbs_determinant_blockRotation` proves
  `T.normalizedAbs (det C) = 1`.
- `determinantOrder F h : LowerQuotient h F.Carrier → ℤ` is defined by transport. It is the
  published `RankinSelberg.determinantOrder T t` (JPSS (4.2.1)) composed with
  `lowerToStandard h F.Carrier`. Likewise `determinantSlice F h k` is the preimage of the
  published `RankinSelberg.determinantSlice T t k` under `lowerToStandard`.
- `determinantOrder_mk` is the representative law `determinantOrder F h [g] = T.ord (det g)`.
  It holds because `lowerToStandard [g] = [C g]` and `ord(det C) = 0`.
  `mk_mem_determinantSlice` gives the matching criterion for slice membership.
- The slice correspondence under `lowerToStandard` is exact.
  `image_lowerToStandard_determinantSlice` says its image is the published slice, and
  `preimage_lowerToStandard_symm_determinantSlice` says the same for the preimage under the
  inverse. `mem_determinantSlice` and `mem_determinantSlice_iff_determinantOrder` unfold
  membership.
- The following laws use the canonical topology:
  - `continuous_determinantOrder` states continuity of the order, proved through the
    quotient map and the continuity of `ord ∘ det`;
  - `isClopen_determinantSlice`, `isOpen_determinantSlice` and `isClosed_determinantSlice`
    state that slices are clopen;
  - `measurableSet_determinantSlice` states measurability for any Borel structure on the
    quotient.
- `disjoint_determinantSlice` and `pairwise_disjoint_determinantSlice` state that the slices
  are pairwise disjoint, and `iUnion_determinantSlice` that their union is the whole
  quotient.
- `determinantOrder_rightTranslate` is the right-translation shift. For every
  `g ∈ GL_N(F)`, `determinantOrder F h (rightTranslate _ g q) = determinantOrder F h q +
  T.ord (det g)`, using the existing `QuotientIntegration.rightTranslate` convention.
  `rightTranslate_mem_determinantSlice` is the corresponding slice statement.

## What is not asserted

This module asserts none of the following:

- Section 4.7, equation (1), or its convergence;
- a Haar normalization, a quotient-measure transfer, a measure tower,
  integration or convergence theorem;
- descent of a representation integrand, Fourier closure or inversion, a
  Mellin identity, a block functional equation or factor multiplicativity.
