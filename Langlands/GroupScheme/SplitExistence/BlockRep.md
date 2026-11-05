# Integral representations of `SL₂` attached to one root (`BlockRep`)

Author: Worker 239.

Fix `α : X` and an additive map `pair : X →+ ℤ`, which stands for `⟨·, α^∨⟩`. This module packages
an integral representation of `SL₂` along `α` as a structure. It then builds such
representations from string decompositions (`StringRep`) and from the Cartan block of
`WeylModule`.

## The structure `SL2Rep B wt α pair`

For a finite index type `B` with weights `wt : B → X`, an `SL2Rep B wt α pair` consists of:

- integral matrices `E k`, `F k : Matrix B B ℤ`, the divided powers of a raising and a
  lowering operator;
- matrices `rep R g : Matrix B B R` for every commutative ring `R` (in a fixed universe) and
  every `2 × 2` matrix `g`.

They satisfy the following fields:

- `rep_mul`: `rep` is multiplicative on matrices of determinant one. `rep_one`: `rep R 1 = 1`.
  `rep_map`: `rep` is natural in `R`.
- `rep_upper`, `rep_lower`: at `[[1, s], [0, 1]]` and `[[1, 0], [s, 1]]`, `rep` is the
  truncated exponential `Σ_{k<N} s^k E^[k]`, respectively `Σ_{k<N} s^k F^[k]`, for every
  `N > 3`.
- `rep_diag`: `rep diag(t, t⁻¹)` is diagonal with entries `t^(pair (wt d))` for a unit `t`.
- `rep_weyl`: a nonzero entry `(r, c)` of `rep [[0, 1], [−1, 0]]` has
  `wt r = wt c − pair (wt c) • α`.
- `E_zero`, `F_zero`, `E_mul`, `F_mul`: the divided-power laws. `E_eq_zero`, `F_eq_zero`:
  vanishing in degrees above `3`.
- `E_weight`, `F_weight`: `E^[k]` shifts weights by `k • α`, and `F^[k]` shifts them by `−k • α`.
- `E_one_mul_F_one_sub`: `[E, F]` is the diagonal matrix of the pairings `pair (wt d)`.

## Constructions

- `StringDecomp.toSL2Rep`: if `pair α = 2`, then a string decomposition `S` of the weights
  gives an `SL2Rep` with `rep R g = S.rep g`, `E = S.E` and `F = S.F` (`toSL2Rep_E`,
  `toSL2Rep_F`). Each field is the corresponding lemma of `StringRep`. Multiplicativity holds
  even without the determinant condition.
- `SL2Rep.ofCartan i₀ c σ S`: given a finite type `ι`, an index `i₀ : ι` with `c i₀ = 2`, a
  string decomposition `S` of a family `ωC : C → X`, and an equivalence
  `σ : B ≃ (Fin 2 ⊕ ι) ⊕ C`, assume that the weights on the first summand are
  `cartLevel r • α` (that is, `−α`, `α` and `0`) and that those on `C` are `ωC`. Then the
  block-diagonal sum of the Cartan block `cart i₀ c` (with operators `cartE`, `cartF`) and of
  `S` is an `SL2Rep`. It is transported to `B` along `σ` with `submatrix`. Each field has its
  own lemma (`ofCartan_rep_mul`, `ofCartan_rep_one`, `ofCartan_rep_map`, `ofCartan_rep_upper`,
  `ofCartan_rep_lower`, `ofCartan_rep_diag`, `ofCartan_rep_weyl`, `ofCartan_E_zero`,
  `ofCartan_F_zero`, `ofCartan_E_mul`, `ofCartan_F_mul`, `ofCartan_E_eq_zero`,
  `ofCartan_F_eq_zero`, `ofCartan_E_weight`, `ofCartan_F_weight`,
  `ofCartan_E_one_mul_F_one_sub`). Each is proved by multiplying block matrices and applying
  the lemma for each block. The following helpers support them:
  - `fromBlocks_ne_zero` locates nonzero entries of a block-diagonal matrix;
  - `wt_eq_of_cartan` describes the weights through `σ`;
  - `sum_fromBlocks_submatrix` moves truncated exponential sums inside the blocks;
  - `ofCartan_diagonal` writes the diagonal of pairings blockwise as `2 · cartLevel` and
    `pair ∘ ωC`.

  `SL2Rep.ofCartan_E` and `SL2Rep.ofCartan_F` record the operators.
- `SL2Rep.reindex V e`: transport along an equivalence `e : B ≃ B'`, with
  `reindex_E`, `reindex_F`.
- `SL2Rep.hom V R : SL₂(R) →* GL_B(R)`: the group homomorphism `g ↦ rep R g`, which is
  well-defined by `rep_mul` and `rep_one` (`MonoidHom.toHomUnits`). `coe_hom` records its
  underlying matrix.

## Provenance

The structure is internal packaging. Mathematically, an `SL2Rep` is a representation of the
group scheme `SL₂` over `ℤ` on a free module with a weight grading, together with the
divided-power (Kostant) ℤ-form of the action of `e` and `f` (Steinberg, *Lectures on Chevalley
groups*, §2; Humphreys, *Introduction to Lie Algebras and Representation Theory*, §26.4). The
module proves only the properties listed above, for the explicit block constructions.
