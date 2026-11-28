# Block diagonal matrices along disjoint two-by-two slots

Lean module: `Langlands.Global.RankinSelberg.RealSlotMatrices`.

This is a helper module of the proof of
`Langlands.Global.RankinSelbergGlobal.RealTemperedWhittaker.RealTemperedWhittakerBoundStatement`
(see `RealTemperedWhittakerBoundProof.md`). It states no `Prop`-valued statement; it proves lemmas
only. The content is internal and follows no literature source. Unprefixed names are in the
namespace `Langlands.Global.RankinSelbergGlobal.RealLeviStages`. `torus`, `alpha`, `npart` and
`kpart` are the positive diagonal matrices and the Iwasawa coordinates of the module
`RealIwasawa`.

The module provides the matrix algebra of a Levi subgroup whose blocks are two-by-two "slots"
and one-by-one blocks. The open cell of each two-by-two block is decomposed in Iwasawa form, and
these decompositions are put together on `GL_N(ℝ)`.

## Slot sets

- `SlotSet N` is a finite set `starts` of natural numbers `p` with `p + 1 < N` and `p + 1 ∉ starts`
  for every `p ∈ starts`. The slot of `p` is the pair of positions `p, p + 1`; two slots are
  disjoint.
- `SlotSet.diag S A` is the block diagonal matrix with the two-by-two block `A p` on every slot
  `p` and the identity elsewhere. `InSlot S i p o` says that the position `i` is the entry
  `o ∈ {0, 1}` of the slot `p`; `first` and `second` are the two positions of a slot. `diag_row`,
  `diag_row_other` give the rows of `diag`; `diag_mul`, `diag_one`, `diag_transpose` show that
  `diag` is multiplicative and commutes with transposition. `diagGL` and `diagGL_mul` are the same
  for invertible blocks, and `diagGL_mem_unitaryCompact` shows that orthogonal blocks give an
  orthogonal matrix.
- `SlotSet.perm` swaps the two positions of every slot (`perm_perm`), and `perm_lt_perm` shows
  that it preserves the order of two positions not in one slot.

## Two-by-two blocks

`upper2 x = [[1, x], [0, 1]]`, `swap2 = [[0, 1], [1, 0]]`, `rot2 θ` is the rotation by `θ`,
`diag2 u v = diag(e^u, e^v)`, and `cellNorm x = √(1 + x²)`. `swap2_mul_upper2` is the Iwasawa
decomposition of the rank-two open cell:
`[[0, 1], [1, x]] = diag(ρ⁻¹, ρ) [[1, x], [0, 1]] r(arctan x) [[0, 1], [1, 0]]`, `ρ = cellNorm x`.

## The slot matrices

- `unip S x`, `swapGL S`, `rot S θ` and `diagE S u v` put `upper2 (x p)`, `swap2`, `rot2 (θ p)` and
  `diag2 (u p) (v p)` on the slots. `unip_mul`, `unip_zero`: `x ↦ unip S x` is a homomorphism;
  `unip_mem`: it is upper unipotent. `swapGL_mem`, `rot_mem`: the slot swap and the rotations
  are orthogonal. `swapGL_eq_permutation`: the slot swap is the permutation matrix of `perm`.
- `slotVec S u v` is the vector with `u p, v p` on the slot `p` and `0` elsewhere
  (`slotVec_of_inSlot`, `slotVec_of_not_inSlot`); `diagE_eq_torus` identifies `diagE S u v` with
  `torus (slotVec S u v)`, and `slotVec_perm` shows `slotVec u (-u) ∘ perm = -slotVec u (-u)`.
- `unip_mul_torus` and `swapGL_mul_torus` move a positive diagonal matrix `torus α` past the slot
  unipotent (rescaling `x p` by `exp(α_{p+1} - α_p)`, see `natVec`, `shifted`) and past the slot
  swap (permuting `α` by `perm`).
- `swapGL_mul_unip` is `swap2_mul_upper2` in every slot at once.

## The Iwasawa decomposition of `w_M n_M(x) g`

- `slotCoord u p` is the entry `(p, p + 1)` of a matrix `u` (`slotCoord_eq`);
  `unip_slot_entry` computes it for `unip S x`; `unipotent_mul_adjacent` adds adjacent upper
  entries of a product of unipotent matrices.
- `unip_mul_unipotent`: `unip S x · n = u · unip S (x + slotCoord n)` for an upper unipotent `n`,
  with `u` upper unipotent and zero on the slot entries. `swapGL_conj_mem`: conjugation by the
  slot swap keeps such a `u` upper unipotent.
- `cellExponent S y = slotVec S (-log ρ(y_p)) (log ρ(y_p))` is the logarithmic diagonal of the
  triangular parts of the rank-two cells. `swapGL_unip_torus` is the Iwasawa form of
  `swapGL S · unip S x · torus α`.
- `swapGL_unip_mul` is the Iwasawa decomposition of `swapGL S · unip S x · g` in terms of that of
  `g`: with `y = shifted (x + slotCoord (npart g)) (alpha g)`, the diagonal coordinate is
  `alpha g ∘ perm + cellExponent S y` (`alpha_swapGL_unip_mul`) and the orthogonal part is
  `rot S (arctan y) · swapGL S · kpart g` (`kpart_swapGL_unip_mul`).
- `sum_mul_perm_add_cellExponent`: a weight `w` with `w ∘ perm = w` pairs with
  `α ∘ perm + cellExponent S y` as with `α`.
