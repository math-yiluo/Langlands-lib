# Block embeddings of binary SL into ternary SL

Module `Langlands.GroupScheme.SpecialLinearTernaryPresentation`, namespace
`Langlands.GroupScheme.SpecialLinear.TernaryPresentation`.

This internal module is plain matrix algebra: it has no schemes or functors. It
sets up the two block copies of `SL₂` inside `SL₃`, the outer involution of `SL₃`
that exchanges them, its relation to the Library's quasi-split `SU₃` twist, and
the fact that over a field the two block copies generate `SL₃`. It imports the
binary presentation module (for the unipotent matrices `upper t`, `lower t`) and
`GroupScheme.Examples.SU3MatrixFixedPoints` (for `SU3Root`). Coefficient rings
live in universe `u`, a second ring in universe `v`, and the target group of
`hom_ext` in universe `w`. All statements are internal and every step is proved
in Lean; no literature theorem is used.

Notation: `SL2 R` and `SL3 R` are local notations for
`Matrix.SpecialLinearGroup (Fin 2) R` and `Matrix.SpecialLinearGroup (Fin 3) R`.

## Block embeddings (section `Blocks`, `R` a commutative ring)

- `leftMatrix g` is the `3 × 3` matrix with `g` in rows and columns `0, 1` and a
  `1` at position `(2, 2)`; `rightMatrix g` has `g` in rows and columns `1, 2`
  and a `1` at position `(0, 0)`. All other entries are `0`.
- `det_two` expands `det g = 1` for `g : SL2 R`; `det_leftMatrix` and
  `det_rightMatrix` show the block matrices have determinant `1`.
- `left, right : SL2 R →* SL3 R` are the two block embeddings, with
  `coe_left`, `coe_right` giving their underlying matrices.
- `left_injective`, `right_injective`: both embeddings are injective.
- `map_left`, `map_right`: both embeddings commute with
  `SpecialLinearGroup.map f` for a ring homomorphism `f : R →+* S`.

Thus `left (upper t)` is the elementary matrix `1 + t E₀₁`, `left (lower t)` is
`1 + t E₁₀`, `right (upper t)` is `1 + t E₁₂` and `right (lower t)` is
`1 + t E₂₁`.

## Outer involution (section `Outer`)

- `antidiagonal` is the matrix `J = [0, 0, 1; 0, -1, 0; 1, 0, 0]`, with
  `antidiagonal_mul_self` (`J² = 1`), `det_antidiagonal` (`det J = 1`),
  `transpose_antidiagonal` (`Jᵀ = J`) and `map_antidiagonal` (`J` is fixed by
  every `f.mapMatrix`).
- `outerMatrix g = J (g⁻¹)ᵀ J`, with `det_outerMatrix`.
- `outer : SL3 R →* SL3 R` is `g ↦ J (g⁻¹)ᵀ J` as a monoid homomorphism;
  `coe_outer` gives its matrix.
- `outer_left g : outer (left g) = right g` and `outer_right g :
  outer (right g) = left g`, with the composite forms `outer_comp_left`,
  `outer_comp_right`. The Lean proofs compute entrywise, writing `g⁻¹` as the
  adjugate (`Matrix.adjugate_fin_two`). The reason no sign twist appears on the
  `SL₂` side is the `-1` in the middle of `J`: for `g ∈ SL₂`,
  `(g⁻¹)ᵀ = w g w⁻¹` with `w = [0, -1; 1, 0]`, and conjugation by `J` turns the
  block at `0, 1` into the block at `1, 2`.
- `outer_outer` (`simp`) and `outer_comp_outer`: `outer` is an involution.
- `outerEquiv : SL3 R ≃* SL3 R` is `outer` as a multiplicative equivalence,
  with `outerEquiv_apply` and `outerEquiv_symm_apply` (both `simp`; the inverse
  is `outer` again).
- `map_outer`, `map_comp_outer`: `outer` commutes with
  `SpecialLinearGroup.map f`.

## Relation to the Library's SU₃ (section `Unitary`)

Here `c : SU3Root.RingInvolution R` is the Library's ring involution package,
with conjugation `c.bar`.

- `antidiagonal_eq_gram`: `J` is, by definition, the Gram matrix
  `SU3Root.gram R` of the Library's quasi-split `SU₃`.
- `unitaryTwist_eq_outer_map`: the Library's twist
  `SU3Root.unitaryTwist c g = J (conjugate transpose of g⁻¹) J` equals
  `outer (SpecialLinearGroup.map c.bar g)`.
- `map_bar_map_bar`: applying `c.bar` entrywise twice is the identity.
- `outer_eq_map_of_preservesForm`: if `g` preserves the Hermitian form
  (`SU3Root.PreservesForm c g`), then `outer g` is `g` with `c.bar` applied
  entrywise. Proof: such `g` is fixed by the twist
  (`SU3Root.unitaryTwist_fixed_iff`), so `outer (map c.bar g) = g`; apply
  `outer` and use `outer_outer`.
- `outer_eq_map_of_mem_twistFixedSubgroup`: the same conclusion for `g` in
  `SU3Root.twistFixedSubgroup c`, via `SU3Root.mem_twistFixedSubgroup`.

## Generation over a field (section `Generation`, `F` a field)

- `range_left_sup_range_right`: the ranges of `left` and `right` generate
  `SL3 F`. Proof: Mathlib's `diagonal_transvection_induction'` reduces to the
  diagonal matrices `diag2n` with two nontrivial entries `c, c⁻¹` (written via
  Mathlib's `diag2 c = diag(c, c⁻¹)` in `SL₂`) and to the
  elementary transvections. Each is written explicitly as a product of block
  elements: diagonal matrices at positions `{0, 1}` or `{1, 2}` are single block
  elements and those at `{0, 2}` are products of a left and a right one;
  transvections at `(0, 1)`, `(1, 0)`, `(1, 2)`, `(2, 1)` are block unipotents;
  the corner transvections are commutators,
  `1 + t E₀₂ = left(upper t) right(upper 1) left(upper (-t)) right(upper (-1))`
  and
  `1 + t E₂₀ = right(lower 1) left(lower t) right(lower (-1)) left(lower (-t))`.
  Each identity is checked entrywise.
- `hom_ext`: two group homomorphisms `SL3 F →* H` that agree after composing
  with `left` and with `right` are equal. Proof: their equalizer contains both
  ranges, hence everything by `range_left_sup_range_right`.
