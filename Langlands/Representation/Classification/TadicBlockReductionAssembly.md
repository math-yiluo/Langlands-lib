# Assembly of Tadić's Lemma 4.8(ii) from its inputs

Author: Worker 5121. Module
`Langlands.Representation.Classification.TadicBlockReductionAssembly`, namespace
`Langlands.Classification.TadicBlockReductionAssembly`. It contains the induction proving
`TadicBlockReductionFromInputs`; the entry theorem is in
`TadicBlockReductionFromInputsProof`, whose Markdown describes the argument in full.

## Helper results

- `exists_le_associated_of_dvd_prod_map`: in a cancellative commutative monoid with zero, a
  divisor of `∏_{i ∈ J} f i` with all `f i` prime is associated to `∏_{i ∈ J'} f i` for some
  `J' ≤ J` (induction on `J`).
- `prod_map_finset_sum`, `UFamily.zero`, `UFamily.finset_sum`, `tadicSocleUnitarity_mono`
  (`(U^k)` implies `(U^j)` for `j ≤ k`), `uFamily_of_stFamily` (one-element families are
  unitary by `TadicBlockSteinberg`), `RParam.ext_refl`.
- Degrees: `degree_rect_le_sum`, `degree_rect_refl`, `rect_degree_pos`,
  `eq_of_le_of_degree_eq`, `degree_le_of_le`, `rect_le_sum`, and `base_degree_le`: in a
  reflection-invariant family of total degree at most `m + 1`, every rectangle has degree at
  most `m` unless one rectangle with `α = 0` has degree `m + 1` (a rectangle with `α ≠ 0`
  comes with its reflection of the same degree).
- `isZelevinskySocle_of_cls_eq_mul_prod`: an irreducible `X` with class
  `[π] ∏_J [⟨rect q⟩]`, `π` a socle of `a`, is a socle of `a + ∑_J rect q` (Zelevinsky 8.4
  as in `TadicBlockRing`).
- `BlockReductionAt m`: the assertion of `TadicBlockReduction` at a fixed `m`;
  `tadicBlockReduction_iff`.
- `eq_of_isZelevinskySocle`: two socle multisegments of one irreducible are equal.
- `exists_derivative_family`: under the induction hypothesis, `ν^(1/2) a⁻` is the sum of the
  rectangles of a unitary family (see the entry Markdown, step 2).
- `not_rect_eq`: under the hypothesis of Lemma 4.8(ii), `a` is not a rectangle `a(n,d)^ρ`
  with `ρ` unitary. `baseUnitary_of_le`: base unitarity from `(U^m)` when the base degree is
  at most `m`. `map_sum_rect_extSeg`.
- `step`: the induction step; `tadicBlockReductionFromInputs` (strong induction on `m`).
