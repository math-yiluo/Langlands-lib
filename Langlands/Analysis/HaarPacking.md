# Packing and fibre bounds for invariant measures on groups

Module `Langlands.Analysis.HaarPacking`, namespace `Langlands.HaarPacking`. It contains no
adelic or algebraic-group content; its adelic use is the proof of
`Langlands.Global.siegelRationalConjugateCounting`
(`Langlands/Global/AdelicSiegelRationalConjugateCountingProof.lean`).

## Provenance

Internal and derived. Both statements are the standard measure-theoretic steps of the
"packing" bound for lattice points (compare the counting argument recalled in the Markdown of
`Langlands/Global/AdelicSiegelRationalConjugateCountingStatement.md`, route "Packing" and
"Volume"). No external source is followed line by line.

## Declarations

### Packing

Let `G` be a group with a measurable space for which multiplication is measurable
(`MeasurableMul G`), and `μ` a left-invariant measure.

- `card_mul_measure_le`: let `Γ` be a subgroup and `W` a measurable set such that the only point
  of `Γ` in `W W⁻¹` is `1`. For every set `Z` and every finite `s ⊆ Γ ∩ Z`,
  `#s · μ(W) ≤ μ(Z W)`. *Proof.* The translates `γ W` (`γ ∈ s`) are pairwise disjoint: if
  `γ w = γ' w'` then `γ'⁻¹ γ = w' w⁻¹ ∈ Γ ∩ W W⁻¹`, so `γ = γ'`. They are measurable, have
  measure `μ(W)` by left invariance (`measure_smul`), and lie in `Z W`; apply
  `measure_biUnion_finset`.
- `finite_inter_and_ncard_mul_le` (**packing**): if moreover `μ(W) ≠ 0` and `μ(Z W) ≠ ∞`, then
  `Γ ∩ Z` is finite and `#(Γ ∩ Z) · μ(W) ≤ μ(Z W)` (`Set.ncard`). *Proof.* If `Γ ∩ Z` were
  infinite, choose `n` with `μ(Z W) < n μ(W)` (`ENNReal.exists_nat_mul_gt`) and a finite subset of
  cardinality `n` (`Set.Infinite.exists_subset_card_eq`); the previous bound gives a
  contradiction. Then apply the bound to `(Γ ∩ Z).toFinset`.

### Fibre bound

Let `G` be a second-countable topological group with its Borel σ-algebra, `μ` a left-invariant
s-finite measure on `G`, `H` a subgroup of `G` with a Borel σ-algebra and `ν` a left-invariant
s-finite measure on `H`.

- `measure_mul_mul_le` (**fibre bound**): for `X, V ⊆ H` and `B ⊆ G` with `X V` and `V⁻¹ B`
  measurable (`V⁻¹ B` means `(V ⊆ G)⁻¹ B`),

  `μ(X B) · ν(V) ≤ ν(X V) · μ(V⁻¹ B)`.

  *Proof.* Let `S = {(h, g) ∈ H × G : h ∈ X V, h⁻¹ g ∈ V⁻¹ B}`; it is measurable because
  `(h, g) ↦ h⁻¹ g` is measurable. By `Measure.prod_apply` and left invariance of `μ`, the slice
  of `S` over `h ∈ X V` is `h · V⁻¹ B`, so `(ν ⊗ μ)(S) = ν(X V) μ(V⁻¹ B)`. By
  `Measure.prod_apply_symm`, `(ν ⊗ μ)(S)` is the integral over `g` of `ν` of the slice over `g`.
  For `g = x b` (`x ∈ X`, `b ∈ B`) this slice contains `x V`, of measure `ν(V)`, so Markov's
  inequality (`mul_meas_ge_le_lintegral₀`) gives `ν(V) μ(X B) ≤ (ν ⊗ μ)(S)`. The set `X B` need
  not be measurable.

The module uses only the axioms `propext`, `Classical.choice` and `Quot.sound`.
