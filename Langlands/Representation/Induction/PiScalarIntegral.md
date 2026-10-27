# Compact scalar averages on finite products

Author: Worker 715.

This module shows that the compact-average invariance property passes from the
factors of a finite product of groups to the product. The property is the one
used as the scalar hypothesis in
`Langlands.Representation.Induction.CompactPairingDuality`. All results are
general measure-theoretic theorems. This is internal infrastructure with no
literature counterpart. It is the standard Fubini argument, which lets the
refined product-Levi case be derived from the GL block case.

## Setting

- `ι` is a finite index type. `G i` are topological groups with subgroups
  `P i` and `K i`.
- Each `K i` is a compact, second countable Borel space. `μ i` is a
  probability measure on it.
- `δj i : P i → ℝ≥0` are the factor weights. `δ` is a weight on
  `Subgroup.pi Set.univ P`. The hypothesis `hδ` ties them together: on an
  element supported in coordinate `j` with entry `q`, `δ` equals `δj j q`.
- The factor hypothesis `hblock` says the following for every `i`. Let
  `φ : G i → ℂ` be locally constant with `φ(q x) = δj i q * φ x`. Then
  `∫_{K i} φ(k g) dμ i = ∫_{K i} φ(k) dμ i` for every `g ∈ G i`.

## Results

- `measurePreserving_update_pi`. The map `(x, a) ↦ update x j a` from
  `(∏ X i) × X j` to `∏ X i` sends `(Measure.pi μ).prod (μ j)` to
  `Measure.pi μ`, for probability measures. The proof checks the two measures
  on boxes, using `Measure.pi_eq`.
- `piVal` and `continuous_piVal`, plus the algebraic lemmas `piVal_update`,
  `update_mul_mulSingle`, `mulSingle_mul_update` and `mulSingle_mem_pi`. These
  cover coordinatewise inclusion and the interaction of `Function.update` with
  `Pi.mulSingle`.
- `integrable_of_continuous_pi`. A continuous scalar function on the compact
  product is integrable for the product measure.
- `integral_piVal_mul_mulSingle`. This handles right translation by an element
  `Pi.mulSingle j h` supported in one coordinate. Lift both integrals along the
  measure-preserving update map. Apply Fubini (`integral_prod`). Then, for
  fixed outer coordinates `x`, apply `hblock j` to
  `ψ(y) = φ(update x j y)`. This `ψ` is locally constant and
  `δj j`-covariant: left multiplication of the `j`-th coordinate by `q` is left
  multiplication by `Pi.mulSingle j q`, and `hδ` identifies the weight.
- `integral_piVal_mul_of_support`. Invariance under every right translation by
  `g` with `g i = 1` off a finite set `s`, by induction on `s`. Write
  `g = Pi.mulSingle j (g j) * g'` and apply the one-coordinate step to
  `x ↦ φ(x g')`. This function is again locally constant and covariant.
- `pi_scalarIntegral`. The product property for `Measure.pi μ`, with
  `s = Finset.univ`. It gives both integrability and invariance.
- `piSubgroupHomeomorph`, `piSubgroupMeasure`,
  `piSubgroupMeasure_isOpenPosMeasure` and `piSubgroup_scalarIntegral`. These
  transport the product statement to the product subgroup
  `Subgroup.pi Set.univ K` of `∀ i, G i`. The tool is the canonical
  homeomorphism `(∀ i, K i) ≃ₜ Subgroup.pi Set.univ K`. `piSubgroupMeasure` is
  the pushforward of `Measure.pi μ`. It charges every nonempty open set when
  each `μ i` does. The transported scalar property is
  `piSubgroup_scalarIntegral`, whose conclusion has the same shape as the
  scalar hypothesis of `CompactPairingDuality`.

## Scope

No group-specific statement is made here. The product subgroup and measure are
used for refined product Levis in
`Langlands.Representation.Parabolic.NaturalInductionDualityFromScalar`.
