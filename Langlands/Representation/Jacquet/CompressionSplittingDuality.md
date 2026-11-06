# Stable-image duality and Jacquet's lemma from the Fitting splitting

`Langlands.Representation.Jacquet.CompressionSplittingDuality`, namespace
`Langlands.Jacquet`.

## Purpose and provenance

The published Library proves two facts about the compressed action
`C = e_K ∘ π(g)` on the `K`-fixed vectors `V^K` of a smooth complex
representation, both under the hypothesis that `V^K` is finite dimensional:

- `compactCompression_stableEvaluationDuality`
  (`CompactCompressionStableDualityProof`): the evaluation pairing identifies the
  stable image of compression by `g⁻¹` on the smooth contragredient with the full
  dual of the stable image of compression by `g` on `V`;
- `stableImageJacquetMap_bijective_of_iwahoriContraction`
  (`IwahoriContractionAdmissibility`): Jacquet's lemma for an element with the
  Iwahori contraction properties.

Both proofs use finite dimensionality only to obtain the Fitting splitting
`V^K = (⋃ₙ ker Cⁿ) ⊕ (⋂ₙ im Cⁿ)` (the published proposition
`CompactCompressionSplits`). This module proves both conclusions from that splitting
alone, for every smooth representation. Renard 2026, VI.9.1 (PDF pp.201-204) and
VI.9.6 (PDF pp.207-210) need this form: there, the splitting comes from uniform
stabilization (Proposition of VI.9.1) and not from admissibility. Renard's Appendix
C.II (PDF pp.282-285) characterizes stable operators by `ker t = ker t²` and
`Im t = Im t²`; this is equivalent to the constant-powers form used by
`CompactCompressionEventuallyStable`.

These are internal helper results. They add no new definitions or statements.

## Results

- `isCompl_iSup_ker_pow_iInf_range_pow_of_eventually`: for an endomorphism `f` of
  a module over any ring, suppose that from some `r` on every power range equals
  `⋂ₙ im fⁿ` and every power kernel equals `⋃ₙ ker fⁿ`. Then these two
  submodules are complementary. Proof: an element `fʳ y` of `ker fʳ` has
  `y ∈ ker f²ʳ = ker fʳ`. For any `x`, write `fʳ x = f²ʳ y`; then
  `x = (x - fʳ y) + fʳ y`.
- `compactCompressionSplits_of_eventuallyStable`: this applied to the compressed
  action.
- `powerKernelSup_le_comap_compressedAction`: the kernel supremum is invariant
  under the compressed action.
- `stableImageAction_bijective_of_splits`: given the splitting, the restriction of
  compression to the stable image is bijective. Injectivity: its kernel lies in
  `ker C`, which is inside the kernel supremum, and that meets the stable image
  only in `0`. Surjectivity: write a stable vector as `s = C x` and split
  `x = t + u`. Then `C t = s - C u` lies in the stable image and in the kernel
  supremum, so `C t = 0` and `s = C u`.
- `compactCompression_stableEvaluationDuality_of_splits`: the published
  `CompactCompressionStableEvaluationDuality ρ hρ K hK g`, assuming only the
  splitting for `g` on `V^K`. The proof uses private linear algebra for a
  bijection `p : A → Dual B` with `p (C a) b = p a (D b)`. The adjoint pair is
  restriction of fixed smooth functionals (`smoothDualFixedRestriction_bijective`)
  with compression by `g⁻¹` and by `g` (`compressedAction_adjoint`). The key
  step: `a ∈ ⋂ₙ im Cⁿ` iff `p a` vanishes on `⋃ₙ ker Dⁿ`. The converse direction
  uses `range (Dⁿ)ᵀ = (ker Dⁿ)^⊥` over the field `ℂ`
  (`LinearMap.range_dualMap_eq_dualAnnihilator_ker`), which needs no finiteness.
  Then:
  - Injectivity: `p a` vanishes on the kernel supremum and on the stable image,
    and these span `B`.
  - Surjectivity: a functional `φ` on the stable image of `D` extends to `B` by
    composing with the projection along the kernel supremum, and its preimage
    under `p` lies in the stable image of `C`.
- `stableImageJacquetMap_bijective_of_splits` and
  `fixedJacquetMap_surjective_of_splits`: Jacquet's lemma for
  `IsIwahoriContraction K N M Nbar g`, assuming the splitting instead of finite
  dimensionality. The proof copies the published proof of
  `stableImageJacquetMap_bijective_of_iwahoriContraction`, with two changes: the
  splitting is the hypothesis, and bijectivity of the stable action comes from
  `stableImageAction_bijective_of_splits`. It uses only public Library lemmas
  (`powerKernelSup_eq_ker_of_iwahoriContraction`,
  `mk_compressedAction_of_iwahoriContraction`,
  `IsIwahoriContraction.exists_pow_lower_fixed`, `IsIwahoriContraction.levi_pow`,
  `map_averageMap_of_forall_eq`).

## Use

Together with the Proposition of VI.9.1, which supplies the splitting for every
smooth representation, the last result gives the Theorem of VI.9.1 (the generalized
Jacquet lemma). The duality result lets the stable pairing of Casselman's theorem be
built for every smooth representation, not only for admissible ones.
