# The completion of a ring at a maximal ideal and maps to complete local rings

This internal module collects facts about `P = Localization.AtPrime 𝔪` and its
completion `P̂ = AdicCompletion (maximalIdeal P) P`, for a maximal ideal `𝔪` of a
commutative ring `S : Type u`. It then extends a map `S → A` into a complete local
ring `A` to `P̂`. These are the comparisons between `S`, `P` and `P̂` that Stacks
Lemma 98.10.1 (Tag 07XB) uses implicitly when it identifies `P̂` with the completion
of `Λ[x₁, …, x_s]` and maps it onto `R` (equation 10.1.1, `artin.pdf` printed
p. 15).

## Localization at a maximal ideal

- `exists_mul_sub_one_mem_pow`: if `w ∉ 𝔪`, then for every `n` some `w'` has
  `w * w' - 1 ∈ 𝔪 ^ n`. If `y * w + i = 1` with `i ∈ 𝔪`, take
  `w' = y * ∑_{k<n} i ^ k`. Then `w * w' - 1 = -(i ^ n)`.
- `mem_pow_of_mul_mem_pow`: if `w ∉ 𝔪` and `w * s ∈ 𝔪 ^ n`, then `s ∈ 𝔪 ^ n`.
- `exists_sub_algebraMap_mem_pow`: every `p : P` is congruent modulo
  `(maximalIdeal P) ^ n` to the image of some `s : S`. For `p = a / w`, use
  `s = a * w'`.
- `mem_pow_of_algebraMap_mem_pow`: if the image of `s` lies in
  `(maximalIdeal P) ^ n`, then `s ∈ 𝔪 ^ n`. The proof uses the description of
  extended ideals in a localization and the previous saturation lemma.

## The completion of a Noetherian local ring

For a Noetherian local ring `R`, `ker_evalₐ` proves that the kernel of
`AdicCompletion.evalₐ (maximalIdeal R) n` is the `n`-th power of the maximal ideal of
the completion. `mem_pow_iff_evalₐ_eq_zero` is the elementwise form. The proof
uses Mathlib's `AdicCompletion.pow_smul_top_eq_ker_eval` and
`AdicCompletion.maximalIdeal_eq_map`.

## The completion of `S` at `𝔪`

Assume `S` is Noetherian. Then `P` is Noetherian
(`isNoetherianRing_localization`). Write `σ = algebraMap S P̂`.

- `algebraMap_completion_eq`: `σ` is the composite `S → P → P̂`.
- `exists_sub_algebraMap_mem_pow_completion`: every `x : P̂` is congruent modulo
  `(maximalIdeal P̂) ^ n` to some `σ s`.
- `mem_pow_of_algebraMap_completion_mem_pow`: if `σ s ∈ (maximalIdeal P̂) ^ n`, then
  `s ∈ 𝔪 ^ n`.
- `maximalIdeal_completion_eq_map`: `maximalIdeal P̂ = 𝔪.map σ`.
- `algebraMap_mem_pow`: `σ` maps `𝔪 ^ n` into `(maximalIdeal P̂) ^ n`.

## Extension to a complete local ring

Let `A : Type v` be a local ring that is complete for its maximal ideal `m_A`. Let
`σA : S →+* A` satisfy `σA s ∈ m_A ↔ s ∈ 𝔪` for all `s`.

- `localizationLift` is the induced map `P →+* A`; elements outside `𝔪` become
  units of the local ring `A`. `localizationLift_pow_le` shows that it maps
  `(maximalIdeal P) ^ n` into `m_A ^ n`.
- `stageMap n : P̂ →+* A / m_A ^ n` evaluates at stage `n` and then applies
  `localizationLift` modulo powers. `stageMap_compatible` shows compatibility with
  the transition maps.
- `completionLift : P̂ →+* A` is `IsAdicComplete.liftRingHom` of this compatible
  family. `mk_completionLift` gives its reductions, and
  `completionLift_algebraMap` proves `completionLift (σ s) = σA s`. The last proof
  compares reductions modulo every `m_A ^ n` using the Hausdorff property.
- `completionLift_mem_pow`: `(maximalIdeal P̂) ^ n` is mapped into `m_A ^ n`.

Assume also that every `a : A` has some `s` with `a - σA s ∈ m_A ^ 2`.

- `completionLift_surjective`: `completionLift` is surjective. By the previous module,
  choose `s₀, s₁, …` with `a - σA s_k ∈ m_A ^ (k + 1)` and
  `s_{k+1} - s_k ∈ 𝔪 ^ (k + 1)`. The recursive choice increments `s_k` by an
  element of `𝔪 ^ (k + 1)`. The images `σ s_k` form a Cauchy sequence in `P̂`.
  Precompleteness gives a limit `L`. Then `completionLift L ≡ a` modulo every
  `m_A ^ n`, and the Hausdorff property of `A` gives equality.
- `completionLift_comap_pow`: the preimage of `m_A ^ n` is
  `ker completionLift ⊔ (maximalIdeal P̂) ^ n`. The surjective map carries the
  maximal ideal onto `m_A`, and preimages of images are taken with the kernel.
