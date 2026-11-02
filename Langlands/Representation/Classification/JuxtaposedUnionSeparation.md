# No nonzero subrepresentation of `⟨Δ₀⟩ × ⟨Δ₁⟩` is equivalent to the union socle

Author: Worker 1032.

This internal helper of the proof of
`Langlands.Classification.JuxtaposedSegmentSocleReverseProductStructure`
(Zelevinsky 1980, Proposition 4.6, step (1), juxtaposed case) makes no literature
assertion of its own. It separates the subrepresentations of `π = ⟨Δ₀⟩ × ⟨Δ₁⟩` from
the socle `ω` of the union segment by their Jacquet modules.

Notation: `ρ` is a cuspidal datum of rank `r` with supercuspidal representative
`A`. `Δ₀` begins at `ν^l ρ` with length `q`, and `Δ₁` begins at `ρ` with length `l`.
`J` is the normalized Jacquet functor along the uniform shape `(r, …, r)` with
`q + l` blocks. For a shuffle set `S`, `τ_S` is the tensor
`⊗ᵢ ν^(e_S(i)) A` with the exponents `e_S = shuffleExponent S l 0`. `S_id` is
`idShuffle q l` and `S₀` is `initShuffle q l`.

## Results

- `shuffleExponent_idShuffle`: the identity shuffle carries the increasing exponents,
  `e_{S_id}(i) = i` for every `i < q + l`.
- `shuffleFactors_idShuffle`: so the factor family of `τ_{S_id}` is the family
  `T.segmentFactors A (q + l)` of the increasing segment induction, `ν^i A` at
  position `i`.
- `nonempty_jacquet_single_equiv`: assume `SegmentSubrepresentationFullJacquet`
  (Zelevinsky 1980, 3.1, the Library statement in
  `Classification.SegmentFullJacquetStatement`, as the explicit hypothesis
  `hfull`). Let `e` be a datum on `GL_(m r)` with one segment, whose beginning is
  `ρ` and whose length is `m`, and whose block is a segment socle. Then
  `J(e.induced)` along the uniform shape with `m` blocks is equivalent to
  `A ⊗ νA ⊗ … ⊗ ν^(m-1) A`.
- `not_nonempty_equiv_of_ne_bot`: assume `q, l > 0` and the two-block swap hypothesis
  `hswap` (the shape of `JuxtaposedSwapFromLibrary.segmentFactor_swap_of_isIrreducible'`).
  Let `σ` be any representation of `GL_((q+l) r)` with `J(σ)` equivalent to
  `τ_{S_id}`. Then no nonzero subrepresentation `X` of `π` is equivalent to `σ`.

## Proofs

`shuffleExponent_idShuffle`: `idShuffle q l` is the set of positions `i ≥ l`, and
the set of `j < i` has `i` elements (`Fin.card_Iio`). If `i ≥ l`, the positions
`j < i` split into the `l` positions below `l`, which are outside `S_id`, and the
positions of `S_id` below `i`. So `S_id` has `i - l` positions below `i`, and the
exponent is `l + (i - l) = i`. If `i < l`, every position below `i` lies outside
`S_id`, and the exponent is `0 + i`.

`nonempty_jacquet_single_equiv`: destructure `e` and substitute `ρ` by the beginning
of its segment and `m` by its length. Then the total rank is definitionally the
degree of the segment. `singleBlockNormalizedProductEquiv` identifies the
one-block product `e.induced` with the block composed with
`reindex (finCongr _)`. That reindexing is the identity, checked entrywise. The block
is a segment socle (`HasSegmentSocles`). The first clause of `IsIrreducibleSocle`
together with its embedding gives `IsSegmentSubrepresentation`, so `hfull` applies.
Transport along the identification by `normalizedJacquetEquiv` and compose with the
equivalence from `hfull`.

`not_nonempty_equiv_of_ne_bot`: since `q, l > 0`, `S₀ ≠ S_id`
(`initShuffle_ne_idShuffle`). So `exists_ne_zero_jacquet_hom_shuffle` gives a
nonzero intertwining map `g : J(X) → τ_{S₀}`. Suppose `E : X ≃ σ`. Then
`f = g ∘ J(E)⁻¹ ∘ Eσ⁻¹ : τ_{S_id} → τ_{S₀}` is nonzero, because precomposing with
equivalences loses nothing. Both shuffle tensors are irreducible (the first clause
of `glCuspidalTensor`). By Schur's lemma, Mathlib's
`Representation.IsIrreducible.bijective_or_eq_zero`, `f` is bijective, so it is an
equivalence. Then `eq_of_shuffleTensor_equiv` gives `S₀ = S_id`, a contradiction.
