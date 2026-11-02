# The product of two segment socles inside one cuspidal induction

Author: Worker 1032.

This internal helper of the proof of
`Langlands.Classification.JuxtaposedSegmentSocleReverseProductStructure`
(Zelevinsky 1980, Proposition 4.6, step (1), juxtaposed case) makes no literature
assertion. It records the standard embedding used in that proof: a product of
segment socles lies in the product of the segment inductions, which regroups into
one induction from the uniform shape (Bernstein–Zelevinsky 1977, transitivity of
induction; in the Library, `Langlands.Parabolic.orderedProductRegrouping`). It
assumes no irreducibility, linkage or commutation result.

Throughout, `ρ` is a cuspidal datum of rank `r` with supercuspidal representative
`A`, `ν^s` is twisting by `|det|^s` (`T.segmentFactor A s`), and
`shuffleExponent` and `shuffleFactors` are those of
`Classification.TwoSegmentSocleShuffleJacquetStatement`. The initial shuffle
`initShuffle q l = {0, …, q-1}` of `Fin (q + l)` comes from
`Classification.JuxtaposedShuffleCombinatorics`.

## Results

The coordinate and twist helpers `index_index_eq_of_lt_iff`,
`val_finSigmaFinEquiv_fin_two`, `twistCongrIso`, `segmentFactorTwistIso`,
`nonempty_cast_iso` and `regroup_nonempty_iso` are imported from
`Classification.JuxtaposedRefinementTools` (same namespace
`Langlands.Classification.JuxtaposedShuffle`), where they were extracted from an
earlier version of this module. This module adds:

- `shuffleExponent_initShuffle_of_lt` and `shuffleExponent_initShuffle_of_le`:
  for the initial shuffle, the exponent at `k < q` is `a₀ + k` and the exponent at
  `k ≥ q` is `a₁ + (k - q)`. Both count the elements of `{0, …, q-1}` (or of its
  complement) below `k` with `Fin.card_filter_val_lt`.
- `exists_injective_initShuffle`: let `d` be a datum on `GL_((q+l) r)` with two
  segment socles, where `d.segments 0` begins at `ρ.twist l` and has length `q`,
  and `d.segments 1` begins at `ρ.twist 0` and has length `l`. Then
  `d.induced = ⟨Δ₀⟩ × ⟨Δ₁⟩` has an injective intertwining map into the product,
  along `uniform (q + l) r`, of `shuffleFactors A (q + l) (initShuffle q l) l 0`,
  that is of `ν^l A, …, ν^(l+q-1) A, A, ν A, …, ν^(l-1) A`.

## Proof of `exists_injective_initShuffle`

Destructure `d`, substitute its length `2`, and let `A'_j` be the representatives
and `J_j : ⟨Δ_j⟩ ↪ i(ν^0 A'_j, …, ν^(m_j - 1) A'_j)` the socle embeddings given by
`HasSegmentSocles`. Normalized induction along the segment shape preserves
injections (`normalizedProduct_embedding_of_factor_embeddings`), giving
`d.induced ↪ i_D(segment inductions)`, where `D` is the segment shape of `d`.

Regroup with `B = uniform (q + l) r`, the refinement `S j = uniform (len Δ_j) r_j`
of `D`, and the lexicographic numbering
`e = finSigmaFinEquiv.trans (finCongr _) : Σ j, Fin (len Δ_j) ≃ Fin (q + l)`. The
block sizes agree because each segment has the rank of `ρ`, and `hc` is
`index_index_eq_of_lt_iff` with `BlockShape.finSigmaFinEquiv_lt_iff`. The
exponent of the initial shuffle at `e ⟨j, k⟩` is `k + a_j`, with `a_0 = l` and
`a_1 = 0` (`val_finSigmaFinEquiv_fin_two` and the two `shuffleExponent_initShuffle`
lemmas). By `nonempty_cast_iso`, entry `k` of fiber `j` is isomorphic to
`ν^k A'_j`, the `k`-th factor of the segment induction of `Δ_j`; the functor of
`S j` turns these into an isomorphism of the inner product with that segment
induction. `regroup_nonempty_iso` then gives
`i_B(shuffleFactors) ≅ i_D(segment inductions)`, and the composite of the
embedding with the inverse of this isomorphism is the required injective map.
