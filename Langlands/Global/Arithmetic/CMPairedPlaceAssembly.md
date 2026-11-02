# Two conjugate place pairs from compatible embeddings

Module `Langlands.Global.Arithmetic.CMPairedPlaceAssembly`, namespace
`Langlands.Global.CMRealization`. These are supporting theorems for the proof of
`Langlands.Global.HarrisPairedPlaceRealizationStatement`. The module adds no definitions and no
assumptions.

## Provenance

Harris (1998), Section 4, printed pages 200–201 (registered source
`harris-1998-local-langlands`), uses two places `v` and `v_s` of the CM field `E`, their complex
conjugates `c(v)` and `c(v_s)`, and completion identifications at both places. The present
theorem derives these four places and the two place data from one set of compatible embeddings
and an automorphism `t` of the global tower. This internal argument is not in the source. It uses
the companion module `HarrisPlaceFromEmbedding` (`exists_harrisPlaceDatum`, `ne_of_place_eq`,
`range_comp_ringEquiv`, `mem_finitePlaceEquiv_iff`, `natCast_mem_finitePlaceEquiv`,
`hasUniquePlaceAbove_finitePlaceEquiv`) and the published Library module `HarrisSetup`
(`PlaceDatum`, `conjPlace`, `HasUniquePlaceAbove`).

## Distinctness of places

- `ne_of_neg_place`: let `j` and `j'` be embeddings `E → F₀` whose images generate `F₀` over
  `ℚ_[p]`. Let `v` and `v'` be the primes they cut out by spectral norm less than one. Suppose a
  nonzero `x ∈ E` has `j x ∈ ℚ_[p]` and `j' x = -j x`. Then `v ≠ v'`. If `v = v'`, then
  `ne_of_place_eq` gives `j' x = j x`. So `2 j x = 0`, which is impossible in characteristic
  zero.
- `pairwise_ne_four`: six inequalities give `List.Pairwise (· ≠ ·)` for a four-element list.

## The assembly (`pairedPlaces_of_embeddings`)

The data are:

- a tower of number fields `E ⊆ E' ⊆ L`, with `E` a CM field and `L / E` Galois;
- embeddings `jE : E → F`, `jE' : E' → F'` and `jL : L → F̃`, where `jE` generates `F` over
  `ℚ_[p]`, `jE'` and `jL` generate `F'` and `F̃` over `F`, and the embeddings are compatible with
  the two towers;
- a group isomorphism `θ : Gal(L/E) ≃* Gal(F̃/F)` with `θ σ (jL x) = jL (σ x)`;
- ring automorphisms `t`, `t'`, `tL` of `E`, `E'`, `L` that are compatible with the inclusions,
  with `tL` commuting with `Gal(L/E)`;
- a ring automorphism `cL` of `L` extending the complex conjugation `c` of `E`;
- nonzero `x_a, x_d ∈ E` with `jE x_a, jE x_d ∈ ℚ_[p]`, `c x_a = -x_a`, `c x_d = x_d`,
  `t x_a = x_a` and `t x_d = -x_d`.

The conclusion is every clause of the target after the degree equalities: two place data `P`
and `Ps` with completion maps `φ` and `φs`, the four distinct places, `p` in each of them and a
unique place of `L` above each, compatibility, continuity both ways, `θ`-equivariance at both
place data, and the two commuting completion diagrams for each.

The proof:

1. `P` and `φ` come from `exists_harrisPlaceDatum` applied to `(jE, jE', jL)` and `θ`. That
   theorem also says that `P.v` is cut out by `jE`.
2. `Ps` and `φs` come from the same theorem applied to the twisted embeddings `jE ∘ t`,
   `jE' ∘ t'` and `jL ∘ tL`, with the same `θ`. Generation is preserved by composing with a
   ring automorphism (`range_comp_ringEquiv`). Compatibility of the twisted embeddings follows
   from that of `t, t', tL` and of the original embeddings. The equivariance
   `θ σ (jL (tL x)) = jL (tL (σ x))` uses `hθ` and the commutation of `tL` with `σ`.
3. `conjPlace E v` is by definition `finitePlaceEquiv c v`. By `mem_finitePlaceEquiv_iff`, the
   conjugate places `c(P.v)` and `c(Ps.v)` are cut out by `jE ∘ c` and by `jE ∘ t ∘ c`.
4. The six inequalities come from `ne_of_neg_place`, using `x_a` for the pairs that differ by
   `c` alone and `x_d` for the others. For example, `jE (t x_d) = -jE x_d` separates `P.v` from
   `Ps.v`, and `jE (c x_a) = -jE x_a` separates `P.v` from `c(P.v)`.
5. Membership of `p` and uniqueness above transfer from `P.v` and `Ps.v` to their conjugates
   (`natCast_mem_finitePlaceEquiv`, `hasUniquePlaceAbove_finitePlaceEquiv` with the extension
   `cL` of `c`). The other clauses are read off from the two applications of
   `exists_harrisPlaceDatum`.
