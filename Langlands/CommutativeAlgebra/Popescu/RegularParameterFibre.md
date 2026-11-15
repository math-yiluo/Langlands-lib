# Flatness from the closed fibre along an ideal

`RegularParameter.flat_of_fibre (hN3 : RegularSequenceFlatStatement)`. Let `B → S` be a local map
of Noetherian local rings and `J ⊂ B` a proper ideal such that `J ⊗_B S → S` is injective. Suppose
`𝔪_B = J + (z₁, …, z_r)`, the `z̄_j` form a weakly regular sequence on `B/J`, and their images form
a weakly regular sequence on `S/JS`. Then `S` is flat over `B`.

The proof uses only the standard axioms.

- `B/J` and `S/JS` are local Noetherian, and the induced map is local.
- `B/J → S/JS` is flat by `hN3` (Stacks 07DY): the `z̄_j` generate `𝔪_{B/J}`, are weakly regular
  on `B/J`, and their images are weakly regular on `S/JS`.
- `(B/J) ⊗_B S ≅ S/JS` (`quotIdealMapEquivQuotTensor`).
- The Library's `Langlands.Algebra.idealLocalFlatnessCriterion` along `J` concludes.
