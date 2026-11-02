# At most one nonzero proper subrepresentation, by support counting

Author: Worker 1032.

This internal helper of the proof of
`Langlands.Classification.JuxtaposedSegmentSocleReverseProductStructure`
(Zelevinsky 1980, Proposition 4.6, step (1), juxtaposed case) makes no literature
assertion. It is the abstract lattice argument behind the counting step of that
proof. There, `ρ` is the product `⟨Δ⟩ × ⟨Δ'⟩`, `A` is its normalized Jacquet
module along the uniform shape, and `Φ X` is the image of the Jacquet module of
`X` in `A`.

## Results

- `mem_jordanHolderSupport_of_equiv`: membership of `τ` in the composition-factor
  support `jordanHolderSupport B` depends only on the equivalence class of `τ`.
- `hasMultiplicityFreeCompositionSeries_of_le_one`: if `B` has a composition
  series `s` and every irreducible representation has Jordan–Hölder multiplicity
  at most one in `B`, then `B` has a multiplicity-free composition series
  (namely `s`).
- `eq_of_ne_bot_of_ne_top`: let `A` have a multiplicity-free composition series
  (`HasMultiplicityFreeCompositionSeries`). Let
  `Φ : Subrepresentation ρ → Subrepresentation A.ρ` be strictly monotone and
  preserve binary intersections. Let `Bad` be a predicate on representations
  whose members are pairwise equivalent. Assume `hcover`: every factor `τ` of
  `A` that is not `Bad` lies in the support of `Φ X` for every `X ≠ ⊥`. Then
  any two subrepresentations `X`, `Y` of `ρ` that are neither `⊥` nor `⊤` are
  equal.

## Proofs

`mem_jordanHolderSupport_of_equiv`: transport the multiplicity along the
equivalence with `equivJordanHolderMultiplicityTransport`.

`hasMultiplicityFreeCompositionSeries_of_le_one`: if two graded pieces
`i`, `j` of `s` are equivalent, then both indices are counted in the
multiplicity of the graded piece `i` in `s`, which is at most one, so `i = j`.

`eq_of_ne_bot_of_ne_top`: by `multiplicityFreeSubmoduleLattice`, the
subrepresentations of `A` are ordered by inclusion of their supports, and `⊤`
has support the support of `A`.

1. `Φ` reflects inclusion. If `Φ X = Φ Y` but `X ≰ Y`, then `X ⊓ Y < X`, so
   `Φ (X ⊓ Y) < Φ X`. But `Φ (X ⊓ Y) = Φ X ⊓ Φ Y = Φ X`, a contradiction.
2. For `Z` neither `⊥` nor `⊤`, the support of `Φ Z` is exactly the set of
   factors of `A` that are not `Bad`. Every such factor lies in it by `hcover`.
   Conversely, a factor of `Φ Z` is a factor of `A`. If it were `Bad`, then
   every `Bad` factor would lie in the support of `Φ Z` (by the first result and
   pairwise equivalence), and so would every other factor (by `hcover`). So
   `⊤ ≤ Φ Z`, while strict monotonicity gives `Φ Z < Φ ⊤`, a contradiction.
3. Hence `X` and `Y` have the same image support, so `Φ X = Φ Y`, and step 1
   gives `X ≤ Y` and `Y ≤ X`.
