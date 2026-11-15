# Adding a segment with the greatest ending to a Zelevinsky label

Module `Langlands.Representation.Classification.MoeglinWaldspurgerZelevinskySocle`. Written by
Worker 5735 for Task 5735.

Helpers: `exists_segmentSocle_of_mem` (a segment of a datum of socles has a socle),
`exists_segmentSocle_of_eq`, `segment_eq_mk`; `labelClass_cons` (an irreducible
subrepresentation of `Z × d₀.induced`, with `d₀` a precedence-ordered datum of socles for
`realize b` and `Z` a socle of the realization of an interval `J` ending last, is a label of
`J ::ₘ b`: prepend `J` with `SegmentProductOrderedAssembly.cons`); `LDrel_of_embeds` (the
comparison wrapper in the language of `Embeds` and labels).

`zsocle_LDrel` (field `zsocle` of `DerivativeFacts` for `LDrel`), assuming
`LeftCuspidalDerivativeLemma`: let `I = [c, e]` end at least where every occurrence of `ν` and
`ν'` ends, let `cls₁`, `cls` be the labels of `ν`, `I + ν`, and `S₁`, `S` those of `ν'`,
`dropFirst I + ν'`. If `LDrel c cls₁ K S₁`, then `LDrel c cls (K + 1) S`.

Proof. From `LDrel c cls₁ K S₁` take `π₁ ↪ A^K × D₁`. Let `Z` be a socle of the realization of
`I`. An irreducible subrepresentation `π` of `Z × π₁` is a label of `I + ν` (`labelClass_cons`),
so has class `cls`. The point `[c, c]` and `I` are unlinked, so `Z × A ≅ A × Z`
(`castIso_swap_of_unlinked`) and `Z × (A^K × D₁) ≅ A^K × (Z × D₁)` (`castIso_commute`).
If `c < e`, the socle cut embeds `Z` into `A × Z₀` with `Z₀` a socle of `[c+1, e]`, and
associativity gives `π ↪ A^(K+1) × (Z₀ × D₁)`; `Y = Z₀ × D₁` has finite length, is left reduced
(segment and product clauses) and all its irreducible subrepresentations are labels of
`[c+1, e] + ν'` (`labelClass_cons`); `LDrel_of_embeds` concludes. If `c = e`, `Z` is isomorphic
to the point block (published `IsSegmentSocle.nonempty_equiv`), hence `π ↪ A^(K+1) × D₁`, and
`LDrel_of_embeds` with `Y = D₁` concludes.
