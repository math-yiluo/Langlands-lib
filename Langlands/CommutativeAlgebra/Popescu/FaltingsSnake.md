# A dimension count from the snake lemma

Linear algebra used in Faltings' proof of Stacks, More on Algebra, Proposition 15.36.1 (07E5),
(2) ⇒ (4). The declaration lives in `Langlands.CommutativeAlgebra.Popescu.Faltings`. It is an
internal helper; the statement is a standard consequence of the snake lemma.

## `rank_coker_le_rank_ker`

Setting: `K` is a field. There are two short exact sequences of `K`-vector spaces,
`0 → X₁ → Y₁ → Z₁ → 0` (maps `i₁`, `p₁`) and `0 → X₂ → Y₂ → Z₂ → 0` (maps `i₂`, `p₂`). There are
vertical maps `α : X₁ → X₂`, `β : Y₁ → Y₂`, `γ : Z₁ → Z₂` with `β ∘ i₁ = i₂ ∘ α` and
`γ ∘ p₁ = p₂ ∘ β`. All six spaces lie in one universe `u`.

Hypotheses:
- `X₁` and `ker γ` are finite-dimensional;
- `dim X₂ ≤ dim X₁`;
- `dim coker γ ≤ dim ker γ`.

Conclusion: `dim coker β ≤ dim ker β`, and `ker β` is finite-dimensional. Dimensions are
`Module.rank` (cardinals), and `coker β` is `Y₂ ⧸ range β`.

The informal reason is that the Euler characteristic `dim ker − dim coker` is additive, and
`χ(α) ≥ 0` here because `α`'s kernel is at least as large as its cokernel. The Lean proof avoids
the snake lemma itself and counts dimensions directly:

1. Put `V = β⁻¹(i₂(X₂)) ⊆ Y₁`. The map `p₁` sends `V` onto `ker γ` (exactness of the second row
   and surjectivity of `p₁`), with kernel `i₁(X₁)`. So `dim V = dim X₁ + dim ker γ`.
2. Put `W = i₂(X₂) ∩ β(Y₁)`. The map `β` sends `V` onto `W` with kernel `ker β`. So
   `dim V = dim W + dim ker β`.
3. `p₂` induces a surjection `coker β → coker γ`. Its kernel is the image `R` of `X₂` in
   `coker β`. So `dim coker β = dim coker γ + dim R`.
4. The map `X₂ → coker β` has image `R` and kernel `W`. So `dim X₂ = dim R + dim W`.
5. Steps 1 and 2 show that `V`, `W` and `ker β` are finite-dimensional, and step 4 shows the same
   for `R`. Every dimension involved is therefore a natural number, and `omega` concludes from the
   four equations and the two inequalities.
