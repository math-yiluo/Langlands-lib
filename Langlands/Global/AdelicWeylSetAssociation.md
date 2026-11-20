# Association of parabolics and the counting identity for `Ω(P, P')`

Module `Langlands.Global.AdelicWeylSetAssociation` proves how the Weyl sets
`Ω(P, P') = weylParameterSet p l p' l' π'` of
`Langlands.Global.AdelicInducedInnerProduct` compose. As a consequence it
proves the counting identity `∑ i, (n_P i)⁻¹ |Ω(P i, P i')| = 1` behind the
weights `n_P` of the wave packet isometry. Every result here is a proved
theorem, and there are no new definitions. All theorems are in the namespace
`Langlands.Global.AdelicGroupPoints`.

## Sources and provenance

The module is internal infrastructure for the proof of
`Langlands.Global.WavePacketIsometryStatement`. Its mathematical content is
the elementary combinatorics of the weights `n_P`:

- J. Arthur, *An introduction to the trace formula* (2005), registered as
  `arthur-ellwood-kottwitz-2005-harmonic-analysis-shimura`, Theorem 7.2 (b),
  printed p.35 (PDF page 47). Here
  `n_P = ∑_{P' ∈ 𝒫} |W(𝔞_P, 𝔞_{P'})|` for an associated class `𝒫`.
- E. Lapid (2011), registered as
  `lapid-2011-asymptotic-inner-product-truncated-eisenstein`, §3, p.314,
  Theorem 2 (PDF page 323).

Neither source proves the identity `∑_P n_P⁻¹ |Ω(P, P')| = 1`. They use it
implicitly when they expand `‖∑_P n_P⁻¹ Θ_P‖²`. The proof here relies only
on the group structure of Weyl conjugations: composition and inverses.

## Results

### A counting lemma

`sum_inv_rowSum_mul_eq_one`. Let `N : I → I → ℕ` on a finite type `I` satisfy:

- `N a b ≠ 0` implies `N b a ≠ 0`;
- if `N a b ≠ 0`, then `N a x = N b x` and `N x a = N x b` for every `x`.

Then `∑ a, (n a)⁻¹ N a b = 1` in `ℝ` for every `b` with
`n b = ∑ x, N b x ≠ 0`.

Proof. Let `C` be the set of `a` with `N a b ≠ 0`. For `a ∈ C` the rows of
`a` and `b` agree, so `n a = n b` and `N a b = N b b`. Hence the left side is
`|C| · (n b)⁻¹ N b b`. On the other hand, `N b x ≠ 0` holds exactly when
`x ∈ C`, by the symmetry. For such `x` the column identity gives
`N b x = N b b`, so `n b = |C| · N b b`. Since `n b ≠ 0`, both `|C|` and
`N b b` are nonzero, and the quotient is `1`.

### Composition and inverses of Weyl conjugations

- `weylParameter_comp`. Suppose `l' ≫ π' = 𝟙`. Then
  `weylParameter l' c π''` composed after `weylParameter l c₀ π'` equals
  `weylParameter l (c ≫ c₀) π''`. On a pure tensor `s ⊗ χ` both sides give
  `s ⊗ (χ ∘ l ∘ c₀ ∘ π' ∘ l' ∘ c ∘ π'')`. The proof uses
  `characterRestrict_comp` and then cancels `π' ∘ l' = 𝟙`.
- `innerIso_mul_inv` and `innerIso_inv_point_inv`:
  `(inn (w w₀))⁻¹ = (inn w)⁻¹ ≫ (inn w₀)⁻¹` and `(inn w⁻¹)⁻¹ = inn w` for the
  inner automorphisms `G.innerIso`.
- `IsWeylConjugation.comp`. If `w₀ M w₀⁻¹ = M'` via `c₀` and
  `w M' w⁻¹ = M''` via `c`, then `(w w₀) M (w w₀)⁻¹ = M''` via `c ≫ c₀`.
- `IsWeylConjugation.exists_symm`. If `w M w⁻¹ = M'` via `c₀`, then
  `w⁻¹ M' w = M` via `inv c₀`, a two-sided inverse of `c₀`.

### The Weyl sets

- `comp_mem_weylParameterSet_right` and `comp_mem_weylParameterSet_left`.
  Composing with the map of an element of `Ω(Pa, Pb)` sends `Ω(Pb, Px)` into
  `Ω(Pa, Px)` (precomposition) and `Ω(Px, Pa)` into `Ω(Px, Pb)`
  (postcomposition).
- `card_weylParameterSet_le_right` and `card_weylParameterSet_le_left`.
  Suppose `Pa` and `Pb` are associate through `IsWeylConjugation pa la pb lb w₀ c₀`,
  both retractions satisfy `l ≫ π = 𝟙`, and the target set is finite. Then
  `|Ω(Pb, Px)| ≤ |Ω(Pa, Px)|` and `|Ω(Px, Pa)| ≤ |Ω(Px, Pb)|`. The
  composition map is injective because composing with the map of the inverse
  conjugation `inv c₀` undoes it. Applying the same lemma to the inverse
  conjugation gives the reverse inequalities.

### Families

Fix a family `P i` with retractions `π i` (`l i ≫ π i = 𝟙`) and an
enumeration `T i i'` of `Ω(P i, P i')` by pairs `(w i i' t, cw i i' t)` with
`IsWeylConjugation`. The map `t ↦ weylParameter (l i) (cw i i' t) (π i')` is
assumed injective and onto `weylParameterSet`. These are exactly the
hypotheses `hW`, `hinj` and `hsurj` of `WavePacketIsometryStatement`.

- `card_eq_natCard_weylParameterSet`: `|T i i'| = |Ω(P i, P i')|`.
- `sum_inv_card_mul_card_eq_one`. Suppose `n_P i' = ∑ i'', |T i' i''|` is
  nonzero. Then `∑ i, (n_P i)⁻¹ |T i i'| = 1` in `ℝ`, with
  `n_P i = ∑ i'', |T i i''|`. This is the counting lemma for
  `N a b = |T a b|`. All three hypotheses come from the results above:
  symmetry from `exists_symm` and `hsurj`, and equality of rows and columns
  of associate members from the two cardinality inequalities in both
  directions. The finiteness of the Weyl sets comes from `hsurj`.

No reflexivity is needed. If `n_P i' = 0` the identity fails, since the sum
is then `0`. The isometry proof avoids this case: there the identity is
multiplied by `(n_P i')⁻¹ = 0`.

## Scope

The module takes arbitrary morphisms `p`, `l`, `π`. It needs only the
retraction identities `l ≫ π = 𝟙`, not that the `P i` are parabolic. It
does not prove that `Ω(P, P')` is finite in general. Finiteness for the
family is derived from the enumeration `T`.
