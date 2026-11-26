# Harris reflex field at the prescribed complex embedding: proof

`Langlands.Shimura.harrisReflexAtEmbedding` proves
`Langlands.Shimura.HarrisReflexAtEmbeddingStatement` in all its universes,
without changing the statement or its imports. The setting is that of the
statement: an even-degree totally real field `E₀`, a totally complex
quadratic extension `E`, an imaginary quadratic field `K₀` with
`ι : K₀ →+* E`, a complex embedding `e : E →+* ℂ`, and
`D : CentralSimpleUnitaryData E₀ E A n` with signature `(n − 1, 1)` at
`realPlaceBelow E₀ e` and `(n, 0)` at every other real place. The proof
constructs charts for the section `harrisCMSection E₀ ι (e.comp ι)` whose
distinguished real place is `realPlaceBelow E₀ e`, whose distinguished
complex embedding is `e`, and for which `D.realReflexField C` is
`e.toRatAlgHom.fieldRange`. The rank-two case is covered.

## Mathematical source

Harris, *The local Langlands conjecture for GL(n) over a p-adic field,
n < p* (Invent. Math. 134, 1998), §1, Theorem 1.2(ii) and the paragraph
following it, p. 185, observes that for a CM field `E = E₀K₀` of the form in
(ii) the reflex field is `E` itself; inside `ℂ` this is the image of the CM
field under the chosen complex embedding. The signatures are those of Harris,
*Galois properties of cohomological automorphic forms on GL(n)* (J. Math.
Kyoto Univ. 39, 1999), §1, equation (1.1), p. 301, and the CM type induced
from the imaginary quadratic subfield is the one of §4 there, pp. 308–309.
Harris–Taylor, *The Geometry and Cohomology of Some Simple Shimura
Varieties* (2001), VII.1.9, pp. 227–228, describe the role of the prescribed
complex embedding. The Lean proof below assembles results already in the
Library; it follows the source in fixing the noncompact real place below the
chosen embedding before choosing charts.

## The Lean proof

**Charts at a prescribed place.** `HarrisSignatureCharts.ofSignatureAt`
takes `1 < n`, a real embedding `τ₁`, a signature `(n − 1, 1)` witness at
`τ₁`, signature `(n, 0)` witnesses at every other real embedding, and a CM
section `Φ` (`IsCMSection E K Φ`). At each real embedding `τ` it applies
`HasSignature.exists_centerCompatible` with the complex embedding `Φ τ`,
which supplies an algebra isomorphism `ℝ ⊗[E] A ≃ₐ[ℝ] Matrix (Fin n) (Fin n) ℂ`
compatible with the involution and on which the centre acts through `Φ τ`.
Its distinguished place is `τ₁` by definition
(`HarrisSignatureCharts.ofSignatureAt_distinguished`). It differs from the
existing `HarrisSignatureCharts.ofSignature` only in that the distinguished
place is given, not chosen from an existential signature hypothesis.

**The distinguished embedding is `e`.** The charts used are
`ofSignatureAt D.rank_gt_one (realPlaceBelow E₀ e)` for the section
`harrisCMSection E₀ ι (e.comp ι)`, whose CM-section property is
`isCMSection_harrisCMSection`. Their distinguished complex embedding is the
section's value at `realPlaceBelow E₀ e`. Since `e.comp ι = e.comp ι`,
`eq_harrisCMSection_realPlaceBelow_iff` shows that this value is `e`.

**A second real place.** `exists_realEmbedding_ne_of_even_finrank` shows
that a totally real number field of even degree has, for every real
embedding `τ₁`, a real embedding different from `τ₁`. The number of real
embeddings equals the degree, by
`Langlands.Global.TotallyReal.realComplexEmbeddings` (real and complex
embeddings of a totally real field correspond) and Mathlib's
`NumberField.Embeddings.card`. The degree is positive and even, hence at
least two.

**The reflex field.** With the second real place,
`CentralSimpleUnitaryData.realReflexField_eq_distinguishedImage` (hypothesis
`3 ≤ n ∨ ∃ τ, τ ≠ C.distinguished`, here the right-hand alternative for
every `n`) gives `D.realReflexField C = C.distinguishedImage`. By definition
`C.distinguishedImage` is `C.distinguishedEmbedding.toRatAlgHom.fieldRange`,
which is `e.toRatAlgHom.fieldRange` by the previous step. In rank two this
uses the second real place; the exceptional rank-two case with a single real
place, where `CentralSimpleUnitaryData.realReflexField_eq_bot` gives `ℚ`,
cannot occur because the degree is even.

## Scope

The module proves only the statement above and the two supporting results
named here. It does not construct a central simple algebra with prescribed
signatures; the datum `D` and its signature witnesses are hypotheses.
