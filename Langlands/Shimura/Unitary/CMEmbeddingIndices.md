# CM embeddings as complex factor indices

Let `E` be a totally real number field and let `K/E` be a quadratic extension
with `K` totally complex. Fix a CM section `Φ`, meaning a choice of complex
embedding of `K` above each real embedding of `E`, with the compatibility
`IsCMSection E K Φ` from `HarrisLevels`.

`cmFactorEmbedding Φ` sends `(τ, true)` to `Φ τ` and `(τ, false)` to its
complex conjugate. `cmFactorEmbeddingEquiv Φ hΦ` constructs an equivalence from
these real-place/Boolean pairs to all complex embeddings of `K`. Its inverse
sends `i` to its real place below, together with the Boolean test
`i = Φ (realPlaceBelow E i)`. The first component formula and the characterization
of the second component are exposed as lemmas.

The inverse laws use the published two-embeddings dichotomy over each real
place. Both selected embeddings have the specified real place below, while
total complexity ensures that the selected embedding differs from its complex
conjugate. Thus the Boolean test separates the two possibilities. No arbitrary
enumeration of the embeddings is introduced.

`complexEmbeddingGaloisAction K` constructs the homomorphism from
`Aut(ℂ/ℚ)` to permutations of complex embeddings by postcomposition:
`i ↦ s ∘ i`. This construction is available for any semiring `K`. Its inverse
is postcomposition by `s⁻¹`; its identity and multiplication laws follow by
extensionality from the automorphism laws.

`cmFactorGaloisAction Φ hΦ` conjugates that permutation action through the
constructed embedding equivalence. In particular, the image of the embedding
associated with the transformed index is exactly `s ∘ cmFactorEmbedding Φ p`.
The first component of the transformed index is the real place below that
composite. Its second component is true exactly when that composite equals the
selected CM embedding above the resulting real place. The identity and
multiplication laws are proved by cancellation of the equivalence and its
inverse, giving an actual monoid homomorphism into permutations.

`mem_hodgeStabilizer_cmFactor` rewrites membership in the existing Hodge
stabilizer as invariance of the Hodge function evaluated on these indices under
`cmFactorGaloisAction`. The forward direction specializes the defining
stabilizer equality; the reverse uses surjectivity of the embedding equivalence.

This is an internal construction from `IsCMSection`, `realPlaceBelow`, the
quadratic embedding dichotomy, and the existing definition of `hodgeStabilizer`.
It supplies the embedding indices and their permutation for subsequent matrix
chart transport. It does not construct that chart transport or identify the
Hodge stabilizer with a scheme-cocharacter conjugacy stabilizer. No preservation
of all real scalars by an arbitrary automorphism of `ℂ/ℚ` is assumed.
