# Harris reflex field at the prescribed complex embedding

`Langlands.Shimura.HarrisReflexAtEmbeddingStatement` starts with an even-degree
totally real field `E₀`, a totally complex quadratic extension `E/E₀`, an
imaginary quadratic subfield given by `ι : K₀ →+* E`, and a specified complex
embedding `e` of `E`. The supplied `CentralSimpleUnitaryData E₀ E A n` has
rank `n > 1` and is assumed to have signature `(n−1,1)` at the real embedding
below `e` and `(n,0)` elsewhere. These signatures refer to the actual
scalar-extended algebra with involution, not to a freely assigned label.

The conclusion asks for charts on that datum for the section
`harrisCMSection E₀ ι (e.comp ι)`. Their distinguished real place must be
`realPlaceBelow E₀ e`, and their distinguished complex embedding must be `e`.
The reflex field of the actual positive homomorphism constructed from those
charts, `D.realReflexField C`, is the intermediate field `e(E)` in `ℂ`.

## Provenance and proof boundary

Harris, *The local Langlands conjecture for GL(n) over a p-adic field, n < p*
(1998), §1, Theorem 1.2(ii) and the paragraph following it, p. 185, gives the
compositum and the reflex-field conclusion. The signatures come from Harris,
*Galois properties of cohomological automorphic forms on GL(n)* (1999), §1,
equation (1.1), p. 301; the induced CM type is chosen in §4, pp. 308–309.
This derived interface specializes these choices to the real embedding
below `e` and the embedding `e.comp ι` of `K₀`. Harris–Taylor, *The Geometry
and Cohomology of Some Simple Shimura Varieties* (2001), VII.1.9,
pp. 227–228, explains the role of the prescribed complex embedding.
The interface does not assert existence of the global algebra with
prescribed signatures. The intended proof uses
`HasSignature.exists_centerCompatible` at each real place without changing
the distinguished place, `eq_harrisCMSection_realPlaceBelow_iff` at `e`, and
`CentralSimpleUnitaryData.realReflexField_eq_distinguishedImage`. In rank
two, the positive even degree gives another real embedding, so the
exceptional single-real-place case of the reflex calculation does not apply.
Only the proposition is defined here.
