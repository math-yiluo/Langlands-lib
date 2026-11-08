# Actual infinite ideles in mixed coordinates

Worker 1692 supplies internal adapters between the actual adelic objects of the
global Hecke target and the mixed-space functions already defined in
`Hecke.MixedSpaceFourier`. The construction uses Mathlib's existing
`InfiniteAdeleRing.ringEquiv_mixedSpace`, with its chosen real and complex
completion embeddings. The number field lies in unrestricted universe `u`.

`mixedInfiniteUnit` maps the infinite part of an actual full idele through that
ring equivalence on units. It preserves multiplication, one and inversion.
On a principal idele it is precisely the mixed embedding of the original
field unit.

`norm_mixedCoordinates` compares the mixed norm with the product of the
completion norms raised to the original place multiplicities. Splitting
places into real and complex places leaves exponent one and two respectively.
The completion embeddings are isometries, giving equality of every factor.
The mixed norm is positive on `mixedInfiniteUnit`. Combining this comparison
with `HeckeDivisor.full_eq_infinite_mul_norm_inv` gives the full normalized
idelic norm as the mixed norm times the inverse positive finite-divisor norm.

`infinite_character_eq_mixed` uses every supplied real and complex character
presentation, without choosing new data. The earlier infinite multiplicative
product formula splits into real and complex products. Each supplied
presentation and its defining polar equality identifies the corresponding
factor with `realCharFun` or `complexCharFun`. This proves equality with
`mixedCharFun` on the actual idele's infinite coordinates.
`character_eq_mixed_mul_finite` then applies the earlier full multiplicative
product formula at any finite set containing the character's integral control
and the idele's nonunit places.

`infinite_additive_eq_mixed` similarly applies the infinite additive product
formula to every infinite adele. The supplied scales give the real Fourier
character and the complex trace character at each place. The character law
combines them into the positive trace character `𝐞(addTrace aR aC x)`.
The complex trace keeps its factor two.

These are direct comparisons of existing objects and supplied local
presentations. They do not assume adelic self-duality, local-data existence,
Poisson summation or the global functional equation, and do not prove those
remaining conclusions.

`norm_mixedCoordinates` reuses `NormOneIdeleClass.norm_ringEquiv_mixedSpace` with unchanged place multiplicities.
