# Skew elements and quadratic coordinates

Module: `Langlands.Algebra.CentralSimple.LandherrQuadraticData`.

Let `E/F` be a separable quadratic extension with nontrivial automorphism
`σ = conjugation F E` from `Langlands.GroupScheme.Examples.SU3RootParametersQuadratic`.
By `conjugation_eq_self_iff`, the elements fixed by `σ` are precisely the image of `F`.
The lemma `exists_not_mem_range` supplies `x` outside this image using only the degree
of the extension. Then `exists_skew` takes `r = x - σ(x)`, which is nonzero and satisfies
`σ(r) = -r`. The definition `skewRoot F E` chooses such an `r`. In characteristic two
this identity makes `r` fixed by `σ`, so `r` lies in the image of `F`.

The quadratic coordinates used here assume characteristic zero. The lemma
`skewRoot_sq_mem` proves that `r²` is fixed by `σ`, and `skewSq F E` chooses `d ∈ F`
mapping to `r²`. The identity `σ(r) = -r` and the nonvanishing of `2r` give
`skewRoot_not_mem_range`. If `d = s²` in `F`, then `(r - s)(r + s) = 0` in `E` would
put `r` in the image of `F`, proving `not_isSquare_skewSq`.

The algebra map `skewLift` sends `ω` to `r`. It is injective because its source is a
field and surjective because the two spaces have dimension two. The equivalence
`quadraticEquiv` packages this bijection as `QuadraticAlgebra F d 0 ≃ₐ[F] E`, so
`exists_eq_add_mul_skewRoot` writes every element of `E` as `a + b r` with `a, b ∈ F`.
For an `F`-algebra `A` and an element `w ∈ A` whose square is the image of `d`,
`liftSkew F E w hw` gives the `F`-algebra map `E → A` sending `r` to `w`.

## Provenance

Elementary Galois theory of quadratic extensions in characteristic zero: `E = F(√d)` with
`√d` negated by the conjugation. These coordinates are used throughout the proof of
Landherr's theorem to write elements of `E ⊗_F R` and the norm form `x² - d y²`.
