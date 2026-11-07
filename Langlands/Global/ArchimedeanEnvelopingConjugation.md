# Complex conjugation of the archimedean enveloping algebra

This module defines complex conjugation on the complexified Lie algebra
`ℂ ⊗[ℝ] 𝔤` of `GL_n(F ⊗ ℝ)` and on its universal enveloping algebra. It also
defines pointwise complex conjugation of smooth functions on the archimedean
group, and shows that this conjugation intertwines the genuine enveloping action
with the conjugation of the enveloping algebra.

The construction is standard and is not taken from a particular source. It is
needed to make the complex conjugate of an automorphic realization stable under
the full differential action and to transport center-finiteness.

## Definitions

- `complexConj K n`: the real-linear map `z ⊗ X ↦ conj z ⊗ X` on
  `ComplexLieAlgebra K n = ℂ ⊗[ℝ] RealLieAlgebra K n`.
- `ConjEnvelopingAlgebra K n`: a type synonym of the enveloping algebra
  `EnvelopingAlgebra K n`, with the same ring structure. A complex scalar `c`
  acts on it through `algebraMap (conj c)`.
- `conjGenerator K n`: the map `x ↦ ι(complexConj x)` into
  `ConjEnvelopingAlgebra K n`. It is a complex Lie algebra homomorphism for the
  conjugated scalar action.
- `envelopingConjAlgHom K n`: the algebra map out of the universal enveloping
  algebra lifted from `conjGenerator` by the universal property.
- `envelopingConj K n`: the same map as a ring endomorphism
  `EnvelopingAlgebra K n →+* EnvelopingAlgebra K n`.
- `centerConj K n`: the restriction of `envelopingConj` to the algebra center
  `EnvelopingCenter K n`.
- `smoothConj K n`: pointwise complex conjugation
  `f ↦ (g ↦ conj (f g))` on `SmoothFunctions K n`, a conjugate-linear map
  (`→ₛₗ[starRingEnd ℂ]`). Smoothness holds because conjugation is a real
  continuous linear map of `ℂ`.
- `conjEnd K n A = smoothConj ∘ A ∘ smoothConj`, for a complex-linear
  endomorphism `A` of the smooth functions.

## Theorems

- `complexConj_tmul`, `complexConj_complexify`, `complexConj_complexConj`:
  `complexConj (z ⊗ X) = conj z ⊗ X`; it fixes the image of the real Lie algebra
  and is an involution.
- `complexConj_smul`: `complexConj (c • x) = conj c • complexConj x`.
- `complexConj_lie`: `complexConj` preserves the Lie bracket. The proof checks
  pure tensors, where the bracket is `(z ⊗ X, w ⊗ Y) ↦ z w ⊗ [X, Y]`.
- `envelopingConj_generator`: `envelopingConj (ι x) = ι (complexConj x)`.
- `envelopingConj_algebraMap`, `envelopingConj_smul`: `envelopingConj` is
  conjugate-linear.
- `envelopingConj_envelopingConj`, `envelopingConj_bijective`: `envelopingConj`
  is an involution. The composite of `envelopingConj` with itself is a complex
  algebra map that fixes every generator `ι x`. By the uniqueness part of the
  universal property it is the identity.
- `envelopingConj_mem_center`, `centerInclusion_centerConj`,
  `centerConj_centerConj`: `envelopingConj` maps the center into itself because
  it is a bijective ring map. `centerConj` is an involution.
- `smoothConj_val`, `smoothConj_smoothConj`: the value formula, and
  `smoothConj` is an involution.
- `smoothConj_smoothRightAction`: conjugation commutes with right translation by
  an archimedean group element. Both sides are equal by definition.
- `smoothConj_smoothDifferential`: conjugation commutes with each real
  directional derivative `smoothDifferential X`. The coordinate expression of
  `smoothConj f` is the composite of the real continuous linear map
  `Complex.conjCLE` with the coordinate expression of `f`. The chain rule gives
  the Fréchet derivative of that composite, and the coordinate expression of `f`
  is differentiable at every invertible matrix.
- `conjEnd_apply`, `conjEnd_smul`, `conjEnd_mul`, `conjEnd_conjEnd`,
  `conjEnd_smoothDifferential`: `conjEnd` is multiplicative, conjugate-linear in
  scalars and an involution, and it fixes every real directional derivative.
- `envelopingAction_envelopingConj`: for every `u`,
  `envelopingAction (envelopingConj u) = conjEnd (envelopingAction u)`. The map
  `v ↦ conjEnd (envelopingAction (envelopingConj v))` is a complex algebra map.
  On a generator `ι (z ⊗ X)` it equals `conj (conj z) • smoothDifferential X`,
  which is the action of `ι (z ⊗ X)`. Uniqueness of lifts
  (`UniversalEnvelopingAlgebra.lift_unique`) identifies it with
  `envelopingAction`. Applying this identity to `envelopingConj u` and using the
  involution property gives the theorem.
- `smoothConj_envelopingAction`:
  `conj (u · f) = envelopingConj u · conj f`.
- `smoothConj_centerAction`: the same identity for the action of the center,
  with `centerConj`.
