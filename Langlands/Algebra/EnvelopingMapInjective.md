# Injective Lie algebra homomorphisms induce injective maps of enveloping algebras

Module `Langlands.Algebra.EnvelopingMapInjective`, namespace
`Langlands.Algebra.UniversalEnveloping`.

## Contents

- `extendedBasis b₁ f hf W hW`: for an injective homomorphism `f : L₁ →ₗ⁅k⁆ L₂` of Lie algebras
  over a field `k` with `L₂` finite-dimensional over `k`, a basis `b₁` of `L₁` indexed by
  `Fin m` and a complement `W` of the range of `f`, the basis of `L₂` indexed by
  `Fin (m + finrank W)` whose first `m` vectors are the `f (b₁ i)` (`extendedBasis_castAdd`,
  under the same hypotheses) and whose remaining vectors form a basis of `W`. The
  finite-dimensionality of `L₂` is needed: the remaining vectors are the finite basis
  `Module.finBasis k W` of the complement `W`.
- `lift_comp_injective`: for finite-dimensional `L₁` and `L₂` and injective `f`, the induced
  algebra map `UniversalEnvelopingAlgebra.lift k (ι ∘ f)` from `U(L₁)` to `U(L₂)` is injective.

## Proof

Take `b₁ = Module.finBasis k L₁` and `b₂ = extendedBasis b₁ f hf W hW`. The induced map sends
the ordered monomial `orderedPBWMonomial b₁ e` to the ordered monomial `orderedPBWMonomial b₂`
of the exponent vector `e` extended by zero along `Fin.castAddOrderEmb`. This holds because the
first vectors of `b₂` are the images of `b₁` and the order embedding preserves the order of the
factors (`ofFn_prod_pow_orderEmbedding`). Extension by zero is injective, so the images of the
ordered PBW basis `orderedPBWBasisOf b₁` of `U(L₁)` are distinct vectors of the ordered PBW basis
of `U(L₂)`. They are therefore linearly independent, and a linear map sending a basis to a
linearly independent family is injective.

This is the standard consequence of the Poincaré–Birkhoff–Witt theorem that the enveloping
algebra of a Lie subalgebra embeds in the enveloping algebra of the whole Lie algebra.
