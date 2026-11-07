# Tangent surjectivity of the conjugation map

Author: Worker 1095.

This helper module of the proof of `BorelPointContainmentStatement` proves
Lemma B. It is a criterion for the conjugation map `(x, h) ↦ x j(h) x⁻¹` of
`BorelPointContainmentDensity` to be surjective on rational tangent vectors
at the rational point `(1, z₀)`. The namespace is
`Langlands.GroupScheme.BorelPointContainment`. The field `k` is arbitrary.

## Objects

- `lieKernel G k` is the Library's Lie algebra of `G`: the kernel of reduction
  `G(k[ε]) → G(k)`, written multiplicatively, with points in the slice over
  `Spec k`. `Lie.kernelTangentEquiv G` identifies it with the rational tangent
  vectors of `G.X` at the identity.
- `Lie.targetMap j k : lieKernel H k →* lieKernel G k` is postcomposition with
  `j`, the differential of `j`.
- `lieKernelConjugation G c` conjugates by the constant `k[ε]`-point
  `Lie.constant G c` of a `k`-point `c`. Below, `c` is
  `G.constantPoint (z₀ ≫ j.hom.hom) P`, the image of `g₀ = j(z₀)` as a point
  over `P = Spec k` in `CommAlgCat` form.
- `IsTangentSurjectiveAt p q f x` (Library,
  `Langlands.AlgebraicGeometry.TangentSmoothness`) says that every rational
  tangent vector of `Y` at `x ≫ f` (a `k[ε]`-point of `Y` over `k` restricting
  to `x ≫ f`) is `s ≫ f` for a rational tangent vector `s` of `X` at `x`.

## Statement

`isTangentSurjectiveAt_conjugation`: let `j : H ⟶ G` and let `z₀` be a
rational point of `H`. Suppose that every `W : lieKernel G k` can be written as

    lieKernelConjugation G c⁻¹ X * Lie.targetMap j k ξ * X⁻¹ = W

for some `X : lieKernel G k` and `ξ : lieKernel H k`, that is,
`W = g₀⁻¹ X g₀ · dj(ξ) · X⁻¹` in `G(k[ε])`. Then `(conjugation j).left` is
surjective on rational tangent vectors at the underlying morphism of
`lift 1 z₀ : Over.mk (𝟙 (Spec k)) ⟶ G.X ⊗ H.X`.

In additive notation on the Lie algebra, the hypothesis says that every
vector is `Ad(g₀⁻¹)X − X + dj(ξ)`. The module `BorelPointContainmentWeights`
proves it for the dynamic centralizer.

## Proof

Let `t` be a rational tangent vector of `G.X` at the image of `(1, z₀)`.
That image is `g₀`, by `lift_conjugation`. Package `t` as a morphism
`T : D ⟶ G.X` over `Spec k`, where `D = Spec k[ε]`, and let `a : Spec k ⟶ D`
be the augmentation. Then `a ≫ T = g₀`. Let `C` be the constant
`k[ε]`-point of `g₀`. The point `w = C⁻¹ * T` restricts to `1`, so it is an
element `W` of `lieKernel G k`, via `Lie.kernelTangentEquiv`. The hypothesis
gives `X` and `ξ` with `C⁻¹ X C · dj(ξ) · X⁻¹ = w` (after rewriting
`Lie.constant G c = C` by `constantPoint_naturality`). Put

    s = lift X (H.constantPoint z₀ D * ξ) : D ⟶ G.X ⊗ H.X.

Then `a ≫ s = lift 1 z₀`, because `X` and `ξ` restrict to `1`. Also
`s ≫ conjugation j = X · (C · dj(ξ)) · X⁻¹`, by `lift_conjugation`,
`MonObj.mul_comp` and `constantPoint_comp`. A group calculation shows that
this equals `C · (C⁻¹ X C · dj(ξ) · X⁻¹) = C · (C⁻¹ T) = T`. So `s.left` is a
rational tangent vector at `(1, z₀)` mapping to `t`.

## Provenance

This is a standard differential computation, internal to this proof. The
differential of `(x, h) ↦ x j(h) x⁻¹` at `(1, z₀)`, translated back to the
identity, is `(X, ξ) ↦ Ad(g₀⁻¹)X − X + dj(ξ)`. Milne's proof of
Corollary 17.34 (via Theorem 17.33 and Lemma 17.32) uses a dimension count
instead of this computation.
