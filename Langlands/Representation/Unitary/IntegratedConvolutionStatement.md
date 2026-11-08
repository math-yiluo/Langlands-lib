# The integrated action turns convolution into composition

`Langlands.Analysis.IntegratedActionConvolutionStatement` is a proposition
definition. It supplies no proof.

## Setting

- `G` is a group with a measurable structure for which multiplication
  `G × G → G` and inversion are measurable (`MeasurableMul₂`,
  `MeasurableInv`). No topology is required.
- `μ` is an s-finite, **left** invariant measure on `G`. No unimodularity is
  assumed.
- `E` is a complex Banach space, in a universe independent of that of `G`.
- `π : G →* (E →L[ℂ] E)` is a homomorphism into bounded operators. Every
  `π g` preserves norms, and every orbit map `g ↦ π g x` is `μ`-almost
  everywhere strongly measurable. These are the hypotheses of the published
  `Langlands.Analysis.integratedIsometricAction`, which integrates an
  integrable weight `f` to the bounded operator
  `π(f) x = ∫ g, f g • π g x ∂μ`.
- `f₁ f₂ : G → ℂ` are `μ`-integrable.

## Conclusion

Write `f₁ ⋆ f₂` for the function
`g ↦ ∫ a, f₁ a * f₂ (a⁻¹ * g) ∂μ`. The statement asserts that

1. `f₁ ⋆ f₂` is `μ`-integrable, and
2. for that integrability proof, the integrated operator of `f₁ ⋆ f₂` is the
   composition `π(f₁) ∘ π(f₂)`.

Both assertions are packaged as one existential over the integrability
proof; by proof irrelevance every integrability proof gives the same
operator. The pointwise value of `f₁ ⋆ f₂` is the Bochner integral, which is
zero at points where the integrand is not integrable; by Fubini these
form a `μ`-null set.

No algebra structure on `L¹(G)`, associativity of convolution, continuity of
`f₁ ⋆ f₂`, trace class or automorphic specialization is asserted.

## Sources and provenance

Getz–Hahn, *An Introduction to Automorphic Representations* (2024),
registered as `getz-hahn-2024-automorphic-representations`, SHA-256
`a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507`,
section 3.4, printed pp.85–86 (one-based PDF pp.101–102). Formula (3.9)
defines the convolution with a **right** Haar measure,
`(f₁ ∗ f₂)(g) = ∫ f₁(g h⁻¹) f₂(h) d_r h`, and states that this definition is
chosen so that `π(f₁ ∗ f₂) = π(f₁) ∘ π(f₂)` (Exercise 3.20), where
`π(f) = ∫ f(g) π(g) d_r g`.

The statement is the left-measure mirror of that identity, with the same
operator convention `f(g) π(g)`. The published integrated action and its
consumers in the Library (the compact-quotient and automorphic `L²` results)
use a left invariant measure on `G`. For such a measure the convolution that
makes `π` multiplicative is `g ↦ ∫ f₁(a) f₂(a⁻¹ g) dμ(a)`. On a unimodular
group, such as the adelic points of a connected reductive group, the
substitution `h = a⁻¹ g` turns this into the formula (3.9). That comparison
is explanatory provenance and is not formalized here.

The group and measure hypotheses are those of Mathlib's measurable-group
product theory (`measurePreserving_prod_mul`), which needs measurable
multiplication on the product and s-finiteness. A second countable
topological group with its Borel σ-algebra satisfies the group hypotheses,
and a left Haar measure on a σ-compact locally compact group is σ-finite,
hence s-finite.

## Intended proof

A private proof compiles. On `G × G` with `μ × μ`, the scalar kernel
`K(a, g) = f₁(a) f₂(a⁻¹ g)` composed with the measure-preserving shear
`(a, b) ↦ (a, a b)` is `f₁(a) f₂(b)`, which is integrable; so `K` is
integrable and its partial integral `f₁ ⋆ f₂` is integrable. The vector
kernel `K(a, g) • π g x` has norm `|K(a, g)| ‖x‖`, hence is integrable.
Fubini exchanges the two integrals. In the inner integral, left invariance
substitutes `g = a b`, and `π(a b) = π(a) π(b)` together with continuity
of `π(a)` gives `f₁(a) • π(a) (π(f₂) x)`. Integrating in `a` gives
`π(f₁) (π(f₂) x)`.
