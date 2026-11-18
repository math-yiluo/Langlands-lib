# The Hilbert smooth-kernel criterion on finite-dimensional real manifolds

This module states the proposition
`Langlands.Archimedean.HilbertSmoothKernelStatement.{uA,uM,uH}` and proves
nothing. It imports only Mathlib.

## Statement

Let `A` be a finite-dimensional real normed vector space, and let `M` be a
topological space with a charted-space structure modelled on `A` that is a
`C^∞` manifold for the identity model with corners `𝓘(ℝ, A)`; thus `M` has no
boundary or corners. Let `H` be a complex inner-product space that is complete,
that is, a complex Hilbert space. For every map `f : M → H` the proposition
asserts the equivalence of

1. `ContMDiff 𝓘(ℝ, A) 𝓘(ℝ, H) ∞ f`: `f` is real `C^∞` as a map into `H` with its
   given norm, regarded as a real normed space by restriction of scalars;
2. `ContMDiff (𝓘(ℝ, A).prod 𝓘(ℝ, A)) 𝓘(ℝ, ℂ) ∞ K`, where
   `K (x, y) = inner ℂ (f x) (f y)`: the complex-valued scalar kernel is real
   `C^∞` on the product manifold `M × M`, which carries the product charts with
   model `A × A`, and `ℂ` is regarded as a real normed space.

Here `∞` is the scoped notation for `C^∞` smoothness (not analytic smoothness),
and `ContMDiff` includes continuity, so neither side assumes continuity of `f`
separately. The universes `uA`, `uM`, `uH` of `A`, `M` and `H` are independent.
No Hausdorff or second-countability assumption is made on `M`, and `H` need not
be finite-dimensional or separable. No group, representation, unitary action or
preassigned derivative appears.

## Source

Karl-Hermann Neeb, *On Differentiable Vectors for Representations of Infinite
Dimensional Lie Groups*, arXiv:1002.1602v3 (1 December 2010), Theorem 7.1,
printed/PDF pp. 21–23 (source ID `neeb-2010-differentiable-vectors-arxiv-v3`;
published in J. Funct. Anal. 259 (2010)). The theorem reads: let `M` be a smooth
manifold, `H` a Hilbert space and `γ : M → H` a map; then `γ` is smooth if and
only if the kernel `K(x, y) := ⟨γ(x), γ(y)⟩` is a smooth function on `M × M`.

The Lean proposition is the case of a manifold modelled on a finite-dimensional
real space and a complex Hilbert space. Correspondence with the source:

- Neeb's manifolds are modelled on locally convex spaces, with the calculus of
  continuous iterated directional derivatives of Definition 2.1 (PDF pp. 6–7). For a
  domain modelled on a finite-dimensional space and a Banach target (`H` or
  `ℂ`), this (Bastiani) `C^∞` smoothness coincides with the Fréchet `C^∞` smoothness
  that `ContMDiff` expresses, both for `M` and for `M × M`.
- Smoothness in the source refers only to the real structure of `H`, as in the
  Lean statement. Lean requires smoothness of the full complex kernel (real and
  imaginary parts), as does the source for a complex Hilbert space; its real
  part is the real inner-product kernel used in the source's proof.
- Mathlib's complex inner product is conjugate-linear in its first argument.
  Under the opposite convention the kernel becomes `K(y, x)`, the composition of
  `K` with the swap diffeomorphism of `M × M`, so the criterion is unchanged.
- The source does not mention separation axioms for `M`. Both sides of the
  equivalence are local, and the source proof is local (its Step 3 reduces to an
  open subset of the model space), so the Lean statement omits them.

## Source proof (prospective)

The source argues as follows; these are prospective proof steps, not results of
this module. The direction from `f` to `K` holds because the inner product is a
continuous real-bilinear map. Conversely,
`‖f(x) − f(y)‖² = K(x, x) + K(y, y) − 2 Re K(x, y)` gives continuity of `f`. For curves,
the mixed derivative `∂₁∂₂K(t, t)` is the limit of the squared norms of the
difference quotients, which yields a weak derivative and then norm convergence,
so `f` is `C^1`; the derivative has the smooth kernel `∂₁∂₂K`, and iteration
gives `C^∞`. On a manifold one works in charts with directional derivatives: the
tangent map `df` has the smooth kernel `∂_{(v,0)}∂_{(0,w)}K`, hence is continuous,
and iteration gives all orders.

## Intended use

Neeb deduces his Theorem 7.2 (a vector of a unitary representation is smooth
iff its diagonal matrix coefficient is smooth near the identity) from this
criterion, since by unitarity the kernel of an orbit map on a translated
identity neighbourhood is the diagonal coefficient at `h⁻¹g`. The intended
consumer in this project is the corresponding Hilbert-norm smoothness of orbit
maps of unitary actions. This module asserts no such smoothness and constructs
no action.
