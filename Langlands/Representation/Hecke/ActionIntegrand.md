# Finite-image integrands for smooth Hecke actions

This is the preliminary integrand construction for the natural Hecke action
recalled in Flath, *Decomposition of representations into tensor products*
(1979), section 1, printed page 179, PDF page 175, registered as
`flath-1979-tensor-products`. The implementation of the finite-image argument
and its intrinsic laws is internal; Flath does not give this detailed proof.

Let `G` be a topological group and let `ρ : Representation ℂ G V` satisfy the
published predicate `Langlands.IsSmooth`. The group and vector space have
independent universes. The vector space is an arbitrary algebraic complex
module: no topology, norm, completeness, or finite-dimensionality is assumed.
The function `f` belongs to the existing
`Langlands.HarmonicAnalysis.SchwartzBruhat G`, exactly the carrier used by the
Hecke test-function API. Measurable structure on the group is required
only with `OpensMeasurableSpace G`, so that open fibers are measurable.

For a smooth vector `v`, choose an open subgroup fixing it. The orbit map
`g ↦ ρ(g)v` is constant on each left coset of that subgroup. The Lean proof uses
the open neighborhood `{x | g⁻¹*x ∈ K}` and the representation multiplication
law to prove local constancy. Multiplying by the locally constant scalar `f(g)`
preserves local constancy. The weighted map has compact support because its
support is contained in the support of `f`. The helper construction in
`HarmonicAnalysis/AlgebraicIntegrand.lean` therefore supplies the actual simple
function

`actionIntegrand ρ hρ f v (g) = f(g) • ρ(g)v`.

The positive `ρ(g)` convention is explicit. For any measure finite on compact
sets, this simple function has finite-measure support. This applies in
particular to left Haar measure in the later locally compact Hausdorff setting;
no global sigma-finiteness assumption enters this construction.

`actionIntegrandLinear` packages pointwise complex bilinearity in `f` and `v`.
Its proofs use linearity of the representation maps, distributivity of scalar
multiplication, and commutativity of complex scalars. The intertwiner identity
is also pointwise: applying an actual representation intertwiner to the
integrand equals the target representation's integrand at the image vector.
It uses the existing Mathlib intertwiner and linear map structures.

This unit does not yet integrate the function or assert a convolution-action
law. The genuine finite fiber-sum integral and published scalar convolution
algebra remain prerequisites for the complete Hecke action. No arbitrary action
or desired algebra law is included as input data.
