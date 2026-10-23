# Gelfand's trick for compact-open Hecke corners

This module proves two general facts about the published compact-open Hecke
corner `Langlands.Hecke.HeckeAlgebra.Corner μ K hK`. Here `G` is a topological
group with Borel σ-algebra, `μ` is a left Haar measure, and `K` is an open
subgroup with compact underlying set. The corner is the convolution algebra of
`K`-bi-invariant test functions. It is a helper for the spherical fixed-line
proof in `Langlands.Representation.Unramified.SphericalFixedLineProof`.

Provenance: commutativity of the spherical Hecke algebra is a source fact. Borel
(1979), *Automorphic L-functions*, §7.1 (printed page 39, PDF page 48), identifies
`H(G(k), Q)` with the commutative algebra `C[Y/kW]` through the Satake isomorphism.
Gross (1998), *On the Satake isomorphism*, §6 (PDF page 11), uses this commutativity
when an unramified representation gives a character `H_K → End(π^K) = C`. The Lean
route is instead the classical Gelfand argument: an automorphism that preserves the
measure and reverses each double coset. It is stated here for an arbitrary
compact-open corner and an arbitrary automorphism. This formulation and its proof
are internal derivations from Mathlib's Haar-character API and the published corner
API, not quotations of a numbered theorem in those sources.

## Measure preservation from a stable compact open subgroup

`Langlands.Hecke.measurePreserving_of_preimage_eq` assumes `G` is locally compact
and `μ` is regular. Let `θ : G ≃ₜ* G` be a continuous multiplicative equivalence
with `θ ⁻¹' K = K`. Then `θ` preserves `μ`.

Proof. Mathlib's `mulEquivHaarChar_smul_preimage` gives
`mulEquivHaarChar θ • μ (θ ⁻¹' K) = μ K`. Because `θ ⁻¹' K = K`, the scalar
multiplies `μ K` to itself. `μ K` is positive because `K` is a nonempty open set,
and finite because `K` is compact, so `ENNReal.mul_left_inj` cancels it. The
modular character `mulEquivHaarChar θ` is therefore `1`. Then
`mulEquivHaarChar_smul_map` says `map θ μ = μ`, and `θ` is measurable because it
is continuous.

## Gelfand's commutativity criterion

`Langlands.Hecke.HeckeAlgebra.Corner.apply_mul_mul` records the bi-invariance
`f (k₁ * x * k₂) = f x` of a corner element for `k₁ k₂ ∈ K`. It is proved from
the published `leftInvariant` and `rightInvariant` lemmas.

`Langlands.Hecke.HeckeAlgebra.Corner.mul_comm_of_measurePreserving` assumes:

- `θ : G ≃ₜ* G` preserves `μ`;
- every `x` satisfies `θ x = k₁ * x⁻¹ * k₂` for some `k₁ k₂ ∈ K`.

Then any two corner elements `f` and `g` commute: `f * g = g * f`.

Proof. Bi-invariance and the double-coset hypothesis give `h (θ z) = h z⁻¹` for
every corner element `h`. Equality of corner elements reduces, by `Subtype.ext`
and `HeckeAlgebra.ext`, to pointwise equality of convolutions. Apply this symmetry
to `f * g` (itself a corner element) to rewrite `(f * g) x` as `(f * g) (θ x⁻¹)`.
Then expand with the published `mul_apply`:
`(f * g) x = ∫ f y * g (y⁻¹ * x) dμ(y)`. The chain of equalities is:

1. Change variables `y = θ u`. This uses `MeasurePreserving.integral_comp` and the
   measurable embedding of the homeomorphism `θ`.
2. Rewrite each factor with the symmetry `h (θ z) = h z⁻¹` and the group laws.
   The integrand becomes `f u⁻¹ * g (x * u)`.
3. Left-translate by `x⁻¹`, using left invariance of the Haar integral
   (`integral_mul_left_eq_self`). This gives `∫ f (y⁻¹ * x) * g y dμ(y)`.
4. Commute the complex factors. The result is `(g * f) x`.

No unimodularity of `G` is used; only left invariance and `θ`-invariance of `μ`.
