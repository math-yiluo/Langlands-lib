# Character-weighted integration of product test functions

This module integrates a test function on a triple product against an inverse
character weight on the two outer factors. The result is a test function on
the middle factor, which gives a complex linear map between the published
`Langlands.HarmonicAnalysis.SchwartzBruhat` spaces. The module also
dualizes this map to the published algebraic duals
`Langlands.HarmonicAnalysis.Distribution`. No new test-function or
distribution space is introduced. All declarations below are in the
namespace `Langlands.HarmonicAnalysis`.

## Parenthesization and formula

The triple product is always `G × (Y × G)`. A point is written
`(g₁, (y, g₂))`, and an integration variable `z : G × G` stands for
`(z.1, z.2) = (g₁, g₂)`. For `α : SchwartzBruhat (G × (Y × G))`,

    SchwartzBruhat.characterAverage χ μ α y =
      ∫ z : G × G, α (z.1, (y, z.2)) * ((χ z.1 : ℂ) * (χ z.2 : ℂ))⁻¹ ∂(μ.prod μ).

This is the Bochner integral over `G × G` for Mathlib's product measure
`μ.prod μ`. The exact statement is `SchwartzBruhat.characterAverage_apply`,
which holds by `rfl`. The unpackaged function
`y ↦ ∫ …` is `SchwartzBruhat.characterAverageIntegral χ μ α`.

`SchwartzBruhat.characterAverageLeftAssoc` handles test functions on the
left-associated product `(G × Y) × G`. It first applies the existing
`Hecke.TestFunction.pullback` along `(Homeomorph.prodAssoc G Y G).symm` and then
`characterAverage`. Its evaluation law `characterAverageLeftAssoc_apply` has the
integrand `α ((z.1, y), z.2) * ((χ z.1 : ℂ) * (χ z.2 : ℂ))⁻¹`.

## Hypotheses

- `G : Type uG` and `Y : Type uY` lie in arbitrary universes.
- `G` is a monoid with a topology. Neither inverses nor continuity of
  multiplication is used. `G` also carries a measurable structure in which
  open sets are measurable (`OpensMeasurableSpace G`). This is weaker than
  equipping a Hausdorff topological group with its Borel structure, as the task
  allows.
- `Y` is any topological space. Neither `G` nor `Y` needs to be Hausdorff.
- `χ : ContinuousMonoidHom G ℂˣ`. Composing with the coercion `ℂˣ → ℂ` gives a
  continuous complex-valued function.
- `μ : Measure G` satisfies `[SFinite μ] [IsFiniteMeasureOnCompacts μ]`.
  Local compactness, second countability, σ-compactness and invariance are not
  assumed.

The s-finiteness is needed only because of how Mathlib defines `Measure.prod`.
It is the Giry-monad bind of the kernel `x ↦ Measure.map (Prod.mk x) μ`.
Mathlib's `Measure.map` along a map that is not almost-everywhere measurable is
an arbitrary Dirac mass when the measure is nonzero. Measurability of the slice
kernel is available only for an s-finite second factor
(`measurable_measure_prodMk_left`). Mathlib's documentation of that lemma also
gives a counterexample without s-finiteness. Without `SFinite μ`, the measure
`μ.prod μ` is therefore not controlled. The instance
`MeasureTheory.Measure.prod.instIsFiniteMeasureOnCompacts` makes `μ.prod μ`
finite on compact sets. It also requires the second factor to be s-finite.

The measure hypotheses are used only for integrability and hence for
additivity. The following results hold for every measure `μ` and need no
`OpensMeasurableSpace G`:

- local constancy, `characterAverageIntegral_isLocallyConstant`;
- the support inclusion, `support_characterAverageIntegral_subset`;
- compact support, `hasCompactSupport_characterAverageIntegral`.

## Measurability without countability

On `G × G`, `μ.prod μ` is a measure for Mathlib's product σ-algebra. Without
second countability this σ-algebra can be strictly smaller than the Borel
σ-algebra of the product topology. The module therefore proves measurability
directly for the product σ-algebra, for any spaces `X` and `Z` with
`OpensMeasurableSpace`.

- `SchwartzBruhat.measurableSet_prod_of_isCompact_of_isOpen`: a compact open
  subset `W` of `X × Z` is product-measurable. Every point of `W` lies in an
  open rectangle `U ×ˢ V ⊆ W`. Compactness extracts a finite subcover, so `W`
  is a finite union of measurable rectangles.
- `SchwartzBruhat.measurable_prod`: every test function on `X × Z` is
  product-measurable. Let `S ⊆ ℂ` be a set that does not contain `0`. Its
  preimage is open by local constancy. It is also closed, because it is the
  complement of the open preimage of `Sᶜ`. It lies in the compact support, so
  it is compact and open, and the previous lemma applies. If `0 ∈ S`, pass to
  the complement.
- `SchwartzBruhat.measurable_inverseCharacterWeight`: the weight
  `z ↦ ((χ z.1 : ℂ) * (χ z.2 : ℂ))⁻¹` is product-measurable, because it is
  built from the measurable coordinate projections.
  `SchwartzBruhat.continuous_inverseCharacterWeight` gives its continuity,
  since neither factor vanishes.

## Integrability

`SchwartzBruhat.slice α y : SchwartzBruhat (G × G)` is the slice
`z ↦ α (z.1, (y, z.2))`, with `slice_apply`.

- **Local constancy of the slice.** The slice is `α` composed with a continuous
  map.
- **Compact support of the slice.** Its support is closed, being the preimage
  of the clopen support of `α`. It lies in the compact image of `support α`
  under `q ↦ (q.1, q.2.2)`, so it is a closed subset of a compact set.

`SchwartzBruhat.integrable_mul_prod` proves the following. Let `f` be a test
function on `X × Z`, let `w` be a continuous product-measurable weight, and let
`ρ` be a measure finite on compact sets. Then `f * w` is integrable for `ρ`.
The proof runs as follows:

1. The support `K` of `f` is compact, and clopen, hence product-measurable.
2. `f * w` is continuous, hence bounded on `K`.
3. `K` has finite `ρ`-measure, so `f * w` is integrable on `K` by
   `Measure.integrableOn_of_bounded`.
4. `f * w` vanishes outside `K`.

`SchwartzBruhat.integrable_characterAverage_slice` applies this to
`slice α y`, the inverse character weight and `ρ = μ.prod μ`. That measure is
finite on compact sets by the s-finiteness discussed above. Every displayed
integrand is therefore integrable.

## Local constancy: the compact-tube argument

`SchwartzBruhat.characterAverageIntegral_isLocallyConstant` proves that the
average is eventually constant near every point `y`.

1. **The compact set.** Let `K` be the image of `support α` under
   `π : (g₁, (y', g₂)) ↦ (g₁, g₂)`. It is a compact subset of `G × G`.
2. **Local agreement.** Fix `z ∈ K`. Both functions on `Y × (G × G)`
   - `(y', z') ↦ α (z'.1, (y', z'.2))`, and
   - `(y', z') ↦ α (z'.1, (y, z'.2))`

   are locally constant. Both take the value `α (z.1, (y, z.2))` at `(y, z)`,
   so they agree on a neighbourhood of `(y, z)`.
3. **The tube.** Mathlib's tube lemma for compact sets
   (`IsCompact.eventually_forall_of_forall_eventually`) applies to `K`. It
   gives a neighbourhood of `y` such that, for every `y'` in it and every
   `z ∈ K`, `α (z.1, (y', z.2)) = α (z.1, (y, z.2))`.
4. **Outside `K`.** If `z ∉ K`, then both `α (z.1, (y', z.2))` and
   `α (z.1, (y, z.2))` are zero, for otherwise `z` would be the image under
   `π` of a support point.
5. **Conclusion.** For `y'` in that neighbourhood the integrands agree at every
   point, so the integrals are equal.

`IsLocallyConstant.iff_eventually_eq` turns this into local constancy.

## Support and compact support

- `SchwartzBruhat.support_characterAverageIntegral_subset`: let `y` be outside
  the image of `support α` under the middle projection `q ↦ q.2.1`. Then
  `α (z.1, (y, z.2)) = 0` for every `z`, so the integrand is identically zero
  and so is the integral.
- `SchwartzBruhat.hasCompactSupport_characterAverageIntegral`: by local
  constancy the support is the complement of a clopen fibre, hence closed. It
  lies in the compact middle projection of `support α`, so it is compact.
  Its closure is itself.

The packaged statements use the topological (compact) support of `α`. For a
test function it equals the ordinary support by
`Hecke.TestFunction.tsupport_eq_support`.

- `SchwartzBruhat.support_characterAverage_subset`:
  `support (characterAverage χ μ α) ⊆ (fun q => q.2.1) '' tsupport α`.
- `SchwartzBruhat.tsupport_characterAverage_subset`: the same inclusion for
  `tsupport (characterAverage χ μ α)`.

## Linearity

`SchwartzBruhat.characterAverage` packages the integral with the two properties
above as a `SchwartzBruhat Y` element and is a `ℂ`-linear map.

- **Additivity.** This follows from `integral_add` and uses the integrability
  of both slices.
- **Homogeneity.** This follows from `integral_const_mul`.

## The character sign

The weight is the inverse of the product of both character values,
`((χ z.1 : ℂ) * (χ z.2 : ℂ))⁻¹`. Since `χ` is multiplicative this equals
`(χ (z.1 * z.2))⁻¹`. It is not a positive or absolute-value weight.

Shalika's weight is the complex conjugate `χ̄(u₁u₂)` of a unitary character
(see below). For a unitary character the inverse and the conjugate agree. The
Library's `standardCharacter` takes values in the unit circle through
`Circle.toUnits`, so in the specialization the weight is Shalika's. This
agreement is a remark only: the module states no conjugation lemma.

## The dual map

`Distribution.characterAverageDual χ μ : Distribution Y →ₗ[ℂ] Distribution (G × (Y × G))`
is algebraic precomposition, implemented as
`(SchwartzBruhat.characterAverage χ μ).dualMap`. Its evaluation law
`Distribution.characterAverageDual_apply` states

    characterAverageDual χ μ D α = D (characterAverage χ μ α).

Its hypotheses are those of `characterAverage`. Nothing is claimed about
injectivity, nor any classification of equivariant distributions.

## Upper-unipotent specialization

`standardCharacterAverage F n` takes the following data:

- a prime `p` with `[Fact p.Prime]`;
- a field `F : PadicField.{uF} p` in an arbitrary universe;
- any `n : ℕ`, including `0`.

Its type uses the canonical topology `F.canonicalTopologicalData.topology` and
the Borel σ-algebra `borel (upperUnipotent (n + 1) F.Carrier)`. For every
`ψ : UnitaryAdditiveCharacter F.Carrier` and every measure `μ` on the upper
unipotent subgroup with `[SFinite μ] [IsFiniteMeasureOnCompacts μ]`, it is the
`ℂ`-linear map

    SchwartzBruhat (upperUnipotent (n + 1) F.Carrier ×
        ((Fin (n + 1) → F.Carrierˣ) × upperUnipotent (n + 1) F.Carrier)) →ₗ[ℂ]
      SchwartzBruhat (Fin (n + 1) → F.Carrierˣ).

It is defined as `SchwartzBruhat.characterAverage (standardCharacterContinuous ψ n) μ`.
The body also installs the valuation relation and the local-field structure from
`F.canonicalTopologicalData`, and supplies `BorelSpace` by `rfl`.

`standardCharacterAverage_apply` gives the integrand
`α (z.1, (t, z.2)) * ((standardCharacter ψ n z.1 : ℂ) * (standardCharacter ψ n z.2 : ℂ))⁻¹`
on `upperUnipotent (n + 1) F.Carrier × upperUnipotent (n + 1) F.Carrier`, for
the measure `μ.prod μ`. The published `standardCharacter_apply` evaluates
`(standardCharacter ψ n g : ℂ)` as
`ψ.complex (∑ i : Fin n, g.val i.castSucc i.succ)`. For `n = 0` the sum is
empty and the character is trivial.

## Source correspondence

J. A. Shalika, *The multiplicity one theorem for GLn*, Ann. of Math. (2)
**100** (1974), 171–193, is the registered source
`shalika-1974-multiplicity-one`. The original PDF is
`/home/taskhub/central-library/Shalika--The multiplicity one theorem for GLn--1974.pdf`,
SHA256 `788c5d124024c768aa47c4e8b179475fbcf5b0882a518ae60b19cdc88089f087`.
Worker 724 read the following pages visually.

- **Printed p.173 (PDF page 4).** `G = GL_n`, `H` its diagonal subgroup, `U` the
  upper-triangular unipotent subgroup, and `χ` a unitary character of `U`.
- **Printed p.174 (PDF page 5).** The character formula
  `χ(u) = ψ(a₁x₁₂ + ⋯ + a_{n-1}x_{n-1,n})`.
- **Printed p.176 (PDF page 7).** `M₁ = U × H × U`.
- **Printed p.177 (PDF page 8), Proposition 1.12.** For `α ∈ C_c^∞(M₁)` it
  defines `β_α ∈ C_c^∞(H)` by

      β_α(h) = ∫_{U×U} α(u₁, h, u₂) χ̄(u₁u₂) du₁ du₂,

  with Haar measures on `U`.

The correspondence with this module:

- `G`, `Y` and `μ` play the roles of `U`, `H` and Haar measure.
- `(u₁, h, u₂)` is the point `(z.1, (y, z.2))` of `G × (Y × G)`.
- `du₁ du₂` is `μ.prod μ`.
- `χ̄(u₁u₂)` is the inverse weight discussed above.
- `characterAverage χ μ α` is `β_α`.

In the specialization, Shalika's `n` is `n + 1`, and the Library's
`standardCharacter` is his `χ` with every `aᵢ = 1`. The diagonal subgroup `H` is
modelled by its parameter space `Fin (n + 1) → F.Carrierˣ` rather than as a
subgroup of `GL_{n+1}(F)`.

Shalika states without proof that `β_α` lies in `C_c^∞(H)`. The measurability,
integrability, compact-tube, support and linearity arguments above are internal
derived content, authored by Worker 724 from Mathlib's measure theory and the
published test-function lemmas. The general setting is likewise internal: an
arbitrary monoid `G`, arbitrary `Y` and a non-invariant `μ`.

## Limitations

The module formalizes only the map `α ↦ β_α` and its elementary laws. It does
not formalize the remaining assertions of Proposition 1.12: surjectivity of
`α ↦ β_α`, and the existence and uniqueness of the distribution `τ` with
`T*(α) = τ(β_α)`. It also omits translation covariance of the average under
`U × U`, classification of twisted product distributions, Bruhat orbital
integration (Lemma 1.10, (1.11)), the support statement Proposition 1.13, and
Shalika invariance. None of these is encoded as a field or an assumed
theorem. These remain separate statements and proofs. No imported published
pair is changed.
