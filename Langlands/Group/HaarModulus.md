# Actual normalizer Haar modulus

The namespace `Langlands.HaarModulus` constructs the positive Haar modulus of
conjugation on an actual subgroup. The module is
`Langlands.Group.HaarModulus`. Worker 76 authored this construction and its
intrinsic proofs. It imports the published compact-open stabilizer construction
of Workers 76 and 128 and the existing positive-character and smooth-twist APIs.

## Conjugation and the positive character

Let `G : Type u` be a topological group and `U : Subgroup G`, with the induced
subgroup topology. Write `N = Subgroup.normalizer (U : Set G)`.
`normalizerConj U g : U ≃ₜ* U` is the continuous multiplicative equivalence whose
ambient value at `u` is `g * u * g⁻¹`. Its inverse has value `g⁻¹ * u * g`.
The two application lemmas record these formulas. Normalizer membership supplies
both subgroup membership proofs; the group laws prove multiplicativity and the
inverse identities. Continuity follows from the ambient multiplication,
inversion and subtype maps. `normalizerConj_one` and `normalizerConj_mul` prove
identity and composition, where conjugation by `g * h` applies `h` first.

Assuming `[LocallyCompactSpace U]`, the definition

```lean
normalizerCharacter U : N →* ℝ≥0ˣ
```

has underlying nonnegative-real value
`MeasureTheory.mulEquivHaarChar (normalizerConj U g)`. The module uses the Borel
measurable space of U locally; no arbitrary measurable structure is an input.
Mathlib's strict positivity makes this value a unit. Its identity and composition
laws prove the monoid-homomorphism fields (commutativity resolves the ordering
in the composition formula). The exported `_apply`, `_one`, `_mul`, `_inv`,
`_pos` and `_ne_zero` lemmas give the value, group laws and positivity explicitly.
The character is determined by the automorphism, independently of a selected
regular Haar measure, through Mathlib's Haar character construction.

## Scaling convention

Put `c = (normalizerCharacter U g : ℝ≥0)` and `α = normalizerConj U g`.
For any regular Haar measure μ on the Borel space U,
`normalizerCharacter_smul_map` states

```text
c • μ.map α = μ.
```

`integral_normalizerConj_symm` states

```text
∫ u, f (α.symm u) ∂μ = c • ∫ u, f u ∂μ.
```

Here `f : U → E`, `E : Type v`, `[NormedAddCommGroup E]`, and
`[NormedSpace ℝ E]`; the universes u and v are independent. This includes real
and complex functions. The formula is for Mathlib's totalized Bochner integral;
no integrability or completeness premise is added. Its proof changes variables
by the inverse measurable equivalence, identifies the pushed measure with the
comap by α, rewrites that comap as `c • μ` using the existing Haar-scaling lemma,
and applies `integral_smul_nnreal_measure`.

This is exactly the inverse-integrand convention in Bernstein–Zelevinsky
1977, Section 1.7. In particular it is the modulus of `u ↦ g*u*g⁻¹`, rather
than the reciprocal group-module convention also discussed there.

## Open kernel

The imported `Langlands.subgroupNonarchimedean` instance from
`Langlands.Topology.Nonarchimedean.Subgroup` supplies `[NonarchimedeanGroup U]` from
`[NonarchimedeanGroup G]`: pull a subgroup identity neighborhood back from G,
choose an ambient open subgroup inside it, and restrict that open subgroup to U.

First `normalizerCharacter_eq_one_of_preimage` proves that a g preserving a
compact open subgroup `K : OpenSubgroup U` has character value one. K is a
positive compact set because it is open and contains the identity. Mathlib's
Haar measure normalized on that set gives K measure one. Applying
`mulEquivHaarChar_smul_preimage` to K and using `α ⁻¹' K = K` yields `c = 1`.

Under `[NonarchimedeanGroup U]`, `isOpen_ker_normalizerCharacter` chooses a compact
open K using `Langlands.compactOpenSubgroupBasis`. The published
`Langlands.compactOpenNormalizerStabilizer U K hK` is an open subgroup of N,
whose membership criterion says precisely that conjugation preserves K.
The preceding calculation puts this open subgroup inside the character kernel;
`Subgroup.isOpen_mono` makes the kernel open. Thus openness is proved from
local compactness and nonarchimedeanness, not assumed as an extra hypothesis.
The stabilizer theorem uses compactness and joint continuity of conjugation;
it was split into the independently published topology module
`Langlands.Topology.CompactOpen.ConjugationStabilizer`.

## Restrictions, half characters and closed wrappers

For any `M : Subgroup G` and `hMU : M ≤ N`,
`restrictCharacter U M hMU : M →* ℝ≥0ˣ` composes the actual character with the
subgroup inclusion; `_apply` records that value. The complex characters
`halfCharacter U M hMU` and `inverseHalfCharacter U M hMU` reuse
`Jacquet.positiveHalfCharacter`, `Jacquet.complexCharacter` and
`Jacquet.inverseHalfCharacter`. Their values are the positive real square root
of the restricted modulus embedded in ℂ, and its inverse. Their `_apply` and
`_sq` lemmas record these formulas and squares, with no complex branch choice.

Restriction preserves open kernel by continuity of the inclusion. The positive
half has exactly the same kernel (`halfCharacter_ker`); the inverse-half open
kernel follows from the existing positive-character API. The corresponding
`isOpen_ker_restrictCharacter`, `isOpen_ker_halfCharacter`, and
`isOpen_ker_inverseHalfCharacter` lemmas assume `[NonarchimedeanGroup U]`.
The two `isSmooth_twist_..._iff` lemmas then apply the published smooth-twist
criterion. They hold for any complex module `V : Type v` and representation of M;
there is no topology on V, finite-dimensionality or admissibility hypothesis.

For a locally compact ambient topological group G and a proof
`hU : IsClosed (U : Set G)`, the four definitions
`closedNormalizerCharacter U hU`, `closedRestrictCharacter U hU M hMU`,
`closedHalfCharacter U hU M hMU`, and
`closedInverseHalfCharacter U hU M hMU` supply local compactness of U internally.
They have no `[LocallyCompactSpace U]` input. If that instance is already
available, their `_eq` lemmas identify them with the general definitions by
reflexivity. Thus the general value and integral formulas apply to closed
subgroups after introducing `letI := hU.locallyCompactSpace`.

With `[LocallyCompactSpace G]` and `[NonarchimedeanGroup G]`, four corresponding
`isOpen_ker_closed...` lemmas and the two
`isSmooth_twist_closedHalfCharacter_iff` and
`isSmooth_twist_closedInverseHalfCharacter_iff` lemmas use only ambient instances
and hU. These specialize to the requested Hausdorff locally compact
nonarchimedean setting. The implemented arguments do not need a Hausdorff
hypothesis, so it is not included in their Lean types. No closedness of M or
local compactness of the normalizer is needed.

## Source and provenance

The original source is I. N. Bernstein and A. V. Zelevinsky, *Induced
representations of reductive p-adic groups I* (1977), registered as
`bernstein-zelevinsky-1977-induced-i`, SHA256
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.
Section 1.7, printed pages 443–444 / PDF pages 4–5, defines the automorphism
modulus by the inverse-integrand formula and then the normalizer character.
Section 1.8(a,b), printed pages 444–445 / PDF pages 5–6, uses its positive and
inverse half powers in induction and localization. Sections 5.1–5.3, printed
pages 459–461 / PDF pages 20–22, supply the general geometric-lemma context in
which normalizer restrictions are needed. The original PDF is retained at
`/home/taskhub/central-library/Bernstein-Zelevinsky--Induced representations of reductive p-adic groups I--1977.pdf`.

The bundled Lean interface, weaker hypotheses, subgroup instance, compact-open
kernel proof and smooth-twist corollaries are derived implementation of that
source construction. They are not attributed to a separately numbered source
result. The analytic input is the pinned Mathlib module
`Mathlib.MeasureTheory.Measure.Haar.MulEquivHaarChar`; the square-root machinery
and smooth-twist proof are reused through published Library imports.
This unit establishes no Jacquet exactness, induction compatibility, geometric
lemma or identification with an explicit GL determinant modulus.
