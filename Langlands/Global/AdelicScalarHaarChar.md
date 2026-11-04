# Haar scaling of the adeles by positive real ideles

Author: Worker 1179. Part of task 40747bb3 (finite volume of `G(F) \ G(𝔸_F)¹`), with
Worker 235.

Let `F` be a number field, let `n = [F : ℚ]`, and let `σ` be a positive real number. Let
`full F σ` be the Library idele that is `σ` at every infinite place and `1` at every finite
place (`Langlands/Global/PositiveRealIdeles.lean`). This module proves that multiplication
by `full F σ` scales additive Haar measure on the adele ring `𝔸_F = Adeles F` by `σ ^ n`:

`addEquivAddHaarChar (ContinuousAddEquiv.mulLeft (full F σ)) = σ ^ n`.

The Library's `absoluteValue_full` computes the idelic norm of `full F σ` as `σ ^ n`. So
this is the case `a = full F σ` of the classical rule that multiplication by an idele `a`
scales Haar measure on `𝔸_F` by `|a|_𝔸`. Only this case is proved here.

The intended application is the Haar modulus of conjugation by positive torus elements on
the adelic points of a unipotent group, through
`Langlands/HarmonicAnalysis/TriangularHaarModulus.md`.

## Notation

- `InfiniteAdeles F` is Mathlib's `InfiniteAdeleRing F`, the product of the archimedean
  completions. `FiniteAdeles F` is the finite adele ring, and
  `Adeles F = InfiniteAdeles F × FiniteAdeles F` is Mathlib's `AdeleRing` (Library
  `Langlands/Global/Adelic.lean`).
- `infinite F σ` is the unit of `InfiniteAdeles F` with `σ` in every archimedean component.
  At a complex place, `σ` sits inside `ℂ` as a real number. `full F σ` is its image in the
  ideles, with finite component `1`.
- `mixedEmbedding.mixedSpace F = ({w real} → ℝ) × ({w complex} → ℂ)` is Mathlib's mixed
  space. Its `volume` is the product of Lebesgue measures, with Mathlib's volume on `ℂ` in
  the complex factors. `R = InfiniteAdeleRing.ringEquiv_mixedSpace F` is Mathlib's ring
  isomorphism `InfiniteAdeles F ≃+* mixedSpace F`. The Library shows that `R` and `R⁻¹` are
  continuous (`continuous_infiniteAdeleCoordinates(_symm)`,
  `Langlands/Global/ArchimedeanGL.lean`).

## Declarations

- `ringEquiv_mixedSpace_infinite_mul`: for every `x ∈ InfiniteAdeles F`,
  `R (infinite F σ * x) = σ • R x`, where `•` is real scalar multiplication on the mixed
  space.

  Proof. `R` is multiplicative. At a real place, the component of `infinite F σ` is
  `realEmbedding σ`, and the real coordinate map sends it to `σ`. At a complex place,
  `extensionEmbedding (realEmbedding σ) = (σ : ℂ)` (Library
  `extensionEmbedding_realEmbedding`). Multiplying by a real complex number is real scalar
  multiplication.

- `map_infinite_mul_volume`: give `InfiniteAdeles F` any Borel σ-algebra and let
  `μ∞ = R⁻¹_* volume`. Then

  `σ ^ n • (x ↦ infinite F σ * x)_* μ∞ = μ∞`.

  Proof. By the previous lemma, `(infinite F σ * ·) ∘ R⁻¹ = R⁻¹ ∘ (σ • ·)`. The mixed
  space is a real vector space of dimension `n` (Mathlib `mixedEmbedding.finrank`).
  Mathlib's `Measure.map_addHaar_smul` gives `(σ • ·)_* volume = σ⁻ⁿ • volume`. Pushing
  forward along `R⁻¹` gives the claim.

- `addEquivAddHaarChar_mulLeft_full`: for every Borel σ-algebra on `Adeles F`,

  `addEquivAddHaarChar (ContinuousAddEquiv.mulLeft (full F σ)) = σ ^ n`.

  The locally compact structure of `Adeles F` is the Library's `adeles_locallyCompactSpace`.

  Proof.
  1. Give `InfiniteAdeles F` and `FiniteAdeles F` their Borel σ-algebras. Both are second
     countable, and so is `Adeles F` (Library `Langlands/Global/AdelesSecondCountable.lean`).
     `FiniteAdeles F` is locally compact (Library `finiteAdeles_locallyCompactSpace`).
  2. Let `μ∞ = R⁻¹_* volume`. It is an additive Haar measure because `R⁻¹` is a continuous
     additive isomorphism with continuous inverse. Let `μ_f` be Mathlib's `addHaar` on
     `FiniteAdeles F`.
  3. Let `e : InfiniteAdeles F × FiniteAdeles F ≃ₜ+ Adeles F` be the identity map, which is
     well typed because the adele ring is defined as this product. Let
     `μ = e_* (μ∞ × μ_f)`. It is an additive Haar measure on `Adeles F`. Mathlib's
     `regular_of_isAddLeftInvariant`, applied to a compact set with nonempty interior,
     makes it regular.
  4. The finite component of `full F σ` is `1`. So in product coordinates, multiplication
     by `full F σ` is `(infinite F σ * ·) × id`. By `Measure.map_prod_map`, its pushforward
     of `μ∞ × μ_f` is `(infinite F σ * ·)_* μ∞ × μ_f`.
  5. Multiplying by `σ ^ n` and using `map_infinite_mul_volume` together with
     `Measure.prod_smul_left` gives `σ ^ n • (full F σ * ·)_* μ = μ`.
     `addEquivAddHaarChar_eq_of_smul_map` (`TriangularHaarModulus.md`) concludes.

## Provenance

This module is internal. Multiplication by an idele `a` scales the Haar measure of `𝔸_F`
by `|a|_𝔸`. That rule is standard in Tate's thesis and in Weil's *Basic Number Theory*.
This module proves only the case of the idele `full F σ`. The Lean argument, which reduces
to real scalar multiplication on Mathlib's mixed space, is internal.
