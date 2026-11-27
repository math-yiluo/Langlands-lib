# The integral closure of a local ring at the center of a discrete valuation ring

Module `Langlands.CommutativeAlgebra.IntegralClosureDvrCenter`, namespace
`Langlands.CommutativeAlgebra.IntegralClosureDvrCenter`. It imports only `Langlands.MathlibBase`.

Setting: rings `A`, `O` and a field `K` with algebra structures `A → K`, `O → K`, `A → O` and
`IsScalarTower A O K`, where `K` is the fraction field of `O` (`IsFractionRing O K`). Write `B`
for the integral closure `integralClosure A K`. The module identifies `O`, when it is a
discrete valuation ring dominating the local ring `A`, with a localization of `B`, and reads
exponents of ideals of `B` at the corresponding prime off the valuation of `O`. It is the
commutative algebra behind the local ring of a curve at a point of a fibre of a finite morphism
(`Langlands.Correspondence.Laumon.CurveSemilocalRing`). The content is standard commutative
algebra, proved here in the form needed; besides Mathlib it uses that the localization of a
Dedekind domain at a nonzero prime is a discrete valuation ring (Serre, *Local Fields*, I §3,
Prop. 4).

## Definitions

| Declaration | Content |
|---|---|
| `centerIdeal A O K : Ideal (integralClosure A K)` | for `O` local: the ideal of `B` spanned by the elements of `B` that are images of elements of `𝔪_O`, the ideal `B ∩ 𝔪_O` |
| `toRing A O K : integralClosure A K →+* O` | for `O` integrally closed: the inclusion of `B` in `O` |

`toRing` exists because an element of `B` is integral over `O`, hence in `O`
(`mem_range_of_mem_integralClosure`, by `IsIntegrallyClosed.isIntegral_iff`); it is defined by
inverting `O ≃ (algebraMap O K).range`.

## Results

| Declaration | Hypotheses (besides the setting) | Statement |
|---|---|---|
| `algebraMap_toRing` | `O` integrally closed | `algebraMap O K (toRing A O K b) = b` |
| `toRing_injective`, `toRing_algebraMap` | `O` integrally closed | `toRing` is injective and restricts to `algebraMap A O` on `A` |
| `centerIdeal_eq_comap`, `mem_centerIdeal_iff` | `O` local, integrally closed | `centerIdeal A O K = (𝔪_O).comap (toRing A O K)`; `b ∈ centerIdeal A O K ↔ ∃ m ∈ 𝔪_O, algebraMap O K m = b` |
| `centerIdeal_under`, `centerIdeal_liesOver`, `centerIdeal_isPrime` | moreover `A` local and `A → O` a local homomorphism | `centerIdeal A O K` is prime and lies over `𝔪_A` |
| `centerIdeal_ne_bot`, `centerIdeal_isMaximal` | moreover `𝔪_A ≠ ⊥`, `A → K` injective (and `B` Dedekind for maximality) | `centerIdeal A O K` is nonzero and maximal |
| `mem_maximalIdeal_pow_iff` | `O` a discrete valuation ring | `x ∈ 𝔪_O ^ m ↔ m ≤ addVal O x` |
| `isLocalization_atPrime` | `O` a discrete valuation ring, `A` local with `𝔪_A ≠ ⊥`, `A → O` local, `A → K` injective, `K` algebraic over `A`, `B` Dedekind | for the algebra structure `(toRing A O K).toAlgebra`, `IsLocalization.AtPrime O (centerIdeal A O K)` |
| `mem_centerIdeal_pow_iff` | as for `isLocalization_atPrime` | `b ∈ centerIdeal A O K ^ m ↔ toRing A O K b ∈ 𝔪_O ^ m` |
| `pow_dvd_iff` | same | `centerIdeal A O K ^ m ∣ I ↔ ∀ d ∈ I, m ≤ addVal O (toRing A O K d)` |
| `isLeast_count_normalizedFactors` | same, `I ≠ ⊥` | the exponent `(normalizedFactors I).count (centerIdeal A O K)` is the least element of `{addVal O (toRing A O K d) | d ∈ I, d ≠ 0}` (in `ℕ∞`) |
| `count_normalizedFactors_span_singleton` | same, `b ≠ 0` | the exponent of `centerIdeal A O K` in `Ideal.span {b}` is `addVal O (toRing A O K b)` |
| `ramificationIdx_centerIdeal` | same, `𝔪_A = Ideal.span {t}` | `(centerIdeal A O K).ramificationIdx A = addVal O (algebraMap A O t)` (in `ℕ∞`) |

Here `addVal O` is `IsDiscreteValuationRing.addVal`, `normalizedFactors` is
`UniqueFactorizationMonoid.normalizedFactors` and `ramificationIdx` is `Ideal.ramificationIdx`.

## Proofs

- **`isLocalization_atPrime`.** Write `P = centerIdeal A O K`. Elements of `B` outside `P` map to
  units of `O` (`centerIdeal_eq_comap`), and `toRing` is injective, so it remains to write each
  `z ∈ O` as `toRing b / toRing s` with `s ∉ P`. As `K` is algebraic over `A`, there is
  `0 ≠ a ∈ A` with `a z` integral over `A` (`IsAlgebraic.exists_integral_multiple`), so
  `z · toRing a = toRing b` with `b = a z ∈ B`. The localization `V` of `B` at `P` is a discrete
  valuation ring (`IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain`), hence a
  valuation ring, and the images of `a` and `b` in `V` are comparable (`ValuationRing.cond`):
  either `b = a c` or `a = b c` for some `c ∈ V`. Through the lift `V → O` of `toRing`
  (`IsLocalization.lift`), the first case gives `z` as the image of `c`; in the second
  `z · (image of c) = 1`, which forces `c` to be a unit of `V`, and `z` is the image of `c⁻¹`.
- **Exponents.** By `isLocalization_atPrime` and
  `IsLocalization.AtPrime.under_maximalIdeal_pow`, `P ^ m` is the preimage of `𝔪_O ^ m`
  (`mem_centerIdeal_pow_iff`), so divisibility by `P ^ m` is a bound on valuations (`pow_dvd_iff`,
  with `mem_maximalIdeal_pow_iff`). For `n` the exponent of `P` in `I`
  (`emultiplicity_eq_count_normalizedFactors`), `P ^ n ∣ I` and `P ^ (n+1) ∤ I` give
  `isLeast_count_normalizedFactors`. For `I = (b)` the least valuation is that of `b`
  (`IsDiscreteValuationRing.addVal_mul`), and `ramificationIdx_centerIdeal` applies this to
  `b = t`, `𝔪_A B = (t)`, with `Ideal.IsDedekindDomain.ramificationIdx_eq_normalizedFactors_count`.
