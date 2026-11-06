# Fourier inversion over `A_G` on a discrete-series orbit with the actual central characters

Lean module: `Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalOrbitCentralInversion`,
namespace `Langlands.HarishChandraSchwartz`. It imports:

- `Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalOrbitFourierInversion` (Worker 249):
  `rationalOrbitInversionIntegrand`, `integral_rationalOrbitInversionIntegrand`,
  `integral_rationalOrbitInversionIntegrand_eq_zero`, stated for a function `cc` on the orbit
  with the twist law `hcc` as a hypothesis;
- `Langlands.Representation.Plancherel.DiscreteSeriesCentralCharacter` (Worker 200): the actual
  unitary central character of a discrete-series class and its restriction to a central
  subgroup, `discreteSeriesCentralRestriction`, with the twist law
  `discreteSeriesCentralRestriction_orbitMap` and `unitaryUnramifiedCircleCharacter_coe`.

## Provenance

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques, d'après
Harish-Chandra*, J. Inst. Math. Jussieu 2 (2003), 235–333, DOI 10.1017/S1474748003000082.

- Proof of Proposition VII.2.1, case `M = G`, printed pp. 317–318 (PDF pp. 83–84):
  "Pour toute représentation lisse `π` de `G` admettant un caractère central, notons `χ_π` la
  restriction à `A_G` de ce caractère", and the Fourier inversion
  `ϕ(g) = ∑_{ω ∈ O ; χ_ω = χ_{ω'}} (E^G_G ψ_ω)(g)` (quoted in `RationalOrbitFourierInversion.md`).

This module specializes `RationalOrbitFourierInversion` to `cc(ω) = χ_ω`, the restriction to
`A_G` of the actual central character of the class `ω`. The definition and the statements are
derived for this purpose.

## Scope and hypotheses

The setting of `RationalOrbitFourierInversion`: `F` a nonarchimedean local field, `G` an affine
group scheme over `F` locally of finite type with the canonical rational-point topology, `T` an
affine commutative group scheme, `s : T → G` with `hs : GroupScheme.IsCentral s`,
`A_G = s(T(F))`, a measurable space on `G(F)/A_G` with a Haar measure `mu`, and
`hindex : (RenardCartan.splitValuationImage s).FiniteIndex`.

- `rationalOrbitCentralCharacter s hs mu omega ω`: `mu` Haar, `omega` a discrete-series class
  (square integrable modulo `A_G` for `mu`), `ω` in its orbit.
- `rationalOrbitCentralCharacter_orbitMap`: no further hypotheses (`T` need not be affine).
- `integral_rationalOrbitCentralInversion_eq_zero s hs mu hindex hG omega ν eta h hΦ`:
  `hG : GroupScheme.IsConnectedReductive G`, a measurable space with `BorelSpace` on `A_G`,
  `ν` left invariant, `h`: some `b ∈ A_G ∩ G¹` has `η(b) ≠ χ_{ω₀}(b)`, and `hΦ : Continuous Φ`.
- `integral_rationalOrbitCentralInversion s hs mu hindex hG omega ν eta h hΦ hint`: `hG`, the
  same measurable structure and `ν`, `h`: `η(b) = χ_{ω₀}(b)` for every `b ∈ A_G ∩ G¹`, `hΦ`, and
  `hint`: the orbit integrand is `ν`-integrable.

## Definitions

- `rationalOrbitCentralCharacter s hs mu omega ω = discreteSeriesCentralRestriction A_G _ mu
  A_G _ ω`, i.e. `χ_ω : A_G →* Circle`.

## Results

- `rationalOrbitCentralCharacter_orbitMap`: `χ_{χ ω₀}(a) = χ(a) χ_{ω₀}(a)` for
  `χ ∈ Im X(G)` and `a ∈ A_G`, in the form of the hypothesis `hcc`.
- `integral_rationalOrbitCentralInversion_eq_zero`: if `η ≠ χ_{ω₀}` at a point of `A_G ∩ G¹`,
  then `∫_{A_G} η(a⁻¹) ∫_O Φ(ω) χ_ω(a) dω dν(a) = 0`.
- `integral_rationalOrbitCentralInversion`: if `η = χ_{ω₀}` on `A_G ∩ G¹`,
  `∫_{A_G} η(a⁻¹) ∫_O Φ(ω) χ_ω(a) dω dν(a) = ν(A_G ∩ G¹) ∑ᶠ_{ω ∈ O ; χ_ω = η} Φ(ω)`.

## Proof notes

1. `rationalOrbitCentralCharacter_orbitMap` is `discreteSeriesCentralRestriction_orbitMap` read
   in `ℂ` (`Circle.coe_mul`, `unitaryUnramifiedCircleCharacter_coe`).
2. The two theorems are `integral_rationalOrbitInversionIntegrand_eq_zero` and
   `integral_rationalOrbitInversionIntegrand` with `cc = rationalOrbitCentralCharacter`,
   `c = χ_{ω₀}` and `hcc` from step 1.

## Open obligations

As in `RationalOrbitFourierInversion`: the normalization `mes(A_G ∩ K) = 1`, the choice of `Φ`
as `ω ↦ (E^G_G ψ_ω)(g)` together with the integrability of the integrand, and the remaining
steps of Proposition VII.2.1. For the continuity of `Φ`, the Library has
`continuous_unitaryOrbitCoefficient` (`ProductInducedOrbitCoefficientSmoothness`, Worker 200)
for the orbit coefficients of a product-induced discrete series, under all the premises listed
in that module's Markdown (among them `HasLaurentUnitaryCoordinates ν e` and `Continuous e` for
the torus coordinates `e`); this module does not use it.
