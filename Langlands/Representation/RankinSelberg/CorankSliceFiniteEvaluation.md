# Finite evaluation of corank-one determinant slices with common compact support

Module `Langlands.Representation.RankinSelberg.CorankSliceFiniteEvaluation`,
namespace `Langlands.RankinSelberg.CommonLevel`.

## Source and provenance

Derived from JPSS (1983), Section 4.5, printed pages 408–409 (PDF pages 43–44).
There a common compact open level `K` for a family of Whittaker functions bounds
their supports on each determinant slice uniformly, and the slice integrals
become finite sums of point values with coefficients that do not depend on the
parameter. This module formalizes the second half of that argument, the passage
from a common compact support on one slice to integrability and analytic
dependence, in the corank-one setting `GL_(r+2) × GL_(r+1)` of the
`corankOneIntegrand`. The common compact support is a hypothesis here. The
companion module `CorankCommonCompactSupport` proves it, and the final assembly
of `CorankOneEntireSliceStatement` combines the two. The general orbit
statements in the first section are internal tools. JPSS does not state them
separately.

## Right orbits on a left quotient

For a topological group `G`, a subgroup `H` and a subgroup `J`:

- `rightTranslateOrbit H J q` is the set `{q · k : k ∈ J}` of right translates of
  the coset `q ∈ H\G` by elements of `J`. It is defined with the published
  `QuotientIntegration.rightTranslate`.
- `self_mem_rightTranslateOrbit`: `q` lies in its own orbit.
- `rightTranslateOrbit_eq_of_mem`: a point of an orbit has the same orbit.
- `disjoint_rightTranslateOrbit`: two different orbits are disjoint.
- `rightTranslateOrbit_mk`: the orbit of `H g` is the image of `g J` in `H\G`.
- `isOpen_rightTranslateOrbit`, `isCompact_rightTranslateOrbit`: if `J` is open
  (resp. compact) then every orbit is open (resp. compact). These hold because
  the quotient map is an open quotient map.
- `exists_finset_rightTranslateOrbit_cover`: if `J` is open and `C ⊆ H\G` is
  compact, there is a finite set `u` of points of `C` whose `J`-orbits are
  pairwise disjoint and cover `C`. The proof takes a finite subcover by orbits
  and keeps one representative for each distinct orbit.
- `integrableOn_and_setIntegral_eq_sum_rightTranslateOrbit`: let `ν` be finite
  on compact sets, `J` compact open, `S` a measurable set stable under right
  translation by `J`, and `f` a function invariant under right translation by
  `J`. Let `u` be a finite set of points of `S` with pairwise disjoint orbits
  such that every point of `S` where `f ≠ 0` lies in one of these orbits. Then
  `f` is integrable on `S`, and

  `∫_S f dν = Σ_{q ∈ u} ν(q J) · f(q)`,

  with `ν(q J)` taken as a real number. The proof writes `S.indicator f` as the
  sum of the indicators of `f` on the orbits. Each orbit is compact open, so it
  has finite measure, and `f` is constant on it.

## Integral determinants

- `ord_det_of_mem_integralSubgroup`: an element of the integral subgroup
  `GL_(r+1)(O)` has determinant of order zero. It follows from the published
  `normalizedAbs_det_of_mem_integralSubgroup`.

## The conditional slice theorem

`corank_slice_of_common_support T r` is stated for an arbitrary
`T : F.TopologicalData` with its topology, valuation and local-field
structures, and the Borel structure on the quotient
`LeftUnipotentQuotient r F.Carrier = N_(r+1)\GL_(r+1)`. The data are:

- a unitary additive character `ψ`;
- a measure `ν` on the quotient that is finite on compact sets (a compatible
  quotient measure is regular, hence qualifies);
- a representation `τ` of `GL_(r+1)` of Whittaker type for the inverse
  standard character, a functional `ℓ`, and a coefficient `Wprime` in the
  coefficient model `coefficientModel τ ℓ`;
- a family `U : ℂ → WhittakerFunctions ψ (r + 1)` of standard Whittaker
  functions on `GL_(r+2)`, right invariant under one open subgroup `K`, with
  `z ↦ (U z)(g)` analytic at every point for every `g`;
- a slice index `m`, and a compact set `C` that contains, for every `z`, the
  support of the restriction to the slice `S_m = determinantSlice T r m` of
  `corankOneIntegrand ψ |·| (U z) Wprime 0`.

The conclusion is the pair required by `CorankOneEntireSliceStatement` for this
`m`: for every `u`, the integrand at `U u` satisfies `SliceIntegrableAt T ν _ m`,
and `z ↦ sliceCoefficient T ν (corankOneIntegrand ψ |·| (U z) Wprime 0) m` is
analytic at every point. Compactness of `K` is not needed.

### Proof

1. `Wprime` is the image `modelMap τ ℓ v` of some vector `v`. Since `τ` is
   admissible, hence smooth, `v` is fixed by an open subgroup `K₁`. Put
   `J = K₁ ⊓ (rankInclusion 1)⁻¹(K) ⊓ GL_(r+1)(O)`. This is an open subgroup
   (the rank inclusion `g ↦ diag(g, 1)` is continuous), and it is compact
   because it is closed in the compact group `GL_(r+1)(O)`.
2. Every integrand is invariant under right translation by `J`. The factor
   `(U z)(diag(g, 1))` is invariant because `diag(k, 1) ∈ K`, the factor
   `Wprime(g) = ℓ(τ(g) v)` because `k` fixes `v`, and the determinant weight
   because `|det k| = 1`. The slice `S_m` is stable under `J` by
   `rightTranslate_mem_determinantSlice` and `ord_det_of_mem_integralSubgroup`.
3. `C ∩ S_m` is compact because the slice is closed. One finite set `u` of
   points of `C ∩ S_m` with pairwise disjoint `J`-orbits covering `C ∩ S_m` is
   chosen once, independent of `z`. By the support hypothesis, every point of
   `S_m` where an integrand is nonzero lies in `C ∩ S_m`.
4. The finite orbit theorem above gives, for every `z`, integrability on `S_m`
   and
   `sliceCoefficient = Σ_{q ∈ u} ν(q J) · corankOneIntegrand(U z)(q)`.
5. The orbit masses do not depend on `z`. At a coset `N g`, each point value is
   `(U z)(diag(g, 1)) · Wprime(g) · |det g|^(0 - 1/2)` (a complex power), and
   only the first factor depends on `z`, analytically.
   A finite sum of constant multiples of analytic functions is analytic
   (`Finset.analyticAt_fun_sum`).

The theorem uses only the standard axioms `propext`, `Classical.choice` and
`Quot.sound`.
