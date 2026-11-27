# Decay of the difference of two nested constant terms

Module `Langlands.Global.AdelicUniformTemperednessDecay`, namespace
`Langlands.Global.StandardParabolicFamily`.

Let `𝓕` be a standard parabolic family, `J` a standard index, `α` a simple root and `g` a
continuous left `G(F)`-invariant function (`ContinuousRationalFunctions F G`).

## Definitions

- `constantTermStep J α φ = C_J φ - C_{J ∖ α} φ`, where `C_Q = 𝓕.constantTerm Q` and
  `J ∖ α = 𝓕.removeSimpleRoot J α`.

## Results

- `constantTerm_minimalParabolic_invariant`: every constant term `C_Q g` is left invariant under
  the rational points of the minimal standard parabolic `P_∅`. These points normalize the
  radical `U_Q` (`StandardLeviIntersection.conj_mem_standardUnipotent`), and
  `normalizedConstantTerm_rationalNormalizer_mul` applies.
- `integrable_radical_integrand`: a continuous function invariant under `U_Q(F)` has an
  integrable constant-term integrand on the compact quotient `U_Q(F) \ U_Q(𝔸)`.
- `constantTermStep_rational_mul`: the step is invariant under the rational points of the
  radical of the maximal parabolic `P_{Δ ∖ α}` (`omitSimpleRoot α`). Those points lie in
  `P_∅(F)` (`radical_rationalImage_le_minimalParabolic`).
- `constantTerm_constantTermStep`: the constant term of the step along `P_{Δ ∖ α}` vanishes.
  By `constantTerm_constantTerm`, `C_{Δ∖α} C_J g = C_{J ∖ α} g` and
  `C_{Δ∖α} C_{J∖α} g = C_{J∖α} g`, and the integral is linear on integrable integrands.
- `constantTerm_mul_ofFinite`: right invariance under a finite-adelic subgroup passes to
  constant terms. Continuity of the constant terms of `g` is the Library's
  `StandardParabolicFamily.continuous_constantTerm` (module
  `Langlands.Global.AdelicLeviConstantTermPairing`).
- `exists_constantTermStep_decay` (**decay**, Mœglin–Waldspurger I.2.10): fix a simple root `α`,
  compact sets `K ⊆ G(𝔸)` and `Y_f ⊆ G(𝔸_f)`, an open subgroup `L`, a threshold `b` and `n`.
  There are a compact `K' ⊇ K` and `C ≥ 0` with the following property. Let `g` be a continuous
  left `G(F)`-invariant function (`ContinuousRationalFunctions`), smooth on the archimedean slices
  and right `L`-invariant. Let `a` lie in the weak simple-root chamber of threshold `b`, let
  `k ∈ K` with `finite(a k) ∈ Y_f`, and let `M ≥ 0` bound the derivatives of order `n` of the
  step at the points `a k'`, `k' ∈ K'` with the same finite coordinate as `k`. Then
  `‖(C_J g - C_{J∖α} g)(a k)‖ ≤ C |α(a)|^{-n/[F:ℚ]} M`.

## Proof of the decay

The step is continuous, smooth on archimedean slices (`adelicUnipotentConstantTermDifferentiation`
for both constant terms), right `L`-invariant and left invariant under the rational points of
`U_{Δ∖α}`. Its constant term along `U_{Δ∖α}` vanishes. The bound is then the Library's
`adelicMaximalUnipotentDecay`, applied to the radical of `P_{Δ ∖ α}` with compact set `{1}` of
left factors. Its smoothness, connectedness and unipotence come from
`isGeometricUnipotentRadical`, and its range is the standard unipotent subgroup by
`range_radical_eq_standardUnipotent`.

## Source

Mœglin–Waldspurger, *Spectral decomposition and Eisenstein series* (1995), registered as
`moeglin-waldspurger-1995-spectral-decomposition`: I.2.10, printed pp.30–34, bounds the
difference between a function and its constant term along a proper maximal parabolic by an
arbitrary inverse power of the omitted simple root, given bounds for its derivatives. The decay
estimate here is that estimate, applied to the step, whose constant term along the maximal
parabolic `P_{Δ ∖ α}` vanishes. In Mœglin–Waldspurger the estimate feeds the rapid decay of the
alternating sum of constant terms (I.2.11–I.2.12, printed pp.34–35), which the proof of
Lemma I.4.1 (printed pp.49–51) uses through its function (4) on p.50. The use of the estimate for
the nested differences `C_J g − C_{J ∖ α} g`, one root at a time, belongs to the induction in
`Langlands.Global.AdelicUniformTemperednessInduction`, which replaces that alternating sum.
