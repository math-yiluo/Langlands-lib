# Smearing along the last lower row

Internal helper for the proof of `HighlyRamifiedGammaStabilityStatement`
(Jacquet–Shalika 1985, §4.4, the function `F` of formula (10), printed page 328).

- `lowerRow x` is `ū_x = [[I,0],[x,1]]` in `GL_(m+2)`, for a row `x ∈ F^(1 × (m+1))`
  (the published lower-block representative with `A = 1` and last entry `1`).
  `lowerRow_add`, `lowerRow_zero`: it is additive in `x`.
  `lowerBlockPair_one_eq_mul_lowerRow`: `[[A,0],[x,1]] = diag(A,1) · ū_x`.
- `continuous_lowerRow`, `lowerRow_orbit_locallyConstant`: for a smooth representation the
  orbit map `x ↦ ρ(ū_x) v` is locally constant (published `Hecke.orbitMap_locallyConstant`).
- `lowerRowSmear μ ρ hρ S hS hSc v` is the vector `∫ S(x) ρ(ū_x) v dμ(x)` for a locally
  constant, compactly supported weight `S`. It is the published finite algebraic integral
  (`AlgebraicIntegral.integral`) of the finite-image function
  `x ↦ S(x) • ρ(ū_x) v` (`compactlySupportedSimpleFunc`); no topology on the carrier is used.
- `lowerRowSmear_dual`: every linear functional `L` gives
  `L(∫ S(x) ρ(ū_x) v) = ∫ S(x) L(ρ(ū_x) v) dμ(x)` for a measure finite on compact sets,
  by the published `integral_linearMap` and `integral_eq_bochner`.

Applied to the second dual model, this exhibits the source's `x`-integral of the dual test
function as the Whittaker function of an actual vector.
