# Values of the dual test function on lower-block representatives

Internal helper for the proof of `HighlyRamifiedGammaStabilityStatement`
(Jacquet–Shalika 1985, §4.4, formulas (4)–(9), printed page 328).

- `finiteFourier ψ T Φ ξ = Σ_{z ∈ T} Φ(z) ψ(Σ_k z_k ξ_k)` is the finite exponential sum
  that replaces the Fourier transform `Φ̂` of the source; the source integral over `z` is a
  finite sum because the Whittaker function is invariant under integral translations.
- `candidateTest ψ χ W T Φ y = χ(det y) Σ_{z ∈ T} Φ(z) W(y w n(z))` is the test function of
  formula (4) twisted by `χ`, translated by `w`; here `n(z)` is the first-row unipotent
  matrix of `TestVector`.
- `reversedLastRow h` is `ξ(h)_k = h_(last, rev k)`.
- `candidateTest_dual`: its first dual function at `diag(h,1)` is
  `χ(det(w ᵗdiag(h,1)⁻¹)) · finiteFourier ψ T Φ (ξ(h)) · W(M(h))`, with `M(h) = dualConj h`.
  The proof moves `n(z)` across `M(h)` by `whittaker_mul_firstRowUnipotent` and reads the
  phase from `dualConj_inv_succ_one`.
- `IsDualSupport f ξ`: `ξ_0` is an integral unit and the other coordinates lie in `𝔭^f`.
- `gl_one_inv_apply`, `reversedLastRow_lowerBlockPair_zero`,
  `reversedLastRow_lowerBlockPair_succ`: for `h = [[A,0],[x,c]]`, `ξ(h) = (c, rev x)`.
- `whittaker_dualConj_lowerBlockPair`: for `W` right invariant under the level-`f` subgroup,
  `W(M([[A,0],[x,c]])) = W(M(diag(A,1)))` whenever `ξ(h)` is on the dual support. The proof
  factors `h = diag(A,1) · [[I,0],[x,c]]` and applies `dualConj_lowerBlockPair_one_mem`. This
  is the source's passage from (5) to (9) under condition (8).
