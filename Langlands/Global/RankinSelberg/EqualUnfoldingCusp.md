# Cusp forms, their duals and Schwartz–Bruhat functions in the equal-rank unfolding

This is an internal helper module for `EqualUnfoldingReduction.md`. Provenance: internal. It
checks that the Library's cusp forms `cuspFunction F T v`, their duals
`dualFunction F n (cuspFunction F T v)`, their Whittaker functions `cuspWhittaker F T ψ v`, and
Schwartz–Bruhat functions satisfy the hypotheses of `eisenstein_unfolding`
(`EqualUnfoldingEisenstein.md`) and `mirabolic_unfolding` (`EqualUnfoldingWhittaker.md`), apart
from the Whittaker expansion and the gauge integrability, which stay premises. Cogdell,
*Analytic theory of L-functions for GL_n* (2004), §2.3, printed pp.209–210, uses these
properties implicitly. Namespace: `Langlands.Global.RankinSelbergGlobal.EqualUnfolding`;
`n = r + 1`.

## Schwartz–Bruhat functions (`SchwartzBruhat`)

- `measurable_of_mem_schwartzBruhat`: Schwartz–Bruhat functions are measurable for the Borel
  σ-algebra on row vectors (local instances from `EqualUnfoldingSection`). By the Library's
  `EqualAnalytic.schwartzBruhat_properties`, they are continuous.
- `measurable_fourierTransform`: for standard `ψ`, the Fourier transform `Φ̂` of a
  Schwartz–Bruhat function is measurable (Library `EqualAnalytic.continuous_fourierTransform`).

## Central characters (`CentralCharacter`)

- `cuspFunction_eq_evaluate`: a cusp function is the evaluation of the continuous automorphic
  form `T.realization.toContinuous v` at the matrix of the point (through
  `GeneralLinearGroupPoints.adelicHomeomorph`).
- `cuspFunction_scalarPoint_mul`: if `T` has central character `ω`, then
  `φ(diag(a, …, a) x) = ω(a) φ(x)`. This is the Library's `centralCharacter_evaluate` for
  `T.realization`, after identifying the matrix of `scalarPoint` with the Library's
  `AdelicGL.scalar`. That identification goes through an explicit equality chain, because a
  direct rewrite times out.
- `dualConj_scalarPoint`: the twist `g ↦ w ᵗg⁻¹ w⁻¹` of the Library's `dualConj` sends `a` to
  `a⁻¹`. Hence `dualCuspFunction_scalarPoint_mul`: `φ̃(a x) = ω(a)⁻¹ φ̃(x)`.
- `centralIdeleCharacter_mul_val` and `centralIdeleCharacter_mul_inv_val`: the values of `ω ω'`
  and `(ω ω')⁻¹` on ideles.
- `cuspFunction_mul_scalarPoint_mul`: `φ(a x) φ'(a x) = (ω ω')(a) φ(x) φ'(x)`.
  `dualCuspFunction_mul_scalarPoint_mul`: `φ̃(a x) φ̃'(a x) = (ω ω')⁻¹(a) φ̃(x) φ̃'(x)`. These are
  the central-character hypotheses of `eisenstein_unfolding` for `χ = ω ω'` and for
  `χ = (ω ω')⁻¹`, the characters in the Library's `EqualUnfoldingStatement`.

## Whittaker functions (`Whittaker`)

- `cuspWhittaker_inv_eq_setIntegral`: the `ψ⁻¹`-Whittaker function `W'` of a cusp form `φ'` is
  the Library's `quotientMassNormalizer` times `∫_{n ∈ fd} φ'(n x) θ_ψ(n) dn`, over the chosen
  fundamental domain of `N_n(F)` in `N_n(𝔸)`. This is the hypothesis `hW'` of
  `mirabolic_unfolding`, with `θ_ψ = genericCharacter F r ψ (fun _ => 1)`. The proof applies the
  Library's `subgroupCharacterCoefficient_eq_setIntegral` and the identity
  `conj θ_{ψ⁻¹} = θ_ψ` (`genericCharacter_inv`).
