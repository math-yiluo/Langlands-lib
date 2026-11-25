# The Schrödinger representation of the real Heisenberg group

**Outside GKT.** This file belongs to the archimedean theory, which Gan–Kudla–Takeda leave out
(preface, p. iv).
The non-archimedean counterpart is the Schrödinger model of GKT §1.2.2 (Theorem 1.13, p. 25),
`Langlands.Theta.Heisenberg.Schrodinger`, `Langlands.LinearAlgebra.Symplectic`; `schrodingerFun_real` ties the two. The
declarations are in the name space `Langlands.Theta.Real` (`RealMetaplecticGroup` and its name
space are in `Langlands.Theta`).

The module `Langlands.Theta.Real.Schrodinger` defines `L²(ℝˡ)` and `𝓢(ℝˡ, ℂ)` for a finite index
type `l`, the standard symplectic form on `l ⊕ l → R`, the Schrödinger operators on `L²` and on
Schwartz space, and the unitary representation of the real Heisenberg group.

## Content

A vector `w ∈ ℝ^{l ⊕ l}` has a translation part `p = translationPart w` and a modulation part
`q = modulationPart w` in `EuclideanSpace ℝ l`. The standard symplectic form is
`ω(w, w') = ∑ᵢ (w (inl i) w' (inr i) - w (inr i) w' (inl i)) = -(w ⬝ᵥ J *ᵥ w')`, the form
`Langlands.stdSymplecticForm l ℝ` of `Langlands.LinearAlgebra.Symplectic`; symplectic matrices
preserve it.

`schrodingerL2 w` is the unitary operator `f ↦ (x ↦ e^{2πi⟨q, x⟩ + πi⟨p, q⟩} f(x + p))` of
`L²(ℝˡ)`: an isometry (translation and multiplication by a function of modulus one preserve the
`L²` norm), invertible with inverse a multiple of `schrodingerL2 (-w)`. The operators satisfy
`S(w) S(w') = e^{πi ω(w, w')} S(w + w')` (`schrodingerL2_comp`), and they are the general
Schrödinger operators `HeisenbergGroup.schrodingerFun` of `Langlands.Theta.Heisenberg.Schrodinger`
for the pairing `⟪·,·⟫` of `ℝˡ` with itself and the character
`fourierCharℂ t = e^{2πit}` (`coeFn_schrodingerL2`, `schrodingerFun_real`). They are strongly
continuous in `w`, and jointly continuous in `(w, f)` (`continuous_schrodingerL2`,
`continuous_schrodingerL2_uncurry`): on Schwartz functions by dominated convergence of the matrix
coefficients, in general by density and equicontinuity. `schrodingerSchwartz w` is the same
operator of Schwartz space (multiplication by a function of temperate growth after a translation),
and `schrodingerL2_toLp` compares the two.

`schrodingerUnitary : HeisenbergGroup (stdSymplecticForm l ℝ) →* (RealL2 l ≃ₗᵢ[ℂ] RealL2 l)`,
`(w, t) ↦ e^{2πit} schrodingerL2 w`, is the Schrödinger representation of the real Heisenberg group
with central character `t ↦ e^{2πit}`. Folland, *Harmonic analysis in phase space*, chapter 1;
Lion–Vergne, *The Weil representation, Maslov index and theta series*, part I (page references to
be added).

The inclusion of Schwartz space in `L²` is Mathlib's `SchwartzMap.toLpCLM`; inside the namespace
`Langlands.Theta` the scoped notation `schwartzToL2 l` stands for it.

## Source and licence

From <https://github.com/leanprover-community/riemann-hypothesis>, commit `f1f6d65`:
`src/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/RealMetaplecticRepresentation.lean`,
lines 1–119 (`L2`, `Sch`, `pPart`, `qPart`, `sympl`, `phase`, `rhoFun`, `rhoIsometry`, `rho`,
`rho_rho`, `rho_zero`); `src/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/MetaplecticRepresentation.lean`,
lines 15–50 (`eChar` and its temperate growth);
`src/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ExistsSchwartzTranslate.lean` (`rhoSch`,
`phase_eq_eChar`) and `src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ContinuousRhoApply.lean`
(`continuous_rho`), both whole. The repository has no licence file; the text is used with attribution, see `licenses/RiemannHypothesis/SOURCE.md`.

## Changes against the source

- Namespace `GlobalTheory.RealWeil` → `Langlands.Theta` (public) and `Langlands.Theta.Real.Internal`.
- Renamed: `L2` → `RealL2`, `Sch` → `RealSchwartz`, `pPart` → `translationPart`, `qPart` →
  `modulationPart`, `rho` → `schrodingerL2`, `rhoSch` → `schrodingerSchwartz`, `eChar` →
  `fourierCharℂ` (Mathlib has no complex form of `Real.fourierChar`), `continuous_rho` →
  `continuous_schrodingerL2`, `continuous_rho_prod` → `continuous_schrodingerL2_uncurry` (arguments
  swapped). Internal: `sympl`, `schrodingerPhase` (`phase`), `rhoFun`, `rhoIsometry`.
- New: the internal bridge `sympl_eq_stdSymplecticForm` to the Library's
  `Langlands.stdSymplecticForm`; `schrodingerL2_comp` is `rho_rho` restated with it; the bridge to
  `HeisenbergGroup.schrodingerFun` (`rhoFun_eq_schrodingerFun`, `schrodingerFun_real`,
  `coeFn_schrodingerL2`, `coe_schrodingerSchwartz`); `schrodingerL2_toLp`; `circleSMul`,
  `schrodingerUnitary`.
- `eLpNorm_rhoFun` and `memLp_rhoFun` are adapted to Mathlib's current `eLpNorm_congr_norm_ae` and
  `MemLp`.
- The wrapper `schwartzToL2` is replaced by the notation for `SchwartzMap.toLpCLM`.

## Declarations

Public declarations of the file (internal ones are in the namespace `Langlands.Theta.Real.Internal` or
`Langlands.HeisenbergGroup.Internal` and are not listed):

- abbrev `Langlands.Theta.Real.RealL2`
- abbrev `Langlands.Theta.Real.RealSchwartz`
- def `Langlands.Theta.Real.translationPart`
- def `Langlands.Theta.Real.modulationPart`
- theorem `Langlands.Theta.Real.translationPart_add`
- theorem `Langlands.Theta.Real.modulationPart_add`
- theorem `Langlands.Theta.Real.translationPart_smul`
- theorem `Langlands.Theta.Real.modulationPart_smul`
- theorem `Langlands.Theta.Real.translationPart_neg`
- theorem `Langlands.Theta.Real.modulationPart_neg`
- theorem `Langlands.Theta.Real.translationPart_zero`
- theorem `Langlands.Theta.Real.modulationPart_zero`
- theorem `Langlands.Theta.Real.translationPart_apply`
- theorem `Langlands.Theta.Real.modulationPart_apply`
- theorem `Langlands.Theta.Real.continuous_translationPart`
- theorem `Langlands.Theta.Real.continuous_modulationPart`
- def `Langlands.Theta.Real.fourierCharℂ`
- theorem `Langlands.Theta.Real.fourierCharℂ_apply`
- theorem `Langlands.Theta.Real.norm_fourierCharℂ`
- theorem `Langlands.Theta.Real.continuous_fourierCharℂ`
- theorem `Langlands.Theta.Real.hasTemperateGrowth_fourierCharℂ`
- def `Langlands.Theta.Real.schrodingerL2`
- theorem `Langlands.Theta.Real.schrodingerFun_real`
- theorem `Langlands.Theta.Real.coeFn_schrodingerL2`
- theorem `Langlands.Theta.Real.schrodingerL2_comp`
- theorem `Langlands.Theta.Real.schrodingerL2_zero`
- def `Langlands.Theta.Real.schrodingerSchwartz`
- theorem `Langlands.Theta.Real.coe_schrodingerSchwartz`
- theorem `Langlands.Theta.Real.schrodingerL2_toLp`
- theorem `Langlands.Theta.Real.continuous_schrodingerL2_uncurry`
- theorem `Langlands.Theta.Real.continuous_schrodingerL2`
- def `Langlands.Theta.Real.circleSMul`
- theorem `Langlands.Theta.Real.circleSMul_apply`
- def `Langlands.Theta.Real.schrodingerUnitary`
- theorem `Langlands.Theta.Real.schrodingerUnitary_apply`

## Dependencies

`Langlands.Theta.Heisenberg.Schrodinger`, `Langlands.LinearAlgebra.Symplectic`; Mathlib (Schwartz space, `L²`,
the symplectic group, temperate growth, dominated convergence).
