# Intertwiners of the real Schrödinger representation

**Outside GKT.** This file belongs to the archimedean theory, which Gan–Kudla–Takeda leave out
(preface, p. iv).
`Intertwines` is relation (2.2) of GKT p. 47 together with the `L²`-isometry, and
`Intertwines.exists_eq_smul` replaces the Schur lemma of GKT §2.1.1 over `ℝ`. The
declarations are in the name space `Langlands.Theta.Real` (`RealMetaplecticGroup` and its name
space are in `Langlands.Theta`).

The module `Langlands.Theta.Real.Intertwiner` studies the operators of Schwartz space that preserve
`L²` norms and carry the Schrödinger operators along a map of `ℝ^{l ⊕ l}`.

## Content

`Intertwines s S` (for `S : RealSchwartz l →ₗ[ℂ] RealSchwartz l`): `‖S f‖_{L²} = ‖f‖_{L²}` for all
`f` (field `norm_toLp`) and `S ∘ schrodingerSchwartz w = schrodingerSchwartz (s w) ∘ S` (field
`comm`). Such an `S` preserves inner products (`Intertwines.inner`, by polarization). If `S` is
surjective:

- for linear `s`, `S` intertwines the derived operators,
  `S (schrodingerDeriv w f) = schrodingerDeriv (s w) (S f)` (`Intertwines.comm_schrodingerDeriv`):
  differentiate `t ↦ ⟪S φ, S(S(t w) f)⟫ = ⟪φ, S(t w) f⟫` at `0`;
- for invertible linear `s`, `S` is continuous for the Schwartz topology
  (`Intertwines.continuous`): `S` conjugates the Weyl algebra into itself, so each seminorm of `S f`
  is bounded by `L²` norms of `S (A' f)`, equal to `L²` norms of `A' f`;
- for `s = id`, `S` is a scalar (`Intertwines.exists_eq_smul`): the matrix coefficients
  `⟪φ, ρ(0, q) f⟫` are the Fourier transform of `φ̄ f` at `-q`, so `S φ̄ · S f = φ̄ f` pointwise by
  Fourier inversion; `S` is multiplication by a function, which commutes with the translations
  `ρ(p, 0)` only if it is constant. This is the Schur half of the real Stone–von Neumann theorem on
  Schwartz space, which is what the metaplectic group needs; the full theorem on `L²` is not
  proved here.

`oscillatorDeriv_mem_weylAlgebra`: the oscillator operators lie in the Weyl algebra.

## Source and licence

From <https://github.com/leanprover-community/riemann-hypothesis>, commit `f1f6d65`: `src/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IteratedLineDerivMemWeylAlg.lean`, lines 246–292 (`hasDerivAt_rhoFun_at`, `inner_toLp_rho`,
`hasDerivAt_inner_rho`), and `src/Development/WeilBound/ThetaLifts/CartanFactorisation/EqOfInner.lean`, lines 61–206 (`Impl`, `Impl.inner`, `exists_rho`, `toLp_rho`,
`eq_of_inner`, `Impl.dRho`, `Impl.continuous`, `exists_ne_zero`, `Impl.scalar`, `quad_mem`). The repository has no licence file; the text is used with attribution, see `licenses/RiemannHypothesis/SOURCE.md`.

## Changes against the source

- Namespace `PositivityTheory.ThKF.E` and `GlobalTheory.RealWeil` → `Langlands.Theta`; auxiliary
  lemmas in `Langlands.Theta.Real.Internal`.
- `Impl` → `Intertwines`, fields `norm` → `norm_toLp`, `impl` → `comm`; the field `comm` is stated
  with the public operators `schrodingerSchwartz` (the source stated it with the internal `rhoFun`);
  the source form is the theorem `Intertwines.comm_rhoFun`, and `Intertwines.of_rhoFun` builds an
  `Intertwines` from it.
- `Impl.dRho` → `Intertwines.comm_schrodingerDeriv`, `Impl.scalar` → `Intertwines.exists_eq_smul`,
  `quad_mem` → `oscillatorDeriv_mem_weylAlgebra`; `exists_rho` → `Internal.exists_schwartz_eq_rhoFun`.
- `sympl_eq` (line 208) is in `Theta/Real/SchrodingerDeriv`; `exists_exp` (lines 12–59) is
  `Langlands.exists_exp_smul_of_continuous_oneParameter` in `Langlands/Analysis/OneParameterSubgroup`;
  `exists_lift` and `lie` (lines 212–319) are in `Theta/Real/Metaplectic/Smooth`.

## Declarations

Public declarations of the file (internal ones are in the namespace `Langlands.Theta.Real.Internal` or
`Langlands.HeisenbergGroup.Internal` and are not listed):

- structure `Langlands.Theta.Real.Intertwines`
- theorem `Langlands.Theta.Real.Intertwines.comm_rhoFun`
- theorem `Langlands.Theta.Real.Intertwines.of_rhoFun`
- theorem `Langlands.Theta.Real.Intertwines.inner`
- theorem `Langlands.Theta.Real.Intertwines.comm_schrodingerDeriv`
- theorem `Langlands.Theta.Real.Intertwines.continuous`
- theorem `Langlands.Theta.Real.Intertwines.exists_eq_smul`
- theorem `Langlands.Theta.Real.oscillatorDeriv_mem_weylAlgebra`

## Dependencies

`Langlands.Theta.Real.WeylAlgebra`, `Langlands.Analysis.OneParameterSubgroup`.
