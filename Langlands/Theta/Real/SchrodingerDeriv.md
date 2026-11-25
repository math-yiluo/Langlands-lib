# The derived Schrödinger representation and the oscillator representation of `sp`

**Outside GKT.** This file belongs to the archimedean theory, which Gan–Kudla–Takeda leave out
(preface, p. iv).
There is no counterpart over a nonarchimedean field (the Heisenberg Lie algebra). The
declarations are in the name space `Langlands.Theta.Real` (`RealMetaplecticGroup` and its name
space are in `Langlands.Theta`).

The module `Langlands.Theta.Real.SchrodingerDeriv` defines the operators of the Heisenberg Lie
algebra and of the symplectic Lie algebra on Schwartz space and proves their commutation relations.

## Content

For `w = (p, q)`, `schrodingerDeriv w f = ∂_p f + 2πi⟨q, ·⟩ f`; it is the derivative at `t = 0` of
`t ↦ rhoFun (t • w) f` pointwise (internal `hasDerivAt_rhoFun`), it is real-linear in `w`, and the
canonical commutation relations hold:
`[D(w), D(w')] = 2πi ω(w, w')` (`schrodingerDeriv_commutator`, by the symmetry of second
derivatives). On the standard basis, `D(e_{inl j}) = ∂ⱼ` and `D(e_{inr k}) = 2πi xₖ`.

For a matrix `X`, `oscillatorDeriv X = (4πi)⁻¹ ∑ₐ,ᵦ (XJ)ₐᵦ / 2 · (Dₐ Dᵦ + Dᵦ Dₐ)`. For `X ∈ sp`
(`XJ` is then symmetric) it satisfies `[oscillatorDeriv X, D(w)] = D(X w)`
(`oscillatorDeriv_commutator`), so that `X ↦ oscillatorDeriv X` is the infinitesimal oscillator
(metaplectic) representation; explicitly, for `X = [[A, B], [C, D]]`,
`oscillatorDeriv X f = (4πi)⁻¹ ∑ B_{jk} ∂ⱼ∂ₖ f - ∑ A_{jk} xₖ ∂ⱼ f - (tr A / 2) f - πi ∑ C_{jk} xⱼ xₖ f`
(`oscillatorDeriv_fromBlocks_apply`). G. B. Folland, *Harmonic analysis in phase space* (1989),
chapter 1, §3, p. 21 (`dρ(p, q, t) = 2πi(pD + qX + tI)` with `D = (2πi)⁻¹ ∂` (Prologue, p. 3), a Lie
algebra homomorphism for the bracket (1.15) of the Heisenberg Lie algebra, p. 18), and chapter 4,
§3, Proposition (4.43), formula (4.44) and Theorem (4.45), p. 186 (`2πi P_A(D, X)`, the explicit
operator above, is the infinitesimal metaplectic representation). That `X ↦ oscillatorDeriv X` is linear and a Lie algebra
homomorphism on `sp` is not proved here.

## Source and licence

From <https://github.com/leanprover-community/riemann-hypothesis>, commit `f1f6d65`: `src/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/RealMetaplecticRepresentation.lean`, lines 121–345 (`dRho`, `dRho_comm`, `quad`, `quad_comm`, `quad_fromBlocks` and
their lemmas). The repository has no licence file; the text is used with attribution, see `licenses/RiemannHypothesis/SOURCE.md`.

## Changes against the source

- Namespace `GlobalTheory.RealWeil` → `Langlands.Theta`; internal lemmas (`hasDerivAt_rhoFun`,
  `mul_J_symm`, `sympl_single`, the source's `dRho_comm` as `schrodingerDeriv_comm_sympl`) in
  `Langlands.Theta.Real.Internal`.
- Renamed: `dRho` → `schrodingerDeriv`, `quad` → `oscillatorDeriv`, `quad_comm` →
  `oscillatorDeriv_commutator`, `quad_fromBlocks` → `oscillatorDeriv_fromBlocks_apply`,
  `dRho_eq_sum` → `schrodingerDeriv_eq_sum`.
- New: `schrodingerDeriv_commutator`, the commutation relation stated with `stdSymplecticForm`;
  `Internal.sympl_eq` (the source's `sympl_eq` of `EqOfInner.lean`, line 208, proved from the bridge).

## Declarations

Public declarations of the file (internal ones are in the namespace `Langlands.Theta.Real.Internal` or
`Langlands.HeisenbergGroup.Internal` and are not listed):

- def `Langlands.Theta.Real.schrodingerDeriv`
- theorem `Langlands.Theta.Real.schrodingerDeriv_apply`
- theorem `Langlands.Theta.Real.schrodingerDeriv_add`
- theorem `Langlands.Theta.Real.schrodingerDeriv_smul`
- theorem `Langlands.Theta.Real.schrodingerDeriv_commutator`
- def `Langlands.Theta.Real.oscillatorDeriv`
- theorem `Langlands.Theta.Real.schrodingerDeriv_eq_sum`
- theorem `Langlands.Theta.Real.oscillatorDeriv_commutator`
- theorem `Langlands.Theta.Real.schrodingerDeriv_single_inl`
- theorem `Langlands.Theta.Real.schrodingerDeriv_single_inr`
- theorem `Langlands.Theta.Real.oscillatorDeriv_fromBlocks_apply`

## Dependencies

`Langlands.Theta.Real.Schrodinger`.
