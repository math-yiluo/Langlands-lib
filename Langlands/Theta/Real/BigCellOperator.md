# The operators of the big cell

**Outside GKT.** This file belongs to the archimedean theory, which Gan–Kudla–Takeda leave out
(preface, p. iv).
`bigCellOp` is the analogue on the open cell of the standard Weil operator `r(g)` of GKT
Definition 2.9 (p. 54). The
declarations are in the name space `Langlands.Theta.Real` (`RealMetaplecticGroup` and its name
space are in `Langlands.Theta`).

The module `Langlands.Theta.Real.BigCellOperator` defines the explicit operators of Schwartz space
from which the metaplectic group is built over the big cell `det A ≠ 0` of `Sp_{2l}(ℝ)`.

## Content

- `chirp S f = e^{-πi⟨x, S x⟩} f` for `S : ℝˡ →L ℝˡ`; `chirp S ∘ chirp T = chirp (S + T)`.
- `dilation B f = f ∘ B` for invertible `B` (and `0` otherwise); `dilation A ∘ dilation B = dilation (B A)`.
- Mathlib's Fourier transform `fourierCLM ℂ (RealSchwartz l)` and its inverse.
- `bigCellOp Ai B C c = chirp (C Ai) ∘ (c • dilation Ai) ∘ 𝓕 ∘ chirp (-(Ai B)) ∘ 𝓕⁻¹`.

All of them are invertible. In the internal part each is shown to preserve the `L²` norm (for
`c² = |det Ai|` in the case of `bigCellOp`; Plancherel for `𝓕`) and to carry the Schrödinger
operator at `(p, q)` to that at an explicit `(p', q')` (`Internal.IntertwinesAt`): the chirp to
`(p, q + S p)` for symmetric `S`, the dilation to `(B⁻¹ p, Bᵀ q)`, the Fourier transform to
`(-q, p)`. Composing, for `g = [[A, B], [C, D]]` symplectic with `A` invertible,
`bigCellOp A⁻¹ B C |det A|^{-1/2}` carries `(p, q)` to `g (p, q)`
(`Internal.intertwinesAt_bigCellOp`): these are the classical metaplectic operators on the big cell
(G. B. Folland, *Harmonic analysis in phase space* (1989), chapter 4, §4, Theorem (4.51), p. 191,
proved on p. 192 from the factorization of Proposition (4.9) and the operators (4.24)–(4.26) of §2,
p. 179). Folland's operator carries the factor `det^{-1/2} A`, which fixes a phase; the intertwining
property does not see the phase, and here only the modulus `|det A|^{-1/2}` is used.

The file also declares the instance `instHasSummableGeomSeriesEuclidean` for the operators of
`EuclideanSpace ℝ l`: Mathlib finds it by itself, but the search exceeds the default limit of the
instance search; the instance gives the same proof directly.

## Source and licence

From <https://github.com/leanprover-community/riemann-hypothesis>, commit `f1f6d65`: `src/Development/WeilBound/ThetaLifts/Reductions/IsoOfIntegral.lean` (whole: `Eu`, `rf`, `Intw`, `Iso`, `ph`, `dil`, `fou`,
`fouInv`, `big` and their lemmas). The repository has no licence file; the text is used with attribution, see `licenses/RiemannHypothesis/SOURCE.md`.

## Changes against the source

- Namespace `PositivityTheory.ThKR.LL` → `Langlands.Theta` (`chirp`, `dilation`, `bigCellOp` and their
  algebraic lemmas) and `Langlands.Theta.Real.Internal` (the rest).
- Renamed: `ph` → `chirp`, `dil` → `dilation`, `big` → `bigCellOp`, `Intw` → `IntertwinesAt`, `Iso` →
  `IsL2Isometry`; the lemma names follow (`iso_ph` → `isL2Isometry_chirp`, `intw_big` →
  `intertwinesAt_bigCellOp`, …).
- The wrappers `fou l`, `fouInv l` and their `rfl` lemmas are removed: Mathlib's `fourierCLM`,
  `fourierInvCLM` and `fourierCLM_apply`, `fourierInvCLM_apply` are used; `Eu l` is written out as
  `EuclideanSpace ℝ l`.
- New: the shortcut instance `instHasSummableGeomSeriesEuclidean` (see above); `dif_pos` replaced by
  `dite_eq_left`.

## Declarations

Public declarations of the file (internal ones are in the namespace `Langlands.Theta.Real.Internal` or
`Langlands.HeisenbergGroup.Internal` and are not listed):

- instance `Langlands.Theta.Real.instHasSummableGeomSeriesEuclidean`
- def `Langlands.Theta.Real.chirp`
- theorem `Langlands.Theta.Real.chirp_apply`
- theorem `Langlands.Theta.Real.chirp_mul`
- theorem `Langlands.Theta.Real.chirp_zero`
- theorem `Langlands.Theta.Real.isUnit_chirp`
- def `Langlands.Theta.Real.dilation`
- theorem `Langlands.Theta.Real.dilation_apply`
- theorem `Langlands.Theta.Real.dilation_one`
- theorem `Langlands.Theta.Real.dilation_mul`
- theorem `Langlands.Theta.Real.isUnit_dilation`
- def `Langlands.Theta.Real.bigCellOp`
- theorem `Langlands.Theta.Real.isUnit_bigCellOp`
- theorem `Langlands.Theta.Real.bigCellOp_one`

## Dependencies

`Langlands.Theta.Real.Intertwiner`; Mathlib (`InnerProductSpace.NormDet`).
