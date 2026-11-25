# The metaplectic group over unipotent elements (internal)

**Outside GKT.** This file belongs to the archimedean theory, which Gan–Kudla–Takeda leave out
(preface, p. iv).
There is no counterpart in the book (derivatives along one-parameter subgroups). The
declarations are in the name space `Langlands.Theta.Real` (`RealMetaplecticGroup` and its name
space are in `Langlands.Theta`).

The module `Langlands.Theta.Real.Metaplectic.Unipotent` is internal to the construction, apart from
one public theorem.

## Content

- `automorphyDet_ne_zero` (public): for `s = [[A, B], [C, D]] ∈ Sp_{2l}(ℝ)`, `det (A - iB) ≠ 0`. The
  symplectic relation `A Bᵀ = B Aᵀ` gives `(A - iB)(Aᵀ + iBᵀ) = A Aᵀ + B Bᵀ = N Nᵀ` for the real
  `l × 2l` matrix `N = (A B)`, and `N` has a right inverse (again by the symplectic relations), so
  `N Nᵀ` is positive definite and invertible.
- For a symmetric `S`, the unipotent symplectic matrices `nn S t` and the operators
  `UU S t = 𝓕 ∘ chirp (-t S) ∘ 𝓕⁻¹`, which intertwine along `nn S t`; differentiating in `t` the
  quantities `(UU S t f)(0)²` and `det (A - iB)(nn S t · s')` for a vacuum vector `f` of `s'` gives the
  normalization of these operators (`isNormalizedLift_unipotent`), used for the big cell.

## Source and licence

From <https://github.com/leanprover-community/riemann-hypothesis>, commit `f1f6d65`: `src/Development/WeilBound/ThetaLifts/Reductions/MetaplecticDerivatives/MetaplecticUnipotentBlockSecondDiag.lean` (whole). The repository has no licence file; the text is used with attribution, see `licenses/RiemannHypothesis/SOURCE.md`.

## Changes against the source

- Namespace `PositivityTheory.ThKR.Mp` → `Langlands.Theta.Real.Internal`.
- The propositions `DdNe` and `NrmUp` are deleted; `ddNe` → `automorphyDet_ne_zero` and `nrmUp` →
  `isNormalizedLift_unipotent` are stated directly.
- `UU_zero`: the fact `0 • A = 0` for the operators is proved by extensionality (the generic
  `zero_smul` no longer unifies with this instance of `SMul`).

## Declarations

Public declarations of the file (internal ones are in the namespace `Langlands.Theta.Real.Internal` or
`Langlands.HeisenbergGroup.Internal` and are not listed):

- theorem `Langlands.Theta.Real.automorphyDet_ne_zero`

## Dependencies

`Langlands.Theta.Real.Metaplectic.Basic`.
