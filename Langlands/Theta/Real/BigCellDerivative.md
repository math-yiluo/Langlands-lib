# Derivatives in `L²` of the big-cell operator families (internal)

**Outside GKT.** This file belongs to the archimedean theory, which Gan–Kudla–Takeda leave out
(preface, p. iv).
There is no counterpart in the book (derivatives along the open cell). The
declarations are in the name space `Langlands.Theta.Real` (`RealMetaplecticGroup` and its name
space are in `Langlands.Theta`).

The module `Langlands.Theta.Real.BigCellDerivative` is internal to the construction of the
metaplectic group; all its declarations are in `Langlands.Theta.Real.Internal`.

## Content

`HasL2DerivAt U Q t₀`: for every Schwartz `f`, `t ↦ (U t f) ∈ L²` has derivative `(Q f) ∈ L²` at
`t₀`. A pointwise derivative with a uniform Schwartz-type bound on the difference quotients gives
such a derivative (`hasDerivAt_schwartz_to_L2`). Constants, scalar multiples and products behave as
expected. The chirps `chirp (S t)` have derivative `quadMul (S' t₀)` (multiplication by
`-πi⟨x, S' x⟩`), the dilations `dilation (B t)` the vector-field derivative
`vectorFieldDeriv (B t₀⁻¹ B')`, and `bigCellOp (A t) (B t) (C t) (c t)` the corresponding sum; at the
identity this is `quadMul C' + vectorFieldDeriv A' + 𝓕 ∘ quadMul (-B') ∘ 𝓕⁻¹ + c'`
(`hasL2DerivAt_bigCellOp`). For a family that conjugates the derived Schrödinger operators along a
smooth family of linear maps, an `L²` derivative at `0` is a weak derivative against every continuous
linear functional (`HasL2DerivAt.hasDerivAt`, through `exists_factor_through_toLp`).

## Source and licence

From <https://github.com/leanprover-community/riemann-hypothesis>, commit `f1f6d65`: `src/Development/WeilBound/ThetaLifts/Reductions/HasDerivAtSchwartzToL2.lean` and `src/Development/WeilBound/ThetaLifts/Reductions/NormExpSubLe.lean`, both whole. The repository has no licence file; the text is used with attribution, see `licenses/RiemannHypothesis/SOURCE.md`.

## Changes against the source

- Namespace `PositivityTheory.ThKR.LL` → `Langlands.Theta.Real.Internal`; the two files are merged.
- Renamed: `LD` → `HasL2DerivAt`, `mq` → `quadMul`, `vf` → `vectorFieldDeriv`, `ld_ph` →
  `hasL2DerivAt_chirp`, `ld_dil` → `hasL2DerivAt_dilation`, `ld_big` → `hasL2DerivAt_bigCellOp`.
- Proofs that relied on `simp` rewriting the source's wrapper `schwartzToL2` exclude
  `SchwartzMap.toLpCLM_apply` from the simp set.

## Declarations

None public: every declaration of the file is internal.

## Dependencies

`Langlands.Theta.Real.BigCellOperator`.
