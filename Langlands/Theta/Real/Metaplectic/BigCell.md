# The metaplectic group over the big cell

**Outside GKT.** This file belongs to the archimedean theory, which Gan–Kudla–Takeda leave out
(preface, p. iv).
`bigCellSection` is the analogue of the section `r` on a Bruhat cell (GKT §2.3, §8.1). The
declarations are in the name space `Langlands.Theta.Real` (`RealMetaplecticGroup` and its name
space are in `Langlands.Theta`).

The module `Langlands.Theta.Real.Metaplectic.BigCell` constructs elements over the big cell and
proves that `proj` is surjective.

## Content

- `RealMetaplecticGroup.exists_weilSchwartz_eq_smul_bigCellSection`: for `s ∈ Sp_{2l}(ℝ)` with
  `det A ≠ 0` there are `g` over `s` and `c` with `weilSchwartz g = c • bigCellSection s`, and `c = 1`
  when `det A > 0`. A unit scalar `z` is chosen so that `z • bigCellSection s` is normalized on
  vacuum vectors (the identity `det (A - iB)(s s') = det A · det((A⁻¹ B)…)` reduces this to the unipotent
  case of `Theta/Real/Metaplectic/Unipotent`); then `exists_of_intertwines_of_isNormalizedLift`
  applies.
- `RealMetaplecticGroup.proj_surjective`: for `s ∈ Sp`, `det (A + t B) ≠ 0` for some `t` because
  `det (A - iB) ≠ 0`; so `s · [[1, 0], [t, 1]]` and `[[1, 0], [-t, 1]]` are in the big cell.

The exact operator for `det A < 0` (an eighth root of unity) is not determined here.

## Source and licence

From <https://github.com/leanprover-community/riemann-hypothesis>, commit `f1f6d65`: `src/Development/WeilBound/ThetaLifts/Reductions/MetaplecticDerivatives/MapOfRealMul.lean` (whole). The repository has no licence file; the text is used with attribution, see `licenses/RiemannHypothesis/SOURCE.md`.

## Changes against the source

- Namespaces `PositivityTheory.ThKR.Mp`, `…Mp.C` → `Langlands.Theta` (the two theorems) and
  `Langlands.Theta.Real.Internal` (the lemmas).
- `secEx_of (h1 : MkElt l) (h2 : NrmUp l) : SecEx l` and `surj_of (h1 : DdNe l) (h2 : SecEx l) :
  Surj l` are restated without the named propositions: the hypotheses are the theorems
  `exists_of_intertwines_of_isNormalizedLift`, `isNormalizedLift_unipotent`,
  `automorphyDet_ne_zero` and `exists_weilSchwartz_eq_smul_bigCellSection`.

## Declarations

Public declarations of the file (internal ones are in the namespace `Langlands.Theta.Real.Internal` or
`Langlands.HeisenbergGroup.Internal` and are not listed):

- theorem `Langlands.Theta.RealMetaplecticGroup.exists_weilSchwartz_eq_smul_bigCellSection`
- theorem `Langlands.Theta.RealMetaplecticGroup.proj_surjective`

## Dependencies

`Langlands.Theta.Real.Metaplectic.Unipotent`.
