# The real metaplectic group: elements, topology, kernel

**Outside GKT.** This file belongs to the archimedean theory, which Gan–Kudla–Takeda leave out
(preface, p. iv).
The kernel `{1, negOne}` of `proj` is the counterpart of "`Mp(W)^{(2)}` is a double cover"
(GKT §5.2). The
declarations are in the name space `Langlands.Theta.Real` (`RealMetaplecticGroup` and its name
space are in `Langlands.Theta`).

The module `Langlands.Theta.Real.Metaplectic.Basic` proves the basic structure of
`RealMetaplecticGroup l`.

## Content

- `RealMetaplecticGroup.ext`: an element is determined by `proj g` and `weilSchwartz g` (the operator
  of `L²` is determined by density of Schwartz space).
- `RealMetaplecticGroup.exists_of_intertwines_of_isNormalizedLift`: every invertible `U` on Schwartz
  space that preserves `L²` norms, intertwines the Schrödinger operators along `s ∈ Sp` and is
  normalized on vacuum vectors is `weilSchwartz g` for some `g` over `s`; the unitary operator is the
  extension of `U` by continuity (`LinearEquiv.extendOfIsometry`).
- `IsTopologicalGroup (RealMetaplecticGroup l)` and `RealMetaplecticGroup.continuous_weil_uncurry`
  (joint continuity of the action on `L²`), from the continuity of the components and the
  isometry of the operators.
- `RealMetaplecticGroup.weilCLM`: `weil` as a homomorphism to the bounded operators `RealL2 l →L[ℂ]
  RealL2 l`, the form a representation has in `Langlands.Archimedean`
  (`Langlands/Representation/Archimedean/SmoothVectors`); `isContinuousRepresentation_weilCLM` is
  `continuous_weil_uncurry` read as `Archimedean.IsContinuousRepresentation`. The Library's smooth
  vectors (`Archimedean.IsSmoothVector`) need a manifold structure on the group, which
  `RealMetaplecticGroup l` does not have yet; smoothness on Schwartz vectors is stated along smooth
  families instead (`contDiff_weil_comp`, in `Smooth`).
- `RealMetaplecticGroup.negOne = (1, -1, -1)`, `weil_negOne`, `proj_negOne`, `negOne_ne_one`, and
  `proj_eq_one_iff`: an element over the identity has a scalar Schwartz operator `c` (Schur), and the
  normalization on the Gaussian vacuum vector gives `c² = 1`. `card_ker_proj`: the kernel has two
  elements.
- `gaussianVector l`: the Gaussian `x ↦ e^{-π‖x‖²}` (the Library's `radialGaussian` of
  `Langlands/Analysis/SchwartzGaussian`, rescaled by `√π`), a vacuum vector of the identity
  (`isVacuumFor_one_gaussianVector`) with `gaussianVector l 0 = 1`.

## Source and licence

From <https://github.com/leanprover-community/riemann-hypothesis>, commit `f1f6d65`: `src/Development/WeilBound/ThetaLifts/Reductions/MetaplecticDerivatives/ContinuousTo.lean` (whole: `MpA.dense_sch`, `MpA.ext`, `MpA.G_ext`, `continuous_to`,
`om_cont2`, `gs`, `ann_gs`, `eps` and its lemmas, `mkElt`, `topG`, `ker`). The repository has no licence file; the text is used with attribution, see `licenses/RiemannHypothesis/SOURCE.md`.

## Changes against the source

- Namespaces `PositivityTheory.ThKR.Mp`, `…Mp.MpA` → `Langlands.Theta.RealMetaplecticGroup` and its
  `Internal` namespace.
- The named propositions are replaced by theorems: `mkElt : MkElt l` →
  `exists_of_intertwines_of_isNormalizedLift` (stated for given `s`, `U`), `topG : TopG l` → an
  instance, `ker : Ker l` → `proj_eq_one_iff` together with `negOne`, `negOne_ne_one`, `weil_negOne`.
- `G_ext` (which needed all three components) is kept internal as `ext_of_weil`; the public `ext`
  needs only `proj` and `weilSchwartz`.
- Renamed: `eps` → `negOne`, `om_eps` → `weil_negOne`, `pr_eps` → `proj_negOne`, `eps_ne` →
  `negOne_ne_one`, `om_cont2` → `continuous_weil_uncurry`, `gs` → `gaussianVector`, `ann_gs` →
  `isVacuumFor_one_gaussianVector`, `gs_zero` → `gaussianVector_zero`, `dd_one` → `automorphyDet_one`.
- The source's `gaussianSchwartz` (`src/GroundTheory/GlobalFields/TateThesis/GaussianSchwartz.lean`)
  is not taken: `gaussianVector` is built from the Library's `radialGaussian` (`gaussianVector_apply`).
- New: `card_ker_proj`, `weilCLM`, `isContinuousRepresentation_weilCLM`.

## Declarations

Public declarations of the file (internal ones are in the namespace `Langlands.Theta.Real.Internal` or
`Langlands.HeisenbergGroup.Internal` and are not listed):

- def `Langlands.Theta.Real.gaussianVector`
- theorem `Langlands.Theta.Real.gaussianVector_apply`
- theorem `Langlands.Theta.Real.fderiv_gaussianVector`
- theorem `Langlands.Theta.Real.isVacuumFor_one_gaussianVector`
- theorem `Langlands.Theta.Real.gaussianVector_zero`
- theorem `Langlands.Theta.Real.automorphyDet_one`
- theorem `Langlands.Theta.RealMetaplecticGroup.negOne_mem`
- def `Langlands.Theta.RealMetaplecticGroup.negOne`
- theorem `Langlands.Theta.RealMetaplecticGroup.weil_negOne`
- theorem `Langlands.Theta.RealMetaplecticGroup.weilSchwartz_negOne`
- theorem `Langlands.Theta.RealMetaplecticGroup.proj_negOne`
- theorem `Langlands.Theta.RealMetaplecticGroup.negOne_ne_one`
- theorem `Langlands.Theta.RealMetaplecticGroup.weil_eq_smul_of_weilSchwartz`
- theorem `Langlands.Theta.RealMetaplecticGroup.ext`
- theorem `Langlands.Theta.RealMetaplecticGroup.continuous_weil_uncurry`
- def `Langlands.Theta.RealMetaplecticGroup.weilCLM`
- theorem `Langlands.Theta.RealMetaplecticGroup.weilCLM_apply`
- theorem `Langlands.Theta.RealMetaplecticGroup.isContinuousRepresentation_weilCLM`
- theorem `Langlands.Theta.RealMetaplecticGroup.exists_of_intertwines_of_isNormalizedLift`
- instance `Langlands.Theta.RealMetaplecticGroup.instIsTopologicalGroup` (`IsTopologicalGroup`)
- theorem `Langlands.Theta.RealMetaplecticGroup.proj_eq_one_iff`
- theorem `Langlands.Theta.RealMetaplecticGroup.card_ker_proj`

## Dependencies

`Langlands.Theta.Real.Metaplectic.Defs`, `Langlands.Analysis.SchwartzGaussian`,
`Langlands.Representation.Archimedean.SmoothVectors`.
