# The real metaplectic group

**Outside GKT.** This file belongs to the archimedean theory, which Gan–Kudla–Takeda leave out
(preface, p. iv).
`RealMetaplecticGroup` is the group of pairs of GKT §2.1.2 (Lemma 2.1, p. 48) over `ℝ`, with the
`L²` and Schwartz models, cut to a double cover, and with the topology of GKT §8.1.1. The
declarations are in the name space `Langlands.Theta.Real` (`RealMetaplecticGroup` and its name
space are in `Langlands.Theta`).

The module `Langlands.Theta.Real.Metaplectic.Defs` defines `Langlands.Theta.RealMetaplecticGroup l`,
for a finite type `l` with decidable equality, with its projection `proj` to `Sp_{2l}(ℝ)`, its Weil
representation `weil` on `L²(ℝˡ)` and `weilSchwartz` on Schwartz space, and its topology.

## Content

An element is a triple `(s, U, V)`: `s ∈ Matrix.symplecticGroup l ℝ`, `U` a unitary operator of
`L²(ℝˡ)`, `V` an invertible continuous operator of `𝓢(ℝˡ, ℂ)`, such that

1. `U (f ∈ L²) = (V f) ∈ L²` for Schwartz `f` (`weil_toLp`);
2. `U ∘ schrodingerL2 w = schrodingerL2 (s w) ∘ U` (`weil_schrodingerL2`) and
   `V ∘ schrodingerDeriv w = schrodingerDeriv (s w) ∘ V` (`weilSchwartz_schrodingerDeriv`);
3. `V` is normalized on vacuum vectors (`IsNormalizedLift s V`): for every `s' ∈ Sp` and every
   vacuum vector `f` of `s'`, `(V f)(0)² · det(A - iB)(s s') = f(0)² · det(A - iB)(s')`, where
   `det (A - iB)` is `automorphyDet` and a vacuum vector of `s'` is an `f` with
   `D(s' eⱼ) f = i D(s' e_{l+j}) f` for all `j` (`IsVacuumFor`; for `s' = 1`, the Gaussian).

The group law is componentwise; by the Schur lemma (`Intertwines.exists_eq_smul`) the operators over
a given `s` form a circle, and condition 3 cuts it down to two points. The topology is induced by
`g ↦ (proj g, (f ↦ weil g f))`, with the pointwise topology on maps of `L²`. The construction
follows the analytic description of the metaplectic group as a group of unitary operators
normalizing the Heisenberg group (Weil, *Sur certains groupes d'opérateurs unitaires*, Acta Math.
111 (1964); Lion–Vergne, *The Weil representation, Maslov index and theta series*, part I; page
references to be added).

**What is proved, and what is not.** It is proved (in the files `Basic`, `BigCell`, `Covering`,
`Smooth` of this directory) that `RealMetaplecticGroup l` is a Hausdorff topological group, that
`proj` is a surjective covering map whose kernel is `{1, negOne}` with `weil negOne = -1`, that
`weil` is strongly continuous and normalizes the Schrödinger representation, that its Schwartz
vectors are smooth along smooth families, and that one-parameter subgroups of `Sp` lift with
derivative the oscillator operators. It is **not** proved that the cover does not split: that the
group is connected (for non-empty `l`) and not isomorphic to `Sp_{2l}(ℝ) × {±1}`. The name
"metaplectic group" is justified by the construction and not yet by a theorem. Also not proved:
uniqueness of the group and of `weil`, a Lie group structure, the formulas on all generators, and
the Maslov cocycle.

`bigCellSection g` is the explicit operator `bigCellOp A⁻¹ B C |det A|^{-1/2}` over
`g = [[A, B], [C, D]]` (see `Theta/Real/BigCellOperator`).

## Source and licence

From <https://github.com/leanprover-community/riemann-hypothesis>, commit `f1f6d65`: `src/Development/WeilBound/ThetaLifts/Reductions/MetaplecticDerivatives/ContinuousPair.lean`, lines 1–125 (`upperParabolic`, `loQ`, `dd`, `Ann`, `Nrm`,
`Amb`, `Mem`, `sub`, `G`, `pr`, `om`, `omS`, the topology, `sec`, `Qd`). The repository has no licence file; the text is used with attribution, see `licenses/RiemannHypothesis/SOURCE.md`.

## Changes against the source

- Namespace `PositivityTheory.ThKR.Mp` → `Langlands.Theta` and `Langlands.Theta.RealMetaplecticGroup`.
- Renamed: `G` → `RealMetaplecticGroup`, `pr` → `proj`, `om` → `weil`, `omS` → `weilSchwartz`,
  `upperParabolic` → `automorphyUpper`, `loQ` → `automorphyLower`, `dd` → `automorphyDet`, `Ann` →
  `IsVacuumFor`, `Nrm` → `IsNormalizedLift`, `Amb` → `RealMetaplecticGroup.Ambient`, `Mem` →
  `RealMetaplecticGroup.Mem` (fields `compat`, `comm_schrodingerL2`, `comm_schrodingerDeriv`,
  `isNormalizedLift`), `sub` → `RealMetaplecticGroup.subgroup`, `om_sch` → `weil_toLp`, `om_rho` →
  `weil_schrodingerL2`, `omS_dRho` → `weilSchwartz_schrodingerDeriv`, `sec` → `bigCellSection`,
  `Qd` → `Internal.bigCellSectionDeriv`.
- `Mp.Mat l`, `Mp.Sp l` are written out.
- Lines 127–170 are not taken: the eleven named propositions `MkElt … OnePar` and the assembly
  `realMetaplectic_of_forall`. Their contents are theorems about the group in the other files.
- `IsVacuumFor` and `IsNormalizedLift` are public because the theorem
  `exists_of_intertwines_of_isNormalizedLift` is stated with them; `Ambient`, `Mem`, `subgroup`,
  `mem` and `continuous_pair` belong to the construction and should not be needed by users.

## Declarations

Public declarations of the file (internal ones are in the namespace `Langlands.Theta.Real.Internal` or
`Langlands.HeisenbergGroup.Internal` and are not listed):

- def `Langlands.Theta.Real.automorphyUpper`
- def `Langlands.Theta.Real.automorphyLower`
- def `Langlands.Theta.Real.automorphyDet`
- def `Langlands.Theta.Real.IsVacuumFor`
- def `Langlands.Theta.Real.IsNormalizedLift`
- theorem `Langlands.Theta.Real.IsVacuumFor.map`
- abbrev `Langlands.Theta.RealMetaplecticGroup.Ambient`
- structure `Langlands.Theta.RealMetaplecticGroup.Mem`
- def `Langlands.Theta.RealMetaplecticGroup.subgroup`
- def `Langlands.Theta.RealMetaplecticGroup`
- instance `Langlands.Theta.RealMetaplecticGroup.instGroup` (`Group`)
- def `Langlands.Theta.RealMetaplecticGroup.proj`
- def `Langlands.Theta.RealMetaplecticGroup.weil`
- def `Langlands.Theta.RealMetaplecticGroup.weilSchwartz`
- theorem `Langlands.Theta.RealMetaplecticGroup.mem`
- theorem `Langlands.Theta.RealMetaplecticGroup.weil_toLp`
- theorem `Langlands.Theta.RealMetaplecticGroup.weil_schrodingerL2`
- theorem `Langlands.Theta.RealMetaplecticGroup.weilSchwartz_schrodingerDeriv`
- theorem `Langlands.Theta.RealMetaplecticGroup.isNormalizedLift_weilSchwartz`
- instance `Langlands.Theta.RealMetaplecticGroup.instTopologicalSpace` (`TopologicalSpace`)
- theorem `Langlands.Theta.RealMetaplecticGroup.continuous_pair`
- theorem `Langlands.Theta.RealMetaplecticGroup.continuous_proj`
- theorem `Langlands.Theta.RealMetaplecticGroup.continuous_weil`
- def `Langlands.Theta.Real.bigCellSection`

## Dependencies

`Langlands.Theta.Real.LocalLift`.
