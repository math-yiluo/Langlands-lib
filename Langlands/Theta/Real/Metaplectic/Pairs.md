# The real metaplectic group in the group of pairs

**Outside GKT.** This file belongs to the archimedean theory, which Gan–Kudla–Takeda leave out
(preface, p. iv). It applies the construction of GKT §2.1.2 (Lemma 2.1, p. 48: the pairs `(g, M)`
with the relation (2.2), p. 47; `Mp(W)^{ℂ¹}`, p. 49), formalized for any model in
`Langlands.Theta.Metaplectic.Defs`, to the Schwartz model over `ℝ`. The declarations are in the
name space `Langlands.Theta.Real` (`RealMetaplecticGroup` and its name space are in
`Langlands.Theta`).

The module `Langlands.Theta.Real.Metaplectic.Pairs` identifies `RealMetaplecticGroup l` with a
subgroup of the metaplectic group of pairs `MetaplecticGroup ρ` of the Schrödinger representation
`ρ` on `𝓢(ℝˡ, ℂ)`, so that both branches state "the Weil representation is the second projection
of a group of pairs normalizing the Heisenberg representation" with the same `MetaplecticGroup`,
`proj` and `weil`.

## Content

- `Real.schrodingerSchwartzRep l : Representation ℂ (HeisenbergGroup (stdSymplecticForm l ℝ))
  (RealSchwartz l)`: `(w, t)` acts by `e^{2πit} schrodingerSchwartz w`
  (`schrodingerSchwartzRep_apply`). It is a representation because its operators are those of the
  unitary representation `schrodingerUnitary` on `L²(ℝˡ)` restricted to Schwartz functions
  (`toLp_schrodingerSchwartzRep`), and `f ↦ f ∈ L²` is injective on Schwartz space
  (`SchwartzMap.injective_toLp`).
- `Real.schwartzL2Inner l`: the `L²` inner product `(f, f') ↦ ⟪f, f'⟫_{L²}` on Schwartz space, a
  sesquilinear form (`schwartzL2Inner_apply`).
- `RealMetaplecticGroup.toPairs : RealMetaplecticGroup l →* MetaplecticGroup (schrodingerSchwartzRep l)`,
  `(s, U, V) ↦ (s, V)` with `s` read as an isometry of `stdSymplecticForm l ℝ` through
  `Matrix.symplecticGroup.toIsometryGroup` (`proj_toPairs`) and `V` as a linear automorphism
  (`weil_toPairs`: `MetaplecticGroup.weil _ (toPairs g) = weilSchwartz g`). The relation (2.2) for
  `(s, V)` follows from the relation for `(s, U)` on `L²` (`weil_schrodingerL2`) and `U f = V f` on
  Schwartz functions (`weil_toLp`).
- `RealMetaplecticGroup.toPairs_injective`: an element is determined by its symplectic matrix and its
  operator of Schwartz space (`RealMetaplecticGroup.ext`, by density of Schwartz space in `L²`).
- `RealMetaplecticGroup.toPairs_mem_unitary`: the image is in `MetaplecticGroup.unitary _
  (schwartzL2Inner l)`, the pairs whose operator preserves the `L²` inner product (the analogue of
  `Mp(W)^{ℂ¹}`).

Over `ℝ` the algebraic pairs group is only an ambient: Schur's lemma of the real branch
(`Real.Intertwines.exists_eq_smul`) is proved for `L²`-isometric intertwiners, and
`RealMetaplecticGroup l` is the subgroup of unitary pairs normalized on vacuum vectors
(`Real.IsNormalizedLift`); `toPairs` is a theorem about it, not its definition.

## Declarations

- `Langlands.Theta.Real.schrodingerSchwartzRep`, `schrodingerSchwartzRep_apply`,
  `toLp_schrodingerSchwartzRep`, `schwartzL2Inner`, `schwartzL2Inner_apply`.
- `Langlands.Theta.RealMetaplecticGroup.toPairs`, `proj_toPairs`, `weil_toPairs`,
  `toPairs_injective`, `toPairs_mem_unitary`.

## Dependencies

`Langlands.Theta.Real.Metaplectic.Basic` (`RealMetaplecticGroup.ext`, and through it
`Langlands.Theta.Real.Metaplectic.Defs`, `Langlands.Theta.Real.Schrodinger`),
`Langlands.Theta.Metaplectic.Defs`.
