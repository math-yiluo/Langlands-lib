# The Schrödinger model of the unitary dual pair

**GKT §12.4.1** (the Schrödinger model `C_c^∞(𝕏^*)` of a Type I pair with `W` split, p. 369) in
Case `3₊`, built from the Schrödinger model of GKT §1.2.2 ((1.6), Theorem 1.13, p. 25).

The module `Langlands.Theta.DualPair.Unitary.Schrodinger` defines the Schrödinger representation of
the Heisenberg group of the symplectic space `𝕎 = M_{α×2ν}(E)` of the unitary dual pair
(`Langlands.Theta.DualPair.Unitary.Form`) on the Schwartz–Bruhat functions on `M_{α×ν}(E)`.

## Content

- `continuous_hermitianPairing_left`: `x ↦ β x y` is continuous for the module topology,
  `β = hermitianPairing c Q`.
- `hermitianSchrodinger c ν Q ψ`: the Schrödinger representation `HeisenbergGroup.schrodingerSB` of
  `HeisenbergGroup (polarizedForm β)` on `SchwartzBruhat (M_{α×ν}(E))`, for a unitary character `ψ`
  of `F` (`hermitianSchrodinger_apply`): `((x₀, y₀), t)` acts by
  `φ ↦ ψ(t) ψ(β(·, y₀) + ½ β(x₀, y₀)) φ(· + x₀)`.

The form of the file is one half of the book's form `⟪,⟫` (GKT Theorem 10.28, p. 288): the
Heisenberg group of `(𝕎, ½⟪,⟫)` with central character `ψ` is that of `(𝕎, ⟪,⟫)` with central
character `t ↦ ψ(t / 2)`, so `hermitianSchrodinger c ν Q ψ` is the book's Schrödinger model for the
character `t ↦ ψ(t / 2)`.

The internal part (namespace `Langlands.Theta.Unitary.Internal`) has the same operators written
with the symplectic form (`heisFun`, with `schrodingerFun_hermitian`: `heisFun = schrodingerFun`),
their composition law (`heisFun_heisFun`), their behaviour under the Siegel Levi
(`heisFun_levi`), and their action on Schwartz–Bruhat functions (`heisFun_mem`, `Heisenberg₂`).

## Source and licence

From <https://github.com/leanprover-community/riemann-hypothesis>, commit `f1f6d65`:
`src/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/KudlaSplittingSplitUnitary.lean`,
lines 76–212 (`heisFun`, `heisFun_heisFun`, `heisFun_levi`, `heisFun_mem`, `Heisenberg₂`,
`heis_apply`; the form and its lemmas of the same lines are in
`Langlands.Theta.DualPair.Unitary.Form`). The repository has no licence file; the text is used with
attribution, see `licenses/RiemannHypothesis/SOURCE.md`.

## Changes against the source

- Namespace `GlobalTheory.SplitUnitary` → `Langlands.Theta` (public) and
  `Langlands.Theta.Unitary.Internal`.
- `SplitUnitary.Heisenberg₂` is replaced, in the public statements, by `hermitianSchrodinger`, that
  is `HeisenbergGroup.schrodingerSB` applied to `hermitianPairing c Q`;
  `schrodingerFun_hermitian` is the bridge `heisFun = schrodingerFun`.
- `SB` → `schwartzBruhatSubmodule`; the source's `isLocallyConstant_addChar` → the Library's
  `isLocallyConstant_of_continuous_addChar`.
- New: `continuous_hermitianPairing_left`, `hermitianSchrodinger`, `hermitianSchrodinger_apply`.

## Declarations

- `Langlands.Theta.continuous_hermitianPairing_left`
- `Langlands.Theta.hermitianSchrodinger`, `hermitianSchrodinger_apply`

## Dependencies

`Langlands.Theta.DualPair.Unitary.Form`.
