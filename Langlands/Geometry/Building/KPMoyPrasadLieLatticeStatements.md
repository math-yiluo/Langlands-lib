# Statements on the constructed lattices `𝔤_{x,r} = Lie(𝒢_{x,r})`

Let `F` be a nonarchimedean local field of either characteristic, `G` an affine group over `F`,
`P : ParahoricBuildingData G` satisfying the apartment axioms (`hP`) and
`h : P.MinimalCongruentCentralizerOrder`. `KPMoyPrasadLieLattices` defines, from models chosen
from the existence statements `hG : MoyPrasadModelStatement`, `hZ : CentralizerModelStatement`
and `hU : AffineRootGroupModelStatement`,

- `P.moyPrasadLie hG hP h x r = Lie(𝒢_{x,r})`, the lattice `𝔤_{x,r}` of KP §13.3.1, and
- `P.lieFiltrationData hZ hU hOrder hP`, the `LieFiltrationData` with `z_r = Lie(𝒵_r)` and
  `u_ψ = Lie(𝒰_ψ)`, using `hOrder : MinimalCongruentOrderStatement` for the decreasing property
  of `z_r`.

Each statement below quantifies over these hypotheses, so it is a statement about the
constructed objects for every admissible choice.

## Statements

- `MoyPrasadLieIndependenceStatement` (KP Corollary 2.10.11): every smooth model `M` of `G` over
  `𝒪[F]` whose integral points over the integers of the maximal unramified extension `K` are
  those of `moyPrasadModel hG hP h x r` (namely `G(K)_{x,r}`) has Lie lattice `𝔤_{x,r}`. The
  general fact for any two smooth models with equal points over the integers of `K` is the
  Library lemma `IntegralModel.lieLattice_eq_of_unramified`.

  The corresponding assertion with equality of points over `𝒪[F]` is false. For `F = ℚ₂` and
  `G = G_m` the standard model `𝒢_{x,0}` and its dilatation along the unit section of its
  special fibre are smooth with connected fibres and both have the points `𝒪[F]^×` over
  `𝒪[F]` (the special fibre `G_m(𝔽₂)` is trivial), but their Lie lattices are `𝒪[F]` and `𝔪`
  (`KPMoyPrasadModelStatements` gives the details). KP's Corollary 2.10.11 concerns points over
  the integers of `K`, which is the form stated here.
- `MoyPrasadLieSpanStatement` (KP 13.3.3): `𝔤_{x,r}` equals
  `(P.lieFiltrationData hZ hU hOrder hP).lieFiltration x r`, the `𝒪[F]`-span of the image of
  `z_r = Lie(𝒵_r)` in `Lie(G)` and of the `u_ψ = Lie(𝒰_ψ)` for the affine roots `ψ ∈ Ψ` with
  `ψ(x) ≥ r` (`Ψ_{x,r}` of KP Definition 13.2.1).
- `MoyPrasadLiePeriodicStatement` (KP 13.3.1, from Proposition 8.5.16 and Lemma A.5.13):
  `𝔤_{x,r+1} = 𝔪 𝔤_{x,r}` for every `x` and `r ≥ 0`, with `𝔪 = 𝓂[F]` the maximal ideal of
  `𝒪[F]`, and the constructed `LieFiltrationData` satisfies `IsPeriodic`
  (`lieFiltration x (r+1) = 𝔪 • lieFiltration x r`). Under `MoyPrasadLieSpanStatement` the two
  conjuncts are equivalent. The definitions `lieFiltrationReal` and `dualLieFiltration` of
  `KPLieFiltrationDual` apply to any `LieFiltrationData`; periodicity gives antitonicity of the
  real-depth extension `lieFiltrationReal` and is an explicit argument of `gradedLieDualPairing`
  in `KPLieGradedPairing`.

This file states these results and does not prove them.

## Sources

- Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023),
  `kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
  `05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732` (printed page = PDF
  page − 31): Corollaries 2.10.10–2.10.11 (p. 124); Proposition 8.5.16 and 8.5.20 (pp. 319–320);
  Definition 13.2.1 (p. 468); §13.3.1 and §13.3.3 (pp. 470–471); Lemma A.5.13 (p. 636).
- Kaletha–Prasad, *Corrections and additions*, 1 November 2024,
  `kaletha-prasad-2024-corrections`, SHA-256
  `23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`. There is no entry for
  §13.3.
