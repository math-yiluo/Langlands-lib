# KP Proposition 13.2.5 (1), (2), (4) and openness on supplied data

This module states four parts of Kaletha–Prasad, *Bruhat–Tits theory: a new
approach* (2023), Proposition 13.2.5, printed p. 469 / PDF p. 500, for the
Moy–Prasad subgroups `P_{x,r}` of `KPMoyPrasadFiltration`. It proves nothing.
The combined target is `MoyPrasadFiltrationStatement`, the conjunction of the
four statements below.

The source is registered as `kaletha-prasad-2023-bruhat-tits-new-approach`,
SHA-256 `05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`.
The authors' corrections of 1 November 2024
(`kaletha-prasad-2024-corrections`, SHA-256
`23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`) list no
change to Definition 13.2.1 or Proposition 13.2.5. Their Chapter 13 entries,
PDF pp. 49–50, concern 13.5.2, 13.6.2 and 13.8.5.

## Common premises

Each statement quantifies over a nonarchimedean local field `F` (any
universe level `u`), a group scheme `G` over `F` with affine structure
morphism, supplied building data `P : ParahoricBuildingData G` (which records
that `G` is connected reductive and `S` a maximal split torus) and a supplied
filtration `Zf : P.CentralizerFiltration`. It assumes:

- `P.SatisfiesApartmentAxioms`: Axiom V 6 (part of the data) and the
  hypotheses V 7 and AS 2–AS 5 of KP Chapter 7. These are the axioms under
  which Chapter 7 proves the results that the proof of 13.2.5 cites:
  Propositions 7.3.12, 7.3.17 and 7.6.4, and Lemma 7.7.8.
- `Zf.SatisfiesFiltrationAxioms`: the supplied filtration is
  commutator-friendly (Definition 7.2.1), stable under `N(F)`, satisfies
  `[Z(F)_r, Z(F)_s] ⊆ Z(F)_{r+s}`, and its commutators with `U_{a,x,s}` lie in
  the depth-`r+s` block. `KPMoyPrasadFiltration.md` explains why the actual
  filtration of KP §9.8 has these properties.
- For the openness target only, `Zf.IsOpenFiltration`: each `Z(F)_r` is open
  in `Z(F)`.

These premises replace "x in the building of a connected reductive `G` with
the filtration of §9.8". The building and the filtration of `Z(F)` are
supplied, not constructed. The statements are therefore conditional
supplied-data versions of the source. Their applicability to an actual group
needs the KP Theorem 9.2.7 certificate and a constructed filtration (§9.8 and
Appendix B), neither of which is in the Library.

## The four statements

- `MoyPrasadSeparatedStatement`: for every point `x` of the apartment,
  `⨅ r, P_{x,r} = ⊥`. This is "separated" in the opening sentence. It is the
  identity `P_{x,∞} = {1}` of the separated extension of §1.6.
- `MoyPrasadBoundedOpenStatement`: for every `x` and every finite
  `r ≥ 0`, `P_{x,r}` is open in `G(F)` for the point topology
  (`rationalPointTopology`) and algebraically bounded
  (`IsAlgebraicallyBounded`, the notion used by the Library's
  `HasBoundedOpenStabilizers`). The opening sentence calls the subgroups
  "bounded open". Openness is stated only at finite depth: Corollary 7.3.14,
  PDF p. 282, asserts openness only when the concave function never takes the
  value `∞`. This finite-depth restriction is an independent clarification,
  not an authors' correction.
- `MoyPrasadCovarianceStatement`: if `IsMoyPrasadAt y r Q` and
  `IsMoyPrasadAt y r Q'`, then `Q = Q'`. This is 13.2.5(1) and (2) for supplied
  data. `IsMoyPrasadAt y r Q` means `Q = g P_{x,r} g⁻¹` for some `g` and some
  apartment point `x` with `g · x = y`. Other maximal split tori and their
  apartments are `G(F)`-translates of the supplied ones, so independence of
  `S` (part (1)) is uniqueness of `Q` across presentations. Taking
  `y = g · x = x'` with `x, x'` in the apartment gives `g P_{x,r} g⁻¹ = P_{x',r}`
  (part (2)). Taking `g · x = x` gives normality of `P_{x,r}` in the
  stabilizer of `x`.
- `MoyPrasadCommutatorStatement`: `⁅P_{x,r}, P_{x,s}⁆ ≤ P_{x,r+s}` for all
  `r, s ≥ 0` (13.2.5(4)).

The opening sentence's "decreasing" is already a theorem,
`CentralizerFiltration.moyPrasad_antitone`.

## Two statements fail on paper

The public note
`notes/bruhat-tits/moy-prasad-supplied-filtration-counterexample.md` gives an
unformalized paper argument that `MoyPrasadCovarianceStatement` and
`MoyPrasadCommutatorStatement` are false, and with them
`MoyPrasadFiltrationStatement`. Its model is the quasi-split ramified `SU_3` of
`Q_2(√2)/Q_2` with the smallest filtration of `Z(F)` that satisfies
`SatisfiesFiltrationAxioms`. Commutator friendliness places the `Z`-component of
a commutator of `u ∈ U_{2a,x,r}` with `u' ∈ U_{-a,x,s}` only in `Z(F)_{r/2+s}`.
For this filtration the component can lie outside `Z(F)_{r+s}`, and the note
gives explicit elements violating both conclusions. The argument assumes that
this group with its standard valuation of root datum is an instance of
`ParahoricBuildingData` satisfying `SatisfiesApartmentAxioms`. The Library has no
such instance, so no Lean counterexample is constructed.

KP's Proposition 13.2.5 itself is not refuted: KP's filtration of `Z(F)` is
larger than this one. The module `KPMoyPrasadDoubleRootStatement` restates the
two statements with the extra premise `IsDoubleRootCommutatorFriendly`, which
this filtration fails. `MoyPrasadSeparatedStatement` and
`MoyPrasadBoundedOpenStatement` are not affected. The four statements stay
published unchanged.

## Not stated

- Part (3), the product bijection at positive depth. The printed indexing
  over all positive and negative roots conflicts with its cited source,
  Proposition 7.3.12(5), which uses non-divisible roots and the concave-function
  blocks `U_{a,x,r} U_{2a,x,r}`. The program's source ledger records this
  discrepancy as an open formal-resolution obligation. No version is stated
  here.
- Parts (5) and (6), the Iwahori decomposition and the Levi intersection.
  They need the Levi embedding `B(G)_M` and the map `x ↦ x_M` of §9.7, which
  are not in the Library.
- The Lie-algebra filtrations of §13.3 and the Moy–Prasad isomorphism of
  §13.5.
