# Double-root commutator friendliness and KP Proposition 13.2.5(1), (2), (4)

This module defines one predicate on supplied filtrations of `Z(F)` and states four
Prop-valued `def`s. Nothing in it is proved. It extends the published modules
`KPMoyPrasadFiltration`, `KPMoyPrasadFiltrationStatement` and
`CentralizerFiltrationExistenceStatement`, which it leaves unchanged.

The published `MoyPrasadCovarianceStatement` and `MoyPrasadCommutatorStatement` assume
`Zf.SatisfiesFiltrationAxioms`. Its commutator clause, `IsCommutatorFriendly`, is KP
Definition 7.2.1. The proofs of Proposition 13.2.5(1), (2) and (4) need a sharper bound on
the `Z`-component of a commutator when a double root `±2a` is involved, and that bound is
not a consequence of Definition 7.2.1 in the way the proofs use it. This module states the
sharper bound and restates the two targets with it as an extra premise. The section "The
gap in the source argument" below gives the details.

## Definition

`ParahoricBuildingData.CentralizerFiltration.IsDoubleRootCommutatorFriendly Zf` has the
hypotheses of the published `IsCommutatorFriendly`. These are an apartment point `x`, a
relative root `a`, elements `u ∈ U_a(F)` and `u' ∈ U_{-a}(F)`, both nontrivial, a real
`r > 0` with `r = x_a(u) + x_{-a}(u')`, and a decomposition
`u'⁻¹ u u' u⁻¹ = v' · j(z) · v` with `v' ∈ U_{-a}(F)`, `v ∈ U_a(F)` and `z ∈ Z(F)`. It adds
the hypothesis that `u ∈ U_{2a}(F)` or `u' ∈ U_{-2a}(F)` (`P.doubleRootGroup a`, trivial
when `2a` is not a root). Under these hypotheses it concludes `z ∈ Z(F)_{2r}`
(`Zf.filtration (2 * r)`), where `IsCommutatorFriendly` concludes only `z ∈ Z(F)_r`.

`U_{2a}(F)` is contained in `U_a(F)` (the root group of `a` is the one of the closed set
`{a, 2a}`), so the two hypotheses on `u` are compatible. By Axiom V 4
(`IsRootDatumValuation.double`), `x_a(u) = x_{2a}(u) / 2` for `u ∈ U_{2a}(F)`. For
`u ∈ U_{2a}(F)` the bound `2r` is therefore `x_{2a}(u) + 2 x_{-a}(u')`, and for
`u' ∈ U_{-2a}(F)` it is `2 x_a(u) + x_{-2a}(u')`. When both lie in double-root groups, `2r`
is `x_{2a}(u) + x_{-2a}(u')`, which is the bound `IsCommutatorFriendly` already gives for the
root `2a`. The new content is the mixed pairs `(a, -2a)` and `(2a, -a)`. When the root
system of `S` is reduced, the predicate says nothing beyond `IsCommutatorFriendly`.

`z` is the `Z`-component of KP Definition 7.1.3. As for `IsCommutatorFriendly`, the
decomposition is a hypothesis: any `z` admitting such a decomposition must lie in `Z(F)_{2r}`.

## The statements

The statements range over every nonarchimedean local field `F : Type u` (equal and mixed
characteristic), every `G` over `Spec F` with `[IsAffineHom G.X.hom]` and every
`P : ParahoricBuildingData G` with `P.SatisfiesApartmentAxioms` (V 6 in the data, V 7 and
AS 2–AS 5), as the published Moy–Prasad statements do.

- `MoyPrasadDoubleRootCovarianceStatement` is the published `MoyPrasadCovarianceStatement`
  with the extra premise `Zf.IsDoubleRootCommutatorFriendly`. For all `Zf` with
  `Zf.SatisfiesFiltrationAxioms` and that premise, every point `y` of the reduced building,
  every `r : ℝ≥0` and all `Q, Q'` with `Zf.IsMoyPrasadAt y r Q` and `Zf.IsMoyPrasadAt y r Q'`,
  it asserts `Q = Q'`. As explained in `KPMoyPrasadFiltrationStatement.md`, this is
  Proposition 13.2.5(1) and (2) for supplied data, including normality of `P_{x,r}` in the
  stabilizer of `x`.
- `MoyPrasadDoubleRootCommutatorStatement` is the published `MoyPrasadCommutatorStatement`
  with the same extra premise: `⁅P_{x,r}, P_{x,s}⁆ ≤ P_{x,r+s}` for every apartment point
  `x` and all `r, s : ℝ≥0` (Proposition 13.2.5(4)).
- `MoyPrasadDoubleRootStatement` is the conjunction of the two previous statements.
- `CentralizerFiltrationDoubleRootExistenceStatement` is the published
  `CentralizerFiltrationExistenceStatement` with one more conjunct: there is
  `Zf : P.CentralizerFiltration` with `Zf.SatisfiesFiltrationAxioms`, `Zf.IsOpenFiltration`
  and `Zf.IsDoubleRootCommutatorFriendly`.

A proof of the existence statement and of the two corrected statements would give
Proposition 13.2.5(1), (2) and (4) for every `P` satisfying the apartment axioms, with no
supplied filtration.

## The gap in the source argument

Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023). Page numbers are printed /
PDF.

- Proposition 13.2.5, p. 469 / PDF p. 500. The proof derives (1) from Propositions 7.3.17
  and 7.6.4, and (2) from Lemma 7.7.8(1). It derives (4) from (2) when `r = 0` or `s = 0`.
  For `r, s > 0` it reduces (4) to commutators of `U_{a,x,r}` with `U_{b,x,s}`, and cites
  Lemma 7.1.2, Definition 7.1.3 and commutator friendliness when `a` is a negative rational
  multiple of `b`. Take `u ∈ U_{2a,x,r}` and `u' ∈ U_{-a,x,s}`, so that `x_a(u) ≥ r/2` and
  `x_{-a}(u') ≥ s`. Lemma 7.1.2(2) (p. 240 / PDF p. 271) places the root factors of the
  commutator in `P_{x,r+s}`. Definition 7.2.1 only places its `Z`-component in
  `Z(k)_{r/2+s}`, whereas `P_{x,r+s} ∩ Z(k) = Z(k)_{r+s}` (Lemma 7.3.16). The pair
  `(U_{a,x,r}, U_{-2a,x,s})` is symmetric, with `Z(k)_{r+s/2}`.
- Proposition 7.3.17, pp. 252–253 / PDF pp. 283–284: `G(k)_{x,f}` is normalized by
  `G(k)_{x,0}` for constant `f`. The proof treats every commutator `(u, v)` with
  `u ∈ U_{a,x,0}` and `v ∈ U_{b,x,f(b)}` by Axiom V 3. V 3 excludes `b ∈ -ℝ_{>0} a`. Among
  the omitted pairs, `u ∈ U_{a,x,0}` against `v ∈ U_{-2a,x,r}` has `x_a(u) + x_{-a}(v) ≥ r/2`,
  so Definition 7.2.1 gives only `Z(k)_{r/2}` for the `Z`-component, while `Z(k)_r` is needed.
  The pairs `(a, -a)` and `(2a, -a)` at these depths do give `Z(k)_r`, and so does
  `(2a, -2a)`, by Definition 7.2.1 for the root `2a`.

Both gaps disappear with the double-root bound. For the pair `(U_{2a,x,r}, U_{-a,x,s})` it
gives `Z(k)_{r+2s} ⊆ Z(k)_{r+s}`. For `(U_{a,x,0}, U_{-2a,x,r})` it gives `Z(k)_r`. The
root factors are handled by Lemma 7.1.2 as in the source.

KP's own computation contains the sharper bound. In the proof of Proposition 7.1.1 for
quasi-split groups (pp. 239–240 / PDF pp. 270–271), the rank-one group is reduced to `SL_2`
or `SU_3` with the Chevalley valuation. In `SU_3` the `Z`-component is the torus element of
`γ = 1 + αα' + ββ'` (conjugations as printed), and the valuation of the root group of `a` is
`φ_a((α, β)) = ω(β)/2`. If `u ∈ U_{2a}(k)` then `α = 0`, as the proof notes, and
`γ - 1 = ββ'`. Its valuation is `ω(β) + ω(β') = 2(φ_a(u) + φ_{-a}(u'))`, for all signs of the
two depths. The case `u' ∈ U_{-2a}(k)` (`α' = 0`) is symmetric. Lemma 7.2.3 (pp. 245–246 /
PDF pp. 276–277) concludes from "the element `γ` computed there" only commutator
friendliness in the sense of Definition 7.2.1.

We know no counterexample to the published `MoyPrasadCovarianceStatement` or
`MoyPrasadCommutatorStatement`. They are not withdrawn. Their premises do not include the
double-root bound, however, and the source proofs do not derive them from the four
published properties, and we found no such derivation. Conjugation by `m(u)` only exchanges
the two mixed pairs, and translation along the apartment preserves `x_a(u) + x_{-a}(u')`.

## Why the actual filtration satisfies the predicate

This is a derived argument, not written out by KP. The existence statement is a target and
its proof must supply it.

- Quasi-split `G`. Lemma 7.2.3 reduces commutators in the rank-one subgroup generated by
  `U_{±a}` and `U_{±2a}` to `SL_2` and `SU_3` through the functoriality of the filtration of
  tori (§7.2, Definition 7.2.2 and properties (1), (2)). In `SU_3` the torus is induced, so
  for `s > 0` property (2) gives `T(k)_s = {t ∈ T(k) | ω(χ(t) - 1) ≥ s for all χ ∈ X^*(T)}`.
  The torus element of `γ` with `ω(γ - 1) = 2r` therefore lies in `T(k)_{2r}`, and
  functoriality puts the `Z`-component in `Z(k)_{2r}`.
- General `G` (§9.8, pp. 374–375 / PDF pp. 405–406). KP define
  `Z(k)_r = Z(K)_{x,r} ∩ Z(k)` over `K = k^ur`, and Lemma 9.8.1 proves commutator
  friendliness by passing to `G(K)` at a point of `A(S, G)`. The group `Z(k)_r` does not depend
  on the point, while translating the point by `v ∈ V(S)` changes `x_a(u)` and `x_{-a}(u')` by
  `a(v)` and `-a(v)`. Choose the point `y` with `y_{-a}(u') = 0`. For `u ∈ U_{2a}(k)` this gives
  `u ∈ U_{2a,y,2r}` and `u' ∈ U_{-a,y,0}`. In the quasi-split group `G_K` the double-root
  bound holds by the previous item. With it, the argument of Proposition 7.3.17 shows that
  `G(K)_{y,2r}` is normalized by `G(K)_{y,0}`, so the commutator lies in `G(K)_{y,2r}`. Its `Z`-component then lies in
  `G(K)_{y,2r} ∩ Z(K) = Z(K)_{y,2r}`, by the Iwahori decomposition of `G(K)_{y,2r}` and
  Lemma 8.5.19, as in the proof of Lemma 9.8.1. Hence it lies in `Z(k)_{2r}`. The case
  `u' ∈ U_{-2a}(k)` uses the point with `y_a(u) = 0`.

## Source correspondence

Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023), registered as
`kaletha-prasad-2023-bruhat-tits-new-approach`:

- Proposition 7.1.1, p. 237 / PDF p. 268, and its proof for quasi-split groups,
  pp. 239–240 / PDF pp. 270–271: the `SL_2` and `SU_3` formulas.
- Lemma 7.1.2, pp. 240–242 / PDF pp. 271–273, and Definition 7.1.3, p. 242 / PDF p. 273:
  commutators of `U_a` and `U_{-a}` and their `Z`-component `u'⁻¹ u u' u⁻¹ ∈ U_{-a}(k) z U_a(k)`.
- Definition 7.2.1, Definition 7.2.2 and Lemma 7.2.3, pp. 245–246 / PDF pp. 276–277.
- Lemma 7.3.16 and Proposition 7.3.17, pp. 252–253 / PDF pp. 283–284.
- Proposition 7.6.4, p. 265 / PDF p. 296, and Lemma 7.7.8, p. 271 / PDF p. 302: the inputs
  of 13.2.5(1) and (2).
- §9.8 and Lemma 9.8.1, pp. 374–375 / PDF pp. 405–406.
- Proposition 13.2.5 and its proof, p. 469 / PDF p. 500.

Kaletha–Prasad, *Corrections and additions* (1 November 2024), registered as
`kaletha-prasad-2024-corrections`. Its Chapter 7 entries (PDF pp. 33–36) concern the opening
of Chapter 7 (AS 5), the proof of Lemma 7.1.4, an added part (6) of Proposition 7.3.12, an
added Lemma 7.3.24, and §§7.4, 7.5, 7.8 and 7.11. None changes Definition 7.2.1, Lemma 7.1.2,
Lemma 7.2.3 or Proposition 7.3.17. PDF p. 41 restricts the projection in the proof of
Lemma 9.8.1 to `B(G)^M`. The Chapter 13 entries (PDF pp. 49–50) concern 13.5.2, 13.6.2 and
13.8.5. The gap described above is not addressed there.

## Provenance and scope

The provenance is derived. The predicate is not a clause of KP Definition 7.2.1. It records
the bound that KP's `SU_3` computation gives and that the proofs of Proposition 13.2.5(1),
(2) and (4) use. The corrected statements are the published ones with this premise added.
The data are supplied, as in the published Moy–Prasad statements, and their applicability to
an actual group needs the KP Theorem 9.2.7 certificate. KP work over Henselian discretely
valued fields; `F` is specialized to nonarchimedean local fields.

The predicate covers only the mixed and double pairs of a multipliable root. The bounds for
the other pairs remain those of `IsCommutatorFriendly` and of the published predicates
`IsRootCompatible` and `IsCommutatorFiltered`. The separation, boundedness and openness
statements and Proposition 13.2.5(3), (5) and (6) (`MoyPrasadProductStatement`,
`MoyPrasadLeviStatement`) are not restated. The derivations recorded for them go through
Proposition 7.3.12 and Lemma 7.3.16 at the constant function `r`. There the `Z`-components
come from pairs in `U_{a,x,r} U_{2a,x,r}` and `U_{-a,x,r} U_{-2a,x,r}`, with
`x_a(u) + x_{-a}(u') ≥ r`, and Definition 7.2.1 already gives `Z(k)_r`.
