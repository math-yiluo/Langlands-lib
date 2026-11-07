# Induction in stages through an actual parabolic of the Levi

Module `Langlands.Representation.Exponents.LeviInductionStages`.

## Purpose and scope

The general case of Renard VI.7.5, Theorem (*Représentations des groupes réductifs
p-adiques*, 9 July 2026 version, printed p.187 / PDF p.193) starts from an embedding
`ρ ↪ ⊕_{P'} i_{P'}^M(ρ_{M'})`, where the `P'` are parabolics of the Levi `M`. Applying
`i_P^G` and VI.1.4 (transitivity, printed pp.136–137 / PDF pp.142–143) turns each summand
`i_P^G i_{P'}^M(ρ_{M'})` into an induction `i_{P''}^G(ρ_{M'})` from a parabolic `P''` of `G`
with Levi `M'`. The supercuspidal case then applies to `ρ_{M'}`.

This module carries out that change of parabolic for actual represented parabolics. The
group `G` is connected reductive, `P = M U` is an actual rational parabolic of `G` (with
`p`, `l`, `r`, `hp`, `hl`, `hr`, `hmul`), and `Q = N V` is an actual rational parabolic of
`M` (with `q`, `n`, `s`, `hq`, `hn`, `hs`, `hmulQ`). The module uses two published proved
results:

- `leviParabolicExtension` (proof of `LeviParabolicExtensionStatement`): there is an
  actual rational parabolic `R = N W` of `G` with Levi group scheme `N`, the same
  embedding of `N` in `G`, `range pR ≤ range p`, and
  `range (q ≫ l ≫ p) = range (l ≫ p) ⊓ range pR` as subgroup functors.
- `leviParabolicTransitivity` (proof of `LeviParabolicTransitivityStatement`): under the
  corresponding rational-point conditions, `i_R^G ≅ i_Q^M ⋙ i_P^G`.

The module proves neither VI.7.5 target. It assumes nothing beyond the published
hypotheses of the two results.

## Declarations

Namespace `Langlands.Aubert.General.RepresentedParabolic`.

- `LeviParabolicExtensionDatum p l q n` (structure): an actual rational parabolic `R` of
  `G` with unipotent radical `W`, inclusions `pR : R ⟶ G`, `nR : N ⟶ R`, `rR : W ⟶ R`,
  and the proofs `hpR`, `hnR`, `hrR`, `hmulR` that `(pR, nR, rR)` is an actual rational
  parabolic triple. It has three compatibility fields:
  - `levi_comp : nR ≫ pR = n ≫ q ≫ l ≫ p`: `N` is embedded in `G` in the same way;
  - `pointImage_le : pointImage pR ≤ pointImage p`, i.e. `R(F) ⊆ P(F)`;
  - `pointImage_inf : pointImage (q ≫ l ≫ p) = pointImage (l ≫ p) ⊓ pointImage pR`,
    i.e. `Q(F) = M(F) ∩ R(F)` inside `G(F)`.

  With `R` in the role of the smaller parabolic and `Q` the parabolic of the Levi, these
  are exactly the hypotheses of `LeviParabolicTransitivityStatement`. The structure
  bundles them; it adds no mathematical content.
- `LeviParabolicExtensionDatum.nonempty`: for connected reductive `G` and the two
  parabolic triples, an extension datum exists. Proof: `leviParabolicExtension`. Its
  subgroup-functor inclusion and intersection are evaluated at the identity test object
  `Over.mk (𝟙 _)`, where `pointImage` is the carrier of the range. This follows
  `exists_ambient_isNormalizedJacquetExponent_of_unitary` in
  `Exponents/NestedLeviJacquetExponents.lean`.
- `LeviParabolicExtensionDatum.ofExtension` (definition): a chosen extension datum
  (`Classical.choice` of `nonempty`).
- `LeviParabolicExtensionDatum.leviInduction_iso`: for every extension datum `D`,
  `Nonempty (i_{D.R}^G ≅ i_Q^M ⋙ i_P^G)`, where both sides are the published
  `leviInductionFunctor`, `i_Q^M` lands in carrier universe `max u v`, and `i_P^G` is
  applied at that universe. The topologies on `M(F)` and `N(F)`, and the local compactness
  and nonarchimedean instances on `M(F)`, are the published Levi-point ones. Proof:
  `leviParabolicTransitivity`, first component, applied to the triple `D.R ⊆ P` with inner
  parabolic `Q`.
- `LeviParabolicExtensionDatum.isNoetherian_leviInduction_iff`: for every smooth `σ` of
  `N(F)`, the induction `i_{D.R}^G(σ)` has a Noetherian group-algebra module over
  `ℂ[G(F)]` if and only if `i_P^G(i_Q^M(σ))` has one. Proof: the component at `σ` of the
  isomorphism above gives an equivariant linear equivalence (`SmoothRep.equivOfIso`). Its
  `ℂ[G(F)]`-linear map, through `Representation.IntertwiningMap.equivLinearMapAsModule`,
  is surjective, and so is the inverse. Mathlib's `isNoetherian_of_surjective` then gives
  both directions. The private helper `isNoetherian_of_iso` records this transfer.

## Provenance

`LeviParabolicExtensionDatum` is internal packaging of the conclusion of
`LeviParabolicExtensionStatement` in the form that `LeviParabolicTransitivityStatement`
consumes. The isomorphism is Renard's VI.1.4 in the form used in the general step of the
VI.7.5 Theorem, and the Noetherian transfer is elementary.
