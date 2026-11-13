# Existence of the KP §9.8 filtration of `Z(F)`

`Langlands.Geometry.Building.CentralizerFiltrationExistenceStatement` is a Prop-valued
`def` at every universe `u`. Nothing in this module proves it.

## Statement

The proposition ranges over every `F : Type u` with `Field F`, `ValuativeRel F`,
`TopologicalSpace F` and `IsNonarchimedeanLocalField F`, in equal and mixed characteristic,
every group scheme `G` over `Spec F` with `[IsAffineHom G.X.hom]`, and every
`P : ParahoricBuildingData G` with `P.SatisfiesApartmentAxioms`. `ParahoricBuildingData`
contains connected reductivity of `G`, a maximal split torus `S`, its `N(F)`-stable class
of `ω`-compatible valuations of the root datum with V 6, the actual centralizer `Z = Z_G(S)`,
and the data of KP Definition 2.6.23. These data define `Z(F)^0` as the published
`P.centralizerZero`. `P.SatisfiesApartmentAxioms` is V 7 and AS 2–AS 5.

The conclusion asserts that there is `Zf : P.CentralizerFiltration` such that
`Zf.SatisfiesFiltrationAxioms ∧ Zf.IsOpenFiltration`. These are the published definitions
of `Langlands.Geometry.Building.KPMoyPrasadFiltration`:

- `P.CentralizerFiltration` consists of subgroups `Z(F)_r` of `Z(F)` for `r : ℝ≥0`. They
  decrease in `r`, their intersection is trivial, and `Z(F)_0` equals `P.centralizerZero`.
  These are the first clauses of KP Definition 7.2.1.
- `SatisfiesFiltrationAxioms` is the conjunction of four predicates:
  - `IsCommutatorFriendly`, the commutator clause of KP Definition 7.2.1 with the
    `Z`-component of Definition 7.1.3: for every apartment point `x`, the `Z`-component of
    `u'⁻¹ u u' u⁻¹` lies in `Z(F)_r` when `r = x_a(u) + x_{-a}(u') > 0`;
  - `IsNormalizerStable`: each `Z(F)_r` is stable under conjugation by `N(F)`;
  - `IsCommutatorFiltered`: `[Z(F)_r, Z(F)_s] ⊆ Z(F)_{r+s}`;
  - `IsRootCompatible`: `z u z⁻¹ u⁻¹` lies in the block `U_{a,x,r+s} U_{2a,x,r+s}` for
    `z ∈ Z(F)_r` and `u ∈ U_{a,x,s}`.
- `IsOpenFiltration` says that each `Z(F)_r` is open in `Z(F)` for the point topology.

With these data the published `MoyPrasadFiltrationStatement` and its four conjuncts apply
to `P` and `Zf`. A proof of this statement together with proofs of those four would make the
Moy–Prasad results hold for every `P` satisfying the apartment axioms, with no supplied
filtration. Two of the four conjuncts, `MoyPrasadCovarianceStatement` and
`MoyPrasadCommutatorStatement`, fail on paper, however (see `KPMoyPrasadFiltrationStatement.md`
and the public note `notes/bruhat-tits/moy-prasad-supplied-filtration-counterexample.md`).
The corrected route uses `CentralizerFiltrationDoubleRootExistenceStatement` and the
double-root statements of `KPMoyPrasadDoubleRootStatement`.

## Source correspondence

Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023), registered as
`kaletha-prasad-2023-bruhat-tits-new-approach`:

- §7.2 and Definition 7.2.1, printed p. 245 / PDF p. 276: the filtration of `Z(k)` with
  conditions (1), (2) and commutator friendliness. Definition 7.1.3, printed p. 242 /
  PDF p. 273, and Lemma 7.1.2, printed pp. 239–241 / PDF pp. 270–272:
  the `Z`-component of a commutator.
- §9.8 and Lemma 9.8.1, printed pp. 374–375 / PDF pp. 405–406. Fix a functorial filtration
  of tori with (1) and (2) of §7.2 (Appendix B). Then `Z(k)_r = Z(K)_{x,r} ∩ Z(k)`, where
  `x` is the unique point of `B(Z)` (Proposition 9.3.9) and `Z(K)_{x,r}` is the §7.3 group of
  the quasi-split group `Z_K` for the constant concave function `r`. Lemma 9.8.1 proves
  `Z(k)_0 = Z(k)^0` and commutator friendliness. By Propositions 7.3.17 and 7.6.4 the
  group does not depend on `S`.
- §13.1 and the opening of Chapter 13, printed pp. 466–467 / PDF pp. 497–498: the choice of
  filtration of tori used for Moy–Prasad groups. Proposition 13.2.5(4), printed p. 469 /
  PDF p. 500, with its proof: the commutator bounds behind `IsCommutatorFiltered` (the case
  of `Z`) and `IsRootCompatible` (through `U_a(F) ∩ G(F)_{x,r+s}`, Proposition 7.3.12(3)).
  Openness of `Z(k)_r` comes from the open bounded groups of §7.3.

Kaletha–Prasad, *Corrections and additions* (1 November 2024), registered as
`kaletha-prasad-2024-corrections`: PDF p. 41 restricts the projection in the proof of
Lemma 9.8.1 to the subset `B(G)^M` of the building. PDF p. 50 corrects Appendix B on the
minimal congruent filtration of tori. Neither changes the existence asserted here.

## Provenance and scope

The provenance is derived. KP construct one filtration from a chosen functorial filtration
of tori. The statement asks only for existence, so any admissible choice is a witness. The
predicates `IsNormalizerStable`, `IsCommutatorFiltered` and `IsRootCompatible` are not
clauses of Definition 7.2.1; they are the properties of the §9.8 filtration that the
Moy–Prasad statements use. `N(F)`-stability follows from the independence of the choice of
`S` and functoriality, and the two commutator bounds from Proposition 13.2.5(4). The
statement quantifies over every `P` satisfying the apartment axioms. By KP
Proposition 6.2.6 (published as `KPApartmentData.eq_of_isOmegaCompatible_of_hasOppositeFactorPairs`)
its class is the canonical one, so KP's construction applies. KP work over Henselian
discretely valued fields with perfect residue field; `F` is specialized to nonarchimedean
local fields.

This module constructs no filtration of tori and no filtration of `Z(F)`, and proves no
part of Proposition 13.2.5.
