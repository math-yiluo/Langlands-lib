# Two apartments are `G(F)^0`-conjugate by an element fixing their intersection

`Langlands.Geometry.Building.ApartmentConjugacyFixingIntersectionStatement`
is a Prop-valued `def` at every universe `u`. It states Kaletha–Prasad
Proposition 4.2.24 for the existing quotient `B(G)` of supplied building data
over a nonarchimedean local field. The data are assumed to satisfy the axioms
that KP assume at the opening of Section 4.2, as corrected, with Axiom 4.1.1
restricted to its clauses for `G` alone. Given two
apartments `A₁`, `A₂` of `B(G)`, some `g ∈ G(F)^0` carries `A₁` onto `A₂` and
fixes every point of `A₁ ∩ A₂`. The module supplies no proof.

## Statement

The proposition quantifies over:

- every nonarchimedean local field `F`, of either characteristic;
- every group scheme `G` over `Spec F` with `[IsAffineHom G.X.hom]`;
- every `P : ParahoricBuildingData G`. These are the Library's building data:
  a maximal split torus `i : S → G`, the class `A(S)` of valuations of the
  root datum, the actual centralizer `Z = Z_G(S)`, axiom V 6 on `Z(F)`, and
  the data of KP Definition 2.6.23 for `Z(F)^0` and `G(F)^0`. Connected
  reductivity of `G` is a field of the data;
- every polysimplicial structure
  `R : P.toValuationBuildingData.PolysimplicialRealization` on `B(G)` and
  every splitting `T : P.toValuationBuildingData.ApartmentSplitting` of the
  apartment, as used by Axioms 4.1.1 and 4.1.4.

It assumes seven predicates on these data. Together they express the axioms
of the corrected opening of KP Section 4.2, with Axiom 4.1.1 restricted to its
clauses for `G` alone:

1. `P.SatisfiesBuildingAxiom R`: the clauses of KP Axiom 4.1.1 for `G` alone.
   With `R`, `B(G)` is a building in the sense of KP Definition 1.5.5, and its
   facets and face relation match those of `R`. `G(F)` acts by polysimplicial
   automorphisms, the apartments correspond bijectively and equivariantly to
   the maximal split tori, and the stabilizer of `A(S)` in `G(F)` is `N(F)`.
2. `P.HasBoundedOpenStabilizers`: KP Axiom 4.1.2.
3. `P.SatisfiesAffineApartmentAxiom T`: KP Axiom 4.1.4.
4. `P.HasRootReflections`: AS 1 of KP Axiom 4.1.6.
5. `P.SatisfiesApartmentAxioms`: V 6, V 7 and AS 2–AS 5 for the class `A(S)`
   and the centralizer of `P`. V 6 is part of the data, so this premise asks
   for V 7 (the root filtrations are compatible with the topology of `G(F)`,
   KP Definition 6.1.2) and AS 2–AS 5.
6. `P.HasCompatibleApartmentFacets`: AS 6 of KP Axiom 4.1.6.
7. `P.HasTitsSystem`: the corrected KP Axiom 4.1.9, for every chamber of
   `A(S)`. With `I` the stabilizer in `G(F)^0` of the chamber, `I` and
   `N(F) ∩ G(F)^0` form a saturated Tits system in `G(F)^0` whose restricted
   building is `B(G)`.

Premises 4–6 are the three fields of `KPBuildingDatum.SatisfiesAffineRootSystemAxiom`.
The seven premises are the same as those of the published
`BoundedSubgroupFixedPointStatement` (KP Corollary 4.2.14).

The conclusion concerns every pair of subsets
`A₁ A₂ : Set P.toValuationBuildingData.ReducedBuilding` with
`P.IsApartment A₁` and `P.IsApartment A₂`. An apartment of `B(G)` is a
translate `h • A(S)` of the image of `A(S)` by some `h ∈ G(F)`
(`ValuationBuildingData.IsApartment`). For such a pair the statement asserts
`∃ g ∈ P.zeroSubgroup, g • A₁ = A₂ ∧ ∀ y ∈ A₁ ∩ A₂, g • y = y`. Here
`P.zeroSubgroup` is `G(F)^0 = G(F)^♮ · Z(F)^0` (KP Definition 2.6.23(3)),
`g • A₁` is the pointwise image of `A₁`, and `g • y` is the action of `G(F)`
on `B(G)`.

## Source correspondence

The source is Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023),
`kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`.
Proposition 4.2.24 is on printed p.176 / PDF p.207, and its proof continues
on printed p.177 / PDF p.208: "Let `A1, A2` be two apartments of `B`. There
exists `g ∈ G(k)^0` such that `gA1 = A2` and `gx = x` for every
`x ∈ A1 ∩ A2`." The statement matches it clause for clause. KP's `B` is the
building of Section 4.2, and KP's `G(k)^0` is `P.zeroSubgroup`.

Section 4.2 opens on printed p.168 / PDF p.199 with "We assume given a
building `B` satisfying Axioms 4.1.1, 4.1.2, 4.1.4, and 4.1.9." The authors'
corrections of 1 November 2024, `kaletha-prasad-2024-corrections`, SHA-256
`23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`, add
Axiom 4.1.6 to this sentence (PDF p.28). They do not change the statement of
Proposition 4.2.24. They cite it in the corrected proof of Proposition 4.2.1
(PDF p.29), and in the proof of Theorem 5.2.1 they keep only the appeal to
it (PDF p.30). The field conventions of Chapter 4 are at its opening, printed
p.157 / PDF p.188: `k` has a discrete valuation, a Henselian valuation ring
and a perfect residue field, and `G` is a connected reductive `k`-group.

## Derived scope and provenance

This is a derived formulation, not a literal transcription.

- **Field.** The statement covers nonarchimedean local fields, of mixed and
  equal characteristic. Their residue fields are finite, hence perfect, and
  their valuation rings are Henselian. Other fields allowed by KP Chapter 4
  are not covered.
- **The building.** KP's Section 4.2 concerns any building with a `G(k)`-action
  satisfying the axioms. Here the building is the existing quotient
  `B(G) = P.toValuationBuildingData.ReducedBuilding` of `G(F) × A(S)` (KP
  Remark 7.6.5), and its apartments are the translates `h • A(S)`. The axioms
  are the Library's predicates on these data.
- **Axiom 4.1.1.** Only the clauses for `G` alone are assumed. The
  comparisons of Axiom 4.1.1 between the buildings of different groups
  (central quotients, derived subgroup, simply connected cover) are not
  premises. KP's proof does not use them.
- **Relation to availability.** The full corrected Definition 4.1.26 for an
  assignment, `KPBuildingAssignment.IsAvailableFor`, supplies all seven
  premises for `P = (𝔅.datum F G hG).base`, `R = (𝔅.datum F G hG).realization`
  and `T = (𝔅.datum F G hG).splitting`. They come from its fields
  `existenceOfBuilding.building`, `boundedSubgroups`, `affineStructure`,
  `affineRootSystem` and `titsSystem`. Hence the statement applies to
  available data.

No existence of the supplied data, of the realization, of the splitting or
of the axiom witnesses is asserted.

## Expected proof route (not prescribed)

KP's proof uses the metric of Proposition 4.2.1 and Proposition 1.5.13(1)
for the Tits system of Axiom 4.1.9. The intersection `A₁ ∩ A₂` is a closed
convex union of facets. A facet `F` of maximal dimension in it is open in
`A₁ ∩ A₂`. Proposition 1.5.13(1) gives `g ∈ G(k)^0` with `gA₁ = A₂` and
`gx = x` for all `x ∈ F`. For `y ∈ A₁ ∩ A₂` and `x ∈ F`, the
segments `[x, y]` and `g[x, y] = [x, gy]` in `A₂` share `x` and the points of
`[x, y] ∩ F` near `x`, so they coincide and `gy = y`. KP's proof does not
discuss an empty intersection. In that case the conclusion is the
transitivity of `G(F)^0` on apartments, which the corrections invoke in the
proof of Proposition 4.2.1.

Library material that may help: the proved
`Langlands.Geometry.Building.metricRealization`, which gives a complete
nonpositively curved metric on `B(G)` with isometric action under the same
seven premises (`MetricRealizationStatement`), and the Tits-system modules
under `Langlands/Group/`, among them `TitsApartmentPairTransport` (a
transporter between two restricted apartments that contain the same two
admissible parabolic subgroups, lying in both), `TitsCommonApartment` and
`TitsApartmentStabilizer`.
