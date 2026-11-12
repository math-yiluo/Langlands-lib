# The actual valuation quotient is the restricted building of the Iwahori–Tits system

`Langlands.Geometry.Building.AffineIwahoriTitsBuildingStatement.{u}` is a named
Prop-valued `def` at an arbitrary universe `u`. It is a proof target, not a theorem.
It asserts that the actual `G(F)^0` affine Iwahori–Tits system of KP Theorem 7.5.3,
in the form of the existing predicate `AffineIwahoriTitsWith`, is the Tits system of
KP Axiom 4.1.9 on the existing reduced building `B(G)`, the quotient (7.6.2).

## Statement

```text
∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] (G : GroupScheme (Spec (CommRingCat.of F)))
  [IsAffineHom G.X.hom] (P : ParahoricBuildingData G),
  P.apartment.SatisfiesApartmentAxioms P.centralizer →
    ∀ (_ : P.normalizerZero.Normal) (_ : P.zeroSubgroup.Normal) (C : Set P.Apartment)
      (e : P.affinePart ≃* AffineRootSystem.affineWeylGroup P.affineRoots),
      AffineRootSystem.IsChamber P.affineRoots C → P.AffineIwahoriTitsWith C e →
        P.IsBuildingTitsSystem C P.affineTitsProjection (P.chamberSimpleInAffinePart e C)
```

The premises are the Chapter 7 apartment axioms (the premise of the published
`AffineIwahoriTitsStatement`), the two normality facts that the published statement
concludes (normality of `P.normalizerZero` makes `P.affinePart` and
`P.affineTitsProjection` available), a chamber `C` of `A(S)`, and a multiplicative
equivalence `e` with all fields of `P.AffineIwahoriTitsWith C e`: `P_C ⊆ G(F)^0`, `e`
realizes the actual action of `N(F) ∩ G(F)^0` on `A(S)`, the Tits axioms for
`(P_C ∩ G(F)^0, N(F) ∩ G(F)^0)` with the geometric chamber-simple reflections, and the
corrected saturation formula. Here `P_C = P.parahoric C = Z(F)^0 · G(F)^♯_C` is the
group of KP Definition 7.4.1 constructed "by hand".

The conclusion is the existing predicate `IsBuildingTitsSystem` of KP Axiom 4.1.9,
for the same Weyl-group datum `π = P.affineTitsProjection` and generating set
`P.chamberSimpleInAffinePart e C`, with Borel subgroup
`I = P.chamberZeroStabilizerIn C`, the stabilizer in `G(F)^0` of the image of `C` in
`B(G)` (KP Definition 4.1.3). Its six fields are:

- `(I, N(F) ∩ G(F)^0)` is a Tits system in `G(F)^0` with Weyl-group datum `π` and
  generating set `Sgen` (TS 1–TS 4);
- `Sgen` is finite;
- the Tits system is saturated (TS 5);
- `Fc ↦ G(F)^0_{Fc}` is a bijection from the facets of `B(G)` (the `G(F)`-translates
  of the images of the facets of `A(S)` for `Ψ`) onto the admissible parabolic
  subgroups of the Tits system;
- the face relation of `B(G)` is reverse inclusion of these stabilizers;
- the apartments `h · A(S)` of `B(G)` correspond to the apartments of the restricted
  building.

Thus the statement contains the identification `I = P_C ∩ G(F)^0` of the Borel
subgroups, the identification of all facet stabilizers of the quotient with the
parabolic subgroups, and the matching of face relations and apartments.

## Source correspondence

The source is *Bruhat–Tits Theory: A New Approach* (2023),
`kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`, read with the
corrections of 1 November 2024, `kaletha-prasad-2024-corrections`, SHA-256
`23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`.

- Axiom 4.1.9 (printed p. 161 / PDF p. 192): `(I, N)` with `I = G(k)^0_C` and
  `N = N(k) ∩ G(k)^0` is a saturated Tits system in `G(k)^0` whose restricted
  building is `B(G)`; the stabilizers `G(k)^0_F` of facets are its parabolic
  subgroups.
- Theorem 7.5.3 (printed p. 261 / PDF p. 292) constructs the Iwahori–Tits system.
- Definition 7.6.1 (printed p. 263 / PDF p. 294) defines `B(G)` as the restricted
  building of the Iwahori–Tits system.
- Proposition 7.6.3 (printed pp. 264–265 / PDF pp. 295–296): `A` with its
  polysimplicial structure from `Ψ` realizes the standard apartment, and the
  parabolic subgroup attached to a facet `F ⊆ A` is the parahoric `G(k)^0_F`.
- Proposition 7.6.4(1) (printed p. 265 / PDF p. 296): for `Ω` in a facet, the group
  `G(k)^0_Ω` of Definition 7.4.1 is the stabilizer and the pointwise stabilizer of
  `Ω` in `G(k)^0`.
- Remark 7.6.5 (printed p. 266 / PDF p. 297): this completes the proof of Axioms
  4.1.1, 4.1.4 and 4.1.9, and by Proposition 4.4.4 the building is the quotient
  (7.6.2) of `G(k) × A`, unchanged when `G(k)^♯_x` is replaced by a larger subgroup of
  `G(k)_x`.
- Proposition 4.4.4 and Corollary 4.4.5 (printed p. 183 / PDF p. 214), with the
  correction of Corollary 4.4.5 (corrections PDF p. 29) requiring the comparison of
  stabilizers at every pair of corresponding points.
- Corrections, Chapter 7 (PDF p. 33): AS 5 is a standing Chapter 7 assumption; it is
  part of `P.apartment.SatisfiesApartmentAxioms P.centralizer`.

KP defines `B(G)` as the restricted building and then compares; the Library's
`B(G)` is the quotient (7.6.2). The statement therefore asks for the transfer of the
Tits-system description to the existing quotient, which is the content of
Propositions 7.6.3 and 7.6.4(1) and Remark 7.6.5.

## Scope

No full building validity, metric, polysimplicial realization, splitting or other
axiom is a premise. The data `P` are supplied; their existence is the separate
statement `ValuationApartmentAxiomsExistenceStatement`, and the Iwahori–Tits premise
is supplied by `AffineIwahoriTitsStatement`. The statement covers every universe,
both characteristics, and empty relative root systems, with no split, quasi-split,
rank, tameness or residue-size restriction.
