# Axiom 4.1.16 for the building of a valuation of the root datum

`Langlands.Geometry.Building.IwahoriDecompositionAxiomStatement` is a
Prop-valued `def` at every universe `u`. It says that the existing building of
supplied valuation data satisfies Kaletha–Prasad Axiom 4.1.16 (Iwahori
decomposition), under the hypotheses of KP Chapter 7 as corrected in 2024.
The module supplies no proof.

## Statement

The proposition quantifies over:

- every nonarchimedean local field `F`, of either characteristic;
- every group scheme `G` over `Spec F` with `[IsAffineHom G.X.hom]`;
- every `P : ParahoricBuildingData G`. These are the Library's building data:
  a maximal split torus `i : S → G`, the class `A(S)` of valuations of the
  root datum of `(G, S)` normalized by the valuation of `F`, the actual
  centralizer `Z = Z_G(S)` with axiom V 6 on `Z(F)`, and the data of KP
  Definition 2.6.23 for `Z(F)^0` and `G(F)^0`. Connected reductivity of `G`
  is a field of the data.

Its single premise is `P.SatisfiesApartmentAxioms`, which unfolds to
`P.apartment.SatisfiesApartmentAxioms P.centralizer`. Since V 6 is part of
the data, the premise asks for V 7 (the root filtrations are compatible with
the topology of `G(F)`, KP Definition 6.1.2) and AS 2–AS 5 of KP Axiom 4.1.6
for the class `A(S)`.

The conclusion is `P.HasIwahoriDecomposition`, from
`Langlands.Geometry.Building.FullValidity.ChamberAxioms`. It asks, for every
chamber `C` of `A(S)` for the affine roots `Ψ = P.affineRoots`
(`AffineRootSystem.IsChamber`) and every cocharacter `ν` of `S` that is
generic (`IsGenericCocharacter`, so that `{a | ⟨a, ν⟩ > 0}` is a positive
system of roots), for `P.IsIwahoriDecompositionAt C ν`. Let
`I = P.zeroStabilizer` of the image of `C` in the building
`B(G) = P.toValuationBuildingData.ReducedBuilding`: the elements of
`G(F)^0 = P.zeroSubgroup` that stabilize this image as a set. Let `U^+` and
`U^-` be the actual dynamic unipotent radicals `U(ν)` and `U(-ν)`. The five
fields of `IsIwahoriDecompositionAt C ν` are:

1. the product map `(U^+(F) ∩ I) × Z(F)^0 × (U^-(F) ∩ I) → G(F)`,
   `(u, z, v) ↦ u · z · v`, with `Z(F)^0` mapped by the centralizer inclusion,
   is injective;
2. its image is `I`;
3. for every non-divisible root `a` there is a smallest affine functional
   `ψ_a` on `A(S)` with derivative `a` that is non-negative on `C`, for the
   pointwise order among all affine functionals with derivative `a`
   (`IsLeastNonnegativeFunctional`);
4. for these `ψ_a` and every enumeration without repetition
   `a_0, …, a_{n-1}` of the non-divisible roots `a` with `⟨a, ν⟩ > 0`, the
   ordered product `U_{ψ_{a_0}} × ⋯ × U_{ψ_{a_{n-1}}} → G(F)` is injective with
   image `U^+(F) ∩ I` (`IsOrderedRootProductBijective C ν`);
5. the same for `-ν`, the negative roots and `U^-(F) ∩ I`.

## Source correspondence

The source is Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023),
`kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`.

- Axiom 4.1.16, printed p.162 / PDF p.193: for a maximal split torus `S`
  with apartment `A`, a chamber `C ⊂ A` and `I = G(k)^0_C`, for any positive
  system of roots `Φ^+` "the product map
  `(U^+(k) ∩ I) × Z(k)^0 × (U^-(k) ∩ I) → I` is bijective". "Moreover, the
  product map `∏_{a ∈ Φ^{±,nd}} U_{ψ_a} → U^±(k) ∩ I` is a bijection, where
  the product is taken in any order, and for any non-divisible root `a`,
  `ψ_a` is the smallest affine functional on `A` with derivative `a` that is
  non-negative on `C`." Here `G(k)^0_C` is the stabilizer of `C` in `G(k)^0`
  (Definition 4.1.3).
- KP 4.1.28, printed p.166 / PDF p.197: "Axiom 4.1.16 is proved in
  Corollary 7.4.9" for the Chapter 7 building.
- Corollary 7.4.9, printed p.257 / PDF p.288: for a chamber `C`, `x ∈ C` and
  a positive system `Φ^+`, `N^♯_x = Z^♯_x` and
  `G(k)^♯_C = ∏_{a ∈ Φ^{-,nd}} U_{a,x,r} · Z^♯_x · ∏_{a ∈ Φ^{+,nd}} U_{a,x,r}`
  for `r = 0` or `0+`. Its proof applies Proposition 7.3.12, printed p.250 /
  PDF p.281, whose parts (3) and (5) give bijectivity of these products in
  any fixed order of the factors.
- Proposition 7.6.4 (1), printed p.265 / PDF p.296: for a subset `Ω` of a
  facet, the group `G(k)^0_Ω` built by hand in Definition 7.4.1 "is the
  stabilizer, as well as the pointwise stabilizer, of `Ω` in `G(k)^0`". It
  identifies KP's `I` with `P_C = Z(k)^0 · G(k)^♯_C`.
- The standing hypotheses of Chapter 7 are at its opening, printed p.235 /
  PDF p.266: `k` is Henselian with a discrete valuation (the residue field
  need not be perfect), `G` is connected reductive, Axiom 4.1.4 holds, and
  each `A(S)` is an equipollence class of valuations of the root datum of
  `(G, S)` with the action of `N(k)` of §6.1.8.

The authors' corrections of 1 November 2024,
`kaletha-prasad-2024-corrections`, SHA-256
`23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`:

- PDF p.27 puts Axiom 4.1.16 into the list of Definition 4.1.26.
- PDF p.33: at the end of the second paragraph of Chapter 7 the authors add
  that AS 1–AS 4 are proved in §6.3 and that "We will assume in addition that
  assertion AS 5 holds."
- PDF pp.33–34 add Proposition 7.3.12 (6), which allows an arbitrary ordering
  of all roots under the extra hypothesis `f(0) > 0`. Axiom 4.1.16 orders the
  roots of one sign only, so this addition is not needed here.

## Derived scope and provenance

This is a derived formulation, not a literal transcription.

- **Field.** The statement covers nonarchimedean local fields, of mixed and
  equal characteristic. Their valuation rings are Henselian and their
  valuations discrete. Other fields allowed by KP Chapter 7 are not covered.
- **The building.** KP Chapter 7 builds `B(G)` from the Iwahori–Tits system
  of Theorem 7.5.3 (Definition 7.6.1). Remark 7.6.5, printed p.266 / PDF
  p.297, realizes it as the quotient (7.6.2) of `G(k) × A`. Here the building
  is the Library's quotient `P.toValuationBuildingData.ReducedBuilding`, with
  its existing action of `G(F)`, and `I` is the stabilizer in `G(F)^0` of the
  image of `C`.
- **Hypotheses.** The premise is the Library predicate
  `SatisfiesApartmentAxioms`. It contains AS 5, which the corrected Chapter 7
  assumes, and AS 2–AS 4, which KP prove in §6.3 for every valuation. It
  also contains V 7, which is not among the standing hypotheses of Chapter 7.
  The statement is therefore weaker than KP's by this extra premise. V 6 is
  part of the data `P`; the opening of Chapter 7 does not list it. The
  premise matches that of the published Chapter 7 statements
  `ParahoricBuildingData.ChamberIwahoriDecompositionStatement` and
  `AffineIwahoriTitsStatement`.
- **One apartment.** KP's axiom concerns every maximal split torus `S` and
  its apartment. The Library predicate concerns the torus and apartment of
  the data `P`. The statement quantifies over all `P`, so it covers every
  maximal split torus for which data are supplied.
- **Positive systems.** A positive system of roots is given by a generic
  cocharacter `ν`, and `U^±` are the dynamic unipotent radicals `U(±ν)`.

No existence of the data, and no other axiom, is asserted. Together with the
published `RootValuationBuildingConstructionStatement`, whose conclusion
includes `P.SatisfiesApartmentAxioms`, this statement would supply Axiom 4.1.16
for the data of that construction. It is one of the certificate items of the
published `BruhatTitsAvailabilityStatement` (KP Theorem 9.2.7 with corrected
Definition 4.1.26).

## Expected proof route (not prescribed)

1. Proposition 7.6.4 (1) for the chamber: `I` equals the Chapter 7 Iwahori
   subgroup `P.chamberIwahori C = P_C`. In KP the stabilizer of a facet in
   `G(k)^0` is a parabolic subgroup of the Iwahori–Tits system of Theorem
   7.5.3 and fixes the facet pointwise (Proposition 1.5.13). On the Library's
   quotient, the stabilizer of the image of a point `x ∈ A(S)` is
   `G(F)^♯_x · N(F)_x` (`ApartmentQuotient.mem_stabilizer_apartment_iff`),
   and the published `chamberParahoricNormalizer` (`P_C ∩ N(F) ⊆ Z(F)^0`,
   KP Lemma 7.5.2 (1)) controls the normalizer part.
2. The published proof of
   `ParahoricBuildingData.ChamberIwahoriDecompositionStatement`
   (Task `0e645cc1`, KP Corollary 7.4.9 with its full-Iwahori
   consequences) supplies the bijective products onto `P.chamberIwahori C`
   with the `Z(F)^0` factor, in every order of the roots of each sign.
3. Identify its factors with `U^±(F) ∩ I` and with the groups `U_{ψ_a}`:
   for `x ∈ C`, `U_{a,x,0} = U_{a,C,0}` (Lemma 6.3.20, printed p.222 / PDF
   p.253), which is `U_{ψ_a}` for the smallest functional `ψ_a`.
   `standardUnipotent_empty_eq_dynamic` compares the standard and dynamic
   unipotent radicals.
