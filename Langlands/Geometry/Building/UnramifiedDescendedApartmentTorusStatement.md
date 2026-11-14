# The descended apartment's torus lies in the unramified apartment's torus

This module states, as the unproved proposition
`UnramifiedDescendedApartmentTorusStatement`, a comparison of tori behind KP's
unramified descent (Chapter 9). Let `S` be a maximal `F`-split torus of `G`, and let
`e` embed the reduced building of `G` over `F` into the reduced building of `G_K`
over the maximal unramified extension `K`, carrying the apartment `A(S)` into the
apartment `A(C.S)` of a maximal `K`-split torus `C.S`. Then `S_K ⊆ C.S`: the base
change to `K` of the inclusion `S → G` factors through the inclusion `C.S → G_K`.

The statement is derived (internal provenance). KP prove the corresponding facts
for special `k`-tori `T ⊇ S` (Propositions 9.3.11, 9.3.13 and 9.3.17), but they do
not state that every apartment of `B(G_K)` containing `A(S)` comes from a torus
containing `S_K`. The data `C`, `e`, `a` of the published
`Langlands.BruhatTits.IntegralModels.UnramifiedFacetCommonTorusStatement` are
arbitrary within its hypotheses, so `C.S` need not be a torus that KP construct.
The proof of the sign part of that statement needs this comparison, because it
compares weights of the special fibre of the torus of `S` with roots for `C.S`.

## Sources

The source is Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023),
registered as `kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732` (KP below).
Locators are printed page / PDF page.

- §9.2.2, p. 326 / p. 357: special `k`-tori, special `k`-apartments, and the
  bijection between maximal `K`-split tori of `G_K` and apartments of `B(G_K)`;
- §9.2.3, p. 326 / p. 357, Theorem 9.2.7 and Definition 9.2.8, p. 329 / p. 360:
  `B(G) = B(G_K)^Γ`, whose apartments are `A^Γ` for special `k`-apartments `A`;
- Proposition 9.3.4, p. 332 / p. 363: every maximal `k`-split torus lies in a
  special `k`-torus;
- Proposition 9.3.11, p. 337 / p. 368: (1) any two points of `B(G_K)_S^Γ` lie in
  the special `k`-apartment of one special `k`-torus containing `S`; (2) the fixed
  set `B(G_K)_S` of `S(K)^b` is the union of the apartments of the maximal `K`-split
  tori of `G_K` that contain `S_K`;
- Proposition 9.3.13, p. 338 / p. 369: if `T ⊇ S` is a special `k`-torus with
  special `k`-apartment `A`, then `B(G_K)_S^Γ = A^Γ`, and this is an affine space
  under `V(S')`. §9.3.14 calls it `A(S)`;
- Proposition 9.3.17, p. 340 / p. 371: `S ↦ B(G_K)_S^Γ` is a bijection from maximal
  `k`-split tori to apartments of `B(G)`. Its injectivity proof uses Lemma 2.2.8 in
  the way the proof sketch below does;
- Axiom 4.1.2, p. 158 / p. 189 (point stabilizers in `G(k)^1` are bounded), Axiom
  4.1.4, p. 158 / p. 189 (the torus acts on its apartment by translations), §4.1.28,
  p. 166 / p. 197 (where these axioms are proved for quasi-split groups), and
  Lemma 2.2.8, p. 71 / p. 102 (a vector with bounded orbit under a split torus is
  fixed). These are used only in the proof sketch.

KP must be read together with the authors' registered corrections,
`kaletha-prasad-2024-corrections` (version of 1 November 2024, SHA-256
`23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`; "corrections"
below, cited by PDF page). Several of their entries touch the cited items. None of
them changes a statement this module cites, but two change the proofs behind
Propositions 9.3.11 and 9.3.13:

- Corrections PDF p. 39, Section 9.3: in the second paragraph of the proof of
  Proposition 9.3.11, "Proposition 8.2.1(1)" becomes "Proposition 8.2.1(1), (5)",
  and "Proposition 9.3.5(2)" becomes "Proposition 9.3.5(1)". The statement of
  Proposition 9.3.11 is unchanged.
- Corrections PDF pp. 39–40, Section 9.3: new paragraphs are inserted just before
  Proposition 9.3.13. They construct the action of `V(S')` on `B(G_K)_S^Γ` and show
  that it does not depend on the special apartment used. The first argument uses
  Proposition 9.3.11 and the amended Proposition 9.3.12. The second, due to
  Tokimoto, extends the action of the lattice `Λ`, the image of `S'(k)` under the
  valuation homomorphism, to `ℚ · Λ` along geodesics and then to `V(S')` by
  continuity. The last paragraph of the proof of Proposition 9.3.13 is deleted. That
  paragraph derived this independence from the original Proposition 9.3.12, whose
  statement the same page amends (adding "contained in an apartment of `B(G)`" and
  removing two superscripts `Γ`). So the conclusions of Proposition 9.3.13 are
  unchanged. Its claim that `B(G_K)_S^Γ` carries a natural affine structure under
  `V(S')` now rests on the inserted construction.
- Corrections PDF p. 39, Section 9.2: the second full paragraph on p. 326 (in §9.2.1:
  Γ-orbits on `B(G_K)` are finite) is replaced by a corrected argument. A paragraph
  is added at the end of §9.2.1: a bounded Γ-stable subgroup of `G(K)` has a
  "Γ-stable fixed point" in `B(G_K)`, that is, a point fixed by the subgroup and by
  Γ. The text of §§9.2.2–9.2.3 is not changed.
- Corrections PDF p. 24, Section 2.2: §2.2 now assumes from its first paragraph that
  `k` is Henselian. The first sentence of the italicized paragraph at the end of
  p. 71 is deleted. In the book that sentence comes after Lemma 2.2.8 and introduces
  the Henselian assumption for the rest of the section. Lemma 2.2.8 itself is
  unchanged. The field `K` it is applied to in the sketch is Henselian.
- Corrections PDF pp. 27–28, Section 4.1: these entries correct AS 3, Remark 4.1.7,
  Axioms 4.1.8(2) and 4.1.9, the proof of Fact 4.1.25 and the axiom list of
  Definition 4.1.26 (which now includes Axioms 4.1.2 and 4.1.4), and they add a
  Remark 4.1.30. Axioms 4.1.2 and 4.1.4 and §4.1.28 are not changed. Corrections
  PDF p. 32 amends Lemma 6.1.26 and Definition 6.1.27, to which §4.1.28 refers for
  Axiom 4.1.4: "`x ∈ A(S)`" becomes "`φ ∈ A(S)`", and `S'`, `G^der` become `S_ad`,
  `G_ad`.
- There are no entries for Proposition 9.3.4, Proposition 9.3.17, Theorem 9.2.7 or
  Definition 9.2.8.

## Source context

In KP §§9.2–9.3, `k` is Henselian with maximal unramified extension `K` and
`Γ = Gal(K/k)`, and `B(G) = B(G_K)^Γ`. For a maximal `k`-split torus `S`, KP choose
a special `k`-torus `T ⊇ S` (a `k`-torus with `T_K` maximal `K`-split, Proposition
9.3.4). The special `k`-apartment `A` of `T_K` satisfies `A^Γ = B(G_K)_S^Γ`
(Proposition 9.3.13). This set is `A(S)`, with the affine structure under `V(S')`
that the corrections construct before Proposition 9.3.13. So `A(S)` lies in the
apartment of a maximal `K`-split torus containing `S_K`. By Proposition 9.3.11(2),
every point fixed by `S(K)^b` lies in the apartment of some maximal `K`-split torus
containing `S_K`, but that torus depends on the point. This module states a
converse for whole apartments: every maximal `K`-split torus whose apartment
contains `A(S)` contains `S_K`. (When the `k`-rank is smaller than the `K`-rank,
`A(S)` lies in many apartments of `B(G_K)`.) KP do not state this converse, and the
corrections do not add it.

## Lean statement

All declarations are in namespace `Langlands.Geometry.Building`, at the arbitrary
universe `u`. The module has one auxiliary declaration, the private instance
`unramifiedDescendedApartmentTorusAffineHom`. It says that the base change of an
affine group scheme along `F → inertiaFixedField F` is affine, by pullback
stability, and it is needed to form `MaximalUnramified.BuildingData`. It adds
nothing to the interface.

`UnramifiedDescendedApartmentTorusStatement.{u}` is a `Prop`-valued definition. Its
inputs are exactly the shared inputs of the published
`Langlands.BruhatTits.IntegralModels.UnramifiedFacetCommonTorusStatement` that
come before its facets and models:

- a nonarchimedean local field `F : Type u` (`Field`, `ValuativeRel`,
  `TopologicalSpace`, `IsNonarchimedeanLocalField`) and a group scheme `G` over
  `Spec F` with `IsAffineHom G.X.hom`;
- `P : ParahoricBuildingData G`, a polysimplicial realization `R` and an apartment
  splitting `T` of `B = P.toValuationBuildingData`, with the seven hypotheses
  `SatisfiesBuildingAxiom R`, `HasBoundedOpenStabilizers`,
  `SatisfiesAffineApartmentAxiom T`, `HasRootReflections`,
  `SatisfiesApartmentAxioms`, `HasCompatibleApartmentFacets` and `HasTitsSystem`.
  `P.S` with `P.i : P.S.toGrp ⟶ G` is the maximal `F`-split torus `S`, and
  `B.Apartment` is `A(S)`;
- with `K = inertiaFixedField F` (the maximal unramified extension):
  `C : MaximalUnramified.BuildingData F (baseChanged F K G)`, KP building data of
  `G_K` with maximal `K`-split torus `C.i : C.S.toGrp ⟶ G_K` and apartment
  `C.Apartment = A(C.S)`; `A : MaximalUnramified.SemilinearApartmentData C`; a map
  `e : B.ReducedBuilding → C.ReducedBuilding`; and a real affine map
  `a : B.Apartment →ᵃ[ℝ] C.Apartment`;
- the eight hypotheses of that statement on `C`, `A`, `e`, `a`:
  1. `e` is injective;
  2. `e (g • z) = rationalExtend F K G g • e z` for every `g ∈ G(F)`;
  3. `e (B.apartmentMap w) = C.apartmentMap (a w)` for every `w : B.Apartment`;
  4. every `A.action σ` fixes every point `e z`;
  5. every point fixed by all `A.action σ` is some `e z`;
  6. if `e z` is a special point of `C`, then `z` is a special point of `B`;
  7. `a ⁻¹' facet C.affineRoots (a w) = facet B.affineRoots w` for every `w`;
  8. every `s` in `characterValuationKernel (MaximalUnramified.valuation F)` of
     `baseChanged F K P.S.toGrp` (the maximal bounded subgroup `S(K)^b`), mapped to
     `G(K)` by the base change of `P.i`, fixes `e (B.apartmentMap w)` for every `w`.

The conclusion is

```lean
∃ f : baseChanged F (inertiaFixedField F) P.S.toGrp ⟶ C.S.toGrp,
  f ≫ C.i = (GroupScheme.baseChange (baseMap F (inertiaFixedField F))).map P.i
```

a group-scheme homomorphism `f : S_K → C.S` through which the base change
`S_K → G_K` of `P.i` factors. Since `C.i` is a monomorphism (it is a closed
immersion, being the inclusion of a maximal split torus), such an `f` is unique.
The statement asserts no property of `f` beyond the factorization. For example,
it does not say how `a` relates to the induced map on cocharacter spaces; a
consumer derives that from hypotheses 2 and 3.

## Why the hypotheses describe the source's situation

As explained in the Markdown of `UnramifiedFacetCommonTorusStatement`, hypotheses
1–8 are the properties of KP's inclusion `B(G) = B(G_K)^Γ ⊂ B(G_K)` (Theorem
9.2.7, Definition 9.2.8) that its consumers use. By hypothesis 3, `e` carries
`A(S)` into the image of `A(C.S)`. The statement quantifies over every `C`, `A`,
`e`, `a` with these properties. In KP's situation, `C` is the building data of
`G_K` for a maximal `K`-split torus whose apartment contains `A(S)`; one such torus
is `T_K` for a special `k`-torus `T ⊇ S`, but the statement covers all of them. The
seven hypotheses on `P` and hypotheses 1, 4–7 are not used in the sketch below. They
are kept so that the statement has exactly the inputs of its consumer; a prover may
use them.

## Proof sketch (why the statement is true)

This is the intended route; it follows the injectivity argument of KP Proposition
9.3.17.

1. `S(K)` stabilizes `Y = e(A(S))`. The group `S(F)` acts on `A(S)` by
   translations (Axiom 4.1.4), so by hypotheses 2 and 3 its image in `G(K)`
   stabilizes `Y`. By hypothesis 8, `S(K)^b` fixes `Y` pointwise. Since `S` is
   `F`-split and a uniformizer of `F` is one of `K`, `S(K) = S(F) · S(K)^b`.
2. The maximal bounded subgroup `C.S(K)^b` fixes `A(C.S)` pointwise (it acts by
   translation by `ν(t) = 0`), so it fixes `Y` pointwise.
3. For `t ∈ C.S(K)^b` and `s ∈ S(K)`, `s t s⁻¹` lies in `G(K)^1` (a normal subgroup
   containing `t`) and fixes `s · Y = Y` pointwise. So the conjugation orbit
   `{s t s⁻¹ | s ∈ S(K)}` lies in the stabilizer in `G(K)^1` of a point of `Y`,
   which is bounded (Axiom 4.1.2 for the quasi-split group `G_K`, verified as listed
   in §4.1.28, p. 166 / p. 197). The Library's
   `IntegerValuationBuildingData.isAlgebraicallyBounded_oneStabilizer` proves this
   boundedness for building data such as `C`, given bounded `Z(K)^1` and bounded
   depth-zero root groups.
4. By Lemma 2.2.8 (applied to the conjugation action of `S_K` through a faithful
   representation, as in the proof of Proposition 9.3.17), `S_K` centralizes `t`.
   `C.S(K)^b` is Zariski dense in the split torus `C.S`, so `S_K` centralizes
   `C.S`.
5. Then `S_K · C.S` is a `K`-split torus containing `C.S`, so it equals `C.S` by
   maximality. Hence `S_K ⊆ C.S`, which gives the factorization.

## Intended consumer

Task 6320 (`0d9f960a-6d9d-4ba2-bc9b-3c0a847189c2`) proves the published
`UnramifiedFacetCommonTorusStatement`. Its sign part is deduced from a statement
over `O` in the coordinates of `C.S` (KP Theorem 8.4.19(2), as in §9.5). That
deduction restricts characters of `C.S` to `S_K` and needs this inclusion.
