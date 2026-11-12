# Existence of the actual affine apartment splitting of KP Axiom 4.1.4

`Langlands.Geometry.Building.ActualApartmentSplittingStatement.{u}` is a named
Prop-valued `def` at an arbitrary universe `u`. It is a proof target, not a theorem.
It asserts that the affine structure of the apartment of actual valuation-building
data satisfies KP Axiom 4.1.4, with actual derived subgroup, derived torus and split
central torus.

## Statement

```text
∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] (G : GroupScheme (Spec (CommRingCat.of F)))
  [IsAffineHom G.X.hom] (B : ValuationBuildingData G),
  B.SatisfiesApartmentAxioms →
    ∃ T : B.ApartmentSplitting, B.SatisfiesAffineApartmentAxiom T
```

`B.ApartmentSplitting` is the existing structure of supplied data: a group scheme
`D` with `d : D → G`, a commutative group scheme `S'` with `j : S' → D` and
`e : S' → S`, and a commutative group scheme `A_G` with `a : A_G → S`.
`B.SatisfiesAffineApartmentAxiom T` is the existing predicate whose fields are

- `d` exhibits the derived subgroup of `G` (`IsDerivedSubgroup`);
- `j` is a maximal split torus of `D`, `e` is a closed immersion and
  `j ≫ d = e ≫ i`, so `S'` is the maximal subtorus of `S` contained in `G_der`;
- `a ≫ i` is the split component `A_G` of `G` (`IsSplitComponent`);
- (A 0) `V(S) = V(S') ⊕ V(A_G)`, as complementary ranges of the real cocharacter maps
  of `e` and `a`;
- (A 1) every element of `N(F)` preserves `S'`, and every element of `N(F)` lying in
  the centre of `G(F)` acts trivially on `A(S)`;
- (A 2) `B.HasAffineConjugations`.

The premise `B.SatisfiesApartmentAxioms` (V 6, V 7 and AS 2–AS 5 for the class of `B`)
is the standing hypothesis of KP Chapter 7, in whose setting the source proves the
axiom. The conclusion is about the given `B`, its torus `S` and its existing
`N(F)`-action on `A(S)`; nothing is replaced.

The clauses of (A 1) not listed above are built into `B` or proved for every `B` in
the Library: `N(F)` acts by affine automorphisms with derivative the Weyl action
(`normalizerAction_linear`), and `Z(F)` acts by the translations `ν(z)`. Given the
splitting, the Library derives `A(S)` as an affine space under `V(S')`
(`derivedTranslationEquiv`) and the translation formula through the projection
`V(S) → V(S')`.

## Source correspondence

The source is *Bruhat–Tits Theory: A New Approach* (2023),
`kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`.

- Axiom 4.1.4 (printed pp. 158–159 / PDF pp. 189–190): `S'` is the unique maximal
  subtorus of `S` contained in `G_der`, `A_G` the maximal split torus in the centre,
  `V(S) = V(S') ⊕ V(A_G)` canonically; A 0 (affine space under `V(S')`), A 1
  (affine action of `N(k)` with derivative the Weyl action on `X_*(S')`, `Z(k)`
  acting by `ν(z)`, and the centre acting trivially), A 2 (conjugation maps between
  apartments are affine with the natural derivative).
- 4.1.28 (printed p. 166 / PDF p. 197): for quasi-split groups, A 0 and A 2 hold by
  construction and A 1 is Lemma 6.1.26.
- Remark 7.6.5 (printed p. 266 / PDF p. 297): Proposition 7.6.4 completes the proof
  of Axioms 4.1.1, 4.1.4 and 4.1.9 for the Chapter 7 building, the quotient (7.6.2) of
  `G(k) × A`.
- §9.5 (printed p. 363 / PDF p. 394): for general `G`, Axiom 4.1.4 is
  Proposition 9.3.16.

## Scope

The statement covers all connected reductive groups over nonarchimedean local
fields that admit such data, at every universe, in both characteristics, with no
split, quasi-split, rank, tameness or residue-size restriction. Existence of the data
`B` is the separate statement `ValuationApartmentAxiomsExistenceStatement`. The
`IsAffineHom` instance is an argument; connected reductivity of `G` is a field of
`B`.
