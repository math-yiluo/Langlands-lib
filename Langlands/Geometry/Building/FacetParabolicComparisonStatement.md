# The apartment-only common-chamber facet-parabolic proof target

`Langlands.Geometry.Building.FacetParabolicComparisonStatement.{u}` is a
distinct named Prop-valued `def`, for arbitrary universe `u`. It is the
common-chamber proof target for both facet comparisons of KP Proposition
7.5.5, using one actual affine Iwahori–Tits datum. It proves no structural
assertion or double-coset bijection.

The original source is Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach*
(2023), `kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`,
Proposition 7.5.5, printed pp. 261–262 / PDF pp. 292–293, together with
Theorem 7.5.3 at PDF p. 292. The consumer is Theorem 7.8.1(3), PDF
pp. 303–304. The 1 November 2024 corrections,
`kaletha-prasad-2024-corrections`, SHA-256
`23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`,
PDF pp. 33–36, correct the Chapter 7 assumptions and the adjacent
7.8.1(2) injectivity argument; Proposition 7.5.5 is unchanged.

## Exact premises and conclusion

The input context and premises are literally those of the unchanged
`ParahoricDoubleCosetStatement`:

```text
∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
  (P : ParahoricBuildingData G),
  P.apartment.SatisfiesApartmentAxioms P.centralizer →
    ∀ C F₁ F₂ : Set P.Apartment, AffineRootSystem.IsChamber P.affineRoots C →
      AffineRootSystem.IsFaceOf P.affineRoots F₁ C →
      AffineRootSystem.IsFaceOf P.affineRoots F₂ C →
      ∃ (_ : P.normalizerZero.Normal) (_ : P.zeroSubgroup.Normal),
        P.CommonChamberFacetParabolics C F₁ F₂.
```

The only geometric hypothesis is the apartment-axiom predicate, followed by
the chamber and the two common-chamber face premises. Normality of both
actual subgroups is concluded. Normality of `P.normalizerZero` permits the
quotient operations in the fixed-data predicates; normality of
`P.zeroSubgroup` is retained for the full component-group consumers.

The final predicate existentially supplies one multiplicative equivalence
`e : P.affinePart ≃* AffineRootSystem.affineWeylGroup P.affineRoots` and
asserts

```text
P.AffineIwahoriTitsWith C e ∧
P.FacetParabolicComparisonWith C F₁ e ∧
P.FacetParabolicComparisonWith C F₂ e.
```

Thus the actual Tits system, its representative-compatible apartment action,
the geometric chamber-simple reflections and saturation are conclusions.
For each `Fa = F₁, F₂`, with
`X = P.facetSimpleInAffinePart e C Fa`, the additional conclusions include

```text
P.parahoric Fa ≤ P.zeroSubgroup,
(Subgroup.closure X).map P.affinePart.subtype = P.affineFacetStabilizer Fa,
↑(P.parahoricInZero Fa) =
  TitsSystem.standardParabolic (P.parahoricInZero C) P.affineTitsProjection X.
```

The subset `X` uses precisely the chamber-simple affine roots vanishing on
`Fa`. Its closure is mapped into the full `P.IwahoriWeylGroup`, so the existing
affine facet stabilizers and all components are preserved. The standard
parabolic is the union of the Iwahori cells indexed by that closure, with
`P.affineTitsProjection` the literal restricted normalizer quotient.

The fixed-data lemma `FacetParabolicComparisonWith.parahoric_image`
identifies the restricted subgroup with the generated full `P.parahoric Fa`
under the actual inclusion in `rationalPoints G`; its
`parahoric_eq_bruhat_cells` lemma gives the full-group cell union.
These are explicit subtype adapters. No comparison with the distinct
pointwise zero-fixer is assumed or hidden in notation. The setwise facet
stabilizer remains distinct from the generated full parahoric.

## Future proof obligations

The statement retains normality, the actual Tits realization, the
facet-generated stabilizer theorem and the standard-parabolic equality as
conclusions to be proved. It supplies no generic geometric generation or
chamber-transitivity proof.

The unchanged global `ParahoricDoubleCosetStatement` still needs the generic
parabolic double-coset result applied to this actual datum and its extension
over all components, with normalization comparisons and the prescribed
value on every representative in the full normalizer. The corresponding
Iwahori bijection also remains unproved. The actual-action kernel, range and
component-surjectivity inputs remain separately retained obligations where
not already available from an accepted proof.

The future validity predicate for corrected Axiom 4.1.9 is not a discharger
for either this apartment-only statement or the unchanged global
double-coset targets. No full building validity, normality, Tits realization,
facet comparison or decomposition conclusion has been added as a global
premise.
