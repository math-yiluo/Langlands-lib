# The apartment-only affine Iwahori–Tits proof target

`Langlands.Geometry.Building.AffineIwahoriTitsStatement.{u}` is a named
Prop-valued `def`, for arbitrary universe `u`. It is a proof target, not a
theorem. It records the `G(F)^0` branch of Kaletha–Prasad Theorem 7.5.3(1),(2)
with all actual objects and geometric simple reflections supplied by
`AffineIwahoriTits` and `AffineChamberReflections`.

The source is *Bruhat–Tits Theory: A New Approach* (2023),
`kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`,
Theorem 7.5.3, printed p. 261 / PDF p. 292, with Lemma 7.5.2 on PDF
pp. 291–292. The 1 November 2024 corrections,
`kaletha-prasad-2024-corrections`, SHA-256
`23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`,
PDF pp. 33–35, correct the opening Chapter 7 assumptions, the affine Weyl
comparison and the saturation formula. The original generic saturation
definition is KP Definition 1.4.1.

## Exact scope

The universal input context is literally the context of the unchanged
`IwahoriDoubleCosetStatement`:

```text
∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
  (P : ParahoricBuildingData G),
  P.apartment.SatisfiesApartmentAxioms P.centralizer →
    ∀ C : Set P.Apartment, AffineRootSystem.IsChamber P.affineRoots C →
      ∃ (_ : P.normalizerZero.Normal) (_ : P.zeroSubgroup.Normal),
        P.AffineIwahoriTits C.
```

The only geometric premise is the published apartment-axiom predicate, followed
by the existing chamber premise. No full building-validity predicate,
normality witness, quotient-action identification, generation condition or
double-coset conclusion is a premise.

Both normality witnesses are conclusions. Normality of `P.normalizerZero`
permits the fixed-data quotient group operations; normality of `P.zeroSubgroup`
is retained as an actual-group conclusion for the full component-quotient
consumers. The predicate `P.AffineIwahoriTits C` then existentially supplies a
multiplicative equivalence
`e : P.affinePart ≃* AffineRootSystem.affineWeylGroup P.affineRoots`
and all fields of `P.AffineIwahoriTitsWith C e`:

- the generated full `P.parahoric C` lies in `P.zeroSubgroup`;
- `e (P.affinePartMk n)` equals the actual
  `P.apartment.normalizerAffineEquiv n` for every representative;
- the published `Langlands.Group.IsTitsSystem` holds for the actual restricted
  groups, quotient projection and geometric chamber-simple reflections;
- the corrected saturation equality
  `⨅ n : P.normalizerInZero, B.map (MulAut.conj ↑n).toMonoidHom
    = B ⊓ P.normalizerInZero` holds, where `B = P.parahoricInZero C`.

The paired fixed-data module spells out every restriction, projection and
subtype identity. These are internal adapters of the actual objects. The
statement does not replace the generated full parahoric by a pointwise fixer,
or the Weyl group by an unrelated abstract group.

## Retained proof obligations

No proof is supplied for normality, the action comparison, the geometric
generation assertions, the Tits axioms or saturation. The separate
`G(F)^♮` branch and choice-independence assertion of 7.5.3 are outside this
target. Facet stabilizer and parahoric comparisons belong to the distinct
`FacetParabolicComparisonStatement`.

For the unchanged global `IwahoriDoubleCosetStatement` and
`ParahoricDoubleCosetStatement`, future proofs must also supply the actual
component extension, normalizing chamber representatives, generic Bruhat and
parabolic transports, and the prescribed values on every full normalizer
representative. This proposition is a structural prerequisite, not a proof of
either closing target. The future validity predicate for corrected Axiom
4.1.9 does not discharge an apartment-only Chapter 7 target by adding a
stronger premise.
