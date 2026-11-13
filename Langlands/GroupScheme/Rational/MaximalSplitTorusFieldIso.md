# Maximal split tori under isomorphisms of fields

This internal lemma supports the proof of Kaletha–Prasad Axiom 4.1.17
(compatibility with isomorphisms). It is the split-torus analogue of the
Library theorem `IsMaximalTorus.baseChange_fieldIso` (module
`Langlands.GroupScheme.Torus.MaximalFieldIso`).

## Statement

`IsMaximalSplitTorus.baseChange_fieldIso (hi : IsMaximalSplitTorus i) (e : k ≃+* K)`:
let `i : T → G` be a maximal split torus of a group scheme `G` over a field `k`,
and let `e : k ≃+* K` be a ring isomorphism. Pull back along
`b = Spec e : Spec K → Spec k`. Then `i_K : T_K → G_K` is a maximal split torus
of `G_K`.

The proposition follows from the Library definition `IsMaximalSplitTorus`
(module `Langlands.GroupScheme.Rational.SplitTorus`): a split torus that is a
closed subgroup, and through which every factorization `f ≫ i' = i` by a split
subtorus `i'` has `f` an isomorphism. Nothing beyond this definition is assumed.

## Provenance

This is a derived fact with no separate literature statement: an isomorphism
of fields induces an equivalence of the categories of group schemes, and an
equivalence preserves the defining property. It provides hypothesis `hmax` of
`ValuationBuildingData.exists_isEquivariantBuildingIso_of_fieldExtension` when
the field extension is an isomorphism `σ : F₁ ≃+* F₂`.

## Proof

Write `a = Spec e⁻¹ : Spec k → Spec K`. Then `a ≫ b = 𝟙` and `b ≫ a = 𝟙` by
functoriality of `Spec`.

- **Split subtorus.** `T_K` is split by `IsSplitTorus.baseChange`. `i_K` is a
  closed subgroup by `IsClosedSubgroup.baseChange`.
- **Maximality.** Let `i' : T' → G_K` be a split subtorus over `K` and
  `f : T_K → T'` satisfy `f ≫ i' = i_K`. Pull everything back along `a`. The
  Library comparison `baseChangeSectionIso b a ha G : (G_K)_a ≅ G`
  (`Langlands.GroupScheme.Torus.SplitDescent`) is natural in `G`. This is
  `RadicalFieldTransport.sectionIso_naturality`, in
  `Langlands.GroupScheme.SectionComparisonNaturality`. Put
  `i₀ = i'_a ≫ (baseChangeSectionIso b a ha G).hom`. It is a split subtorus of
  `G`, by `IsSplitTorus.baseChange`, `IsClosedSubgroup.baseChange` and
  `IsClosedSubgroup.comp_iso`. Put
  `f₀ = (baseChangeSectionIso b a ha T).inv ≫ f_a`. Functoriality, `f ≫ i' = i_K`
  and naturality give `f₀ ≫ i₀ = i`, so `f₀` is an isomorphism by maximality of
  `i`. Hence `f_a` is an isomorphism.
- **Returning to `K`.** Naturality of `baseChangeSectionIso a b hb` (with the
  roles of `a` and `b` exchanged) writes `f` as
  `(baseChangeSectionIso a b hb T_K).inv ≫ (f_a)_b ≫ (baseChangeSectionIso a b hb T').hom`.
  This is a composite of isomorphisms, so `f` is an isomorphism.

The proof uses no flatness or descent; it only uses that base change along `b`
is inverted by base change along `a`.
