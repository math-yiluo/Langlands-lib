# Cohomology of the derived comparison for compactly supported cohomology

Author: Worker 26. Completes Worker 26's
`Langlands.Cohomology.DiscreteSheafDerivedComparison`. That module identifies the
cohomology of the last two factors of `compactComplexComparison` but not of
its first factor, the exact postcomposition isomorphism. Uses
`Langlands.Cohomology.LeftExactHomology` (`toCycles`, `homologyHom`,
`homologyNatTrans`, `derivedHom`, `derivedNatTrans`),
`Langlands.Cohomology.DerivedExactComposition` (`homologyπ_mapHomologyIso_hom`,
`rightDerivedCompIsoOfResolution`, `derivedCompIso`, `derivedCompIso_hom_homology`,
`mapDerivedCategoryHomologyIso`) and
`Langlands.Cohomology.AcyclicResolution.DerivedComparisonComposite`
(`derivedComplexCongr_refl_hom_app`).

## Exact functors

Let `Φ : D ⥤ E` be an additive functor between abelian categories that
preserves finite limits and finite colimits.

- `mapCyclesIso_hom_comp_toCycles`: for a short complex `S`, Mathlib's cycles
  comparison `(S.mapCyclesIso Φ).hom` followed by `LeftExactHomology.toCycles Φ S`
  is the identity. Both maps are compatible with the inclusions of cycles, and
  the inclusion of cycles is a monomorphism.
- `homologyHom_eq_mapHomologyIso_hom`: `LeftExactHomology.homologyHom Φ S` is
  Mathlib's homology comparison `(S.mapHomologyIso Φ).hom`. Both maps agree
  after the projection to homology. The first is `inv (toCycles Φ S)` followed by
  `Φ` of the projection (`homologyπ_homologyHom`). The second is the cycles
  comparison followed by `Φ` of the projection (`homologyπ_mapHomologyIso_hom`).
  These agree by the previous lemma.

For an additive `G : C ⥤ D`, where `C` has injective resolutions, and an
injective resolution `I` of `X`:

- `rightDerivedCompIsoOfResolution_refl_hom_comp_derivedHom`: the classical
  comparison `(DerivedPlus.rightDerivedCompIsoOfResolution G Φ (Iso.refl (G ⋙ Φ)) I n).hom`,
  from `Φ (Rⁿ G X)` to `Rⁿ (G ⋙ Φ) X`, followed by
  `LeftExactHomology.derivedHom Φ G I n` is the identity. The proof unfolds both
  maps through `I.isoRightDerivedObj`. The termwise isomorphism for the identity
  of `G ⋙ Φ` is the identity. The remaining homology maps cancel by the
  previous lemma.
- `rightDerivedCompIsoOfResolution_refl_hom_comp_derivedNatTrans`: the same
  for Mathlib's chosen resolution, with `(LeftExactHomology.derivedNatTrans Φ G n).app X`.

## The comparison on a twisted site

Setting and notation of `DiscreteSheafDerivedComparison`. Its variables are
repeated in the same order: the twisted site from `C`, `P`, `X`, `ρ`, `J` and the
group `G`, `R : Type w`, `L`, the sheafification, refinement, Kan-extension and
enough-injectives hypotheses, points `Φ : I → J.Point.{w}` with the action
hypotheses, and derived categories in universes `w₁`–`w₄`.

- `compactComplexForgetHomologyIso J R L E F n`: the degree `n` cohomology of
  `(smoothForget R G).mapDerivedCategory` applied to the image of
  `(compactComplex J R L E).obj F` in the derived category is
  `(smoothForget R G).obj ((discreteCompactDerived J R L E n).obj F)`, the module
  underlying the smooth compactly supported cohomology. It is the published
  `mapDerivedCategoryHomologyIso (smoothForget R G) n` (the cohomology of the
  forgetful image of a complex is the forgetful image of its cohomology),
  followed by `smoothForget` applied to the published `compactComplexHomologyIso`.
- `compactComplexComparison_homology E F n`: the degree `n` cohomology of
  `(compactComplexComparison J R L E).app F`, followed by the published
  `sheafCompactComplexHomologyIso` for the target, equals
  `(compactComplexForgetHomologyIso J R L E F n).hom` followed by
  `(compactComparison J R L E n).app F`. It is a regrouping of
  `compactComplexComparison_homology_eq`, which states the same identity with
  the two isomorphisms written out.
- `compactComplexComparison_homology_eq E F n`: the degree `n` cohomology of
  `(compactComplexComparison J R L E).app F`, followed by
  `DerivedPlus.homologyIso` for the target, equals
  the published `mapDerivedCategoryHomologyIso (smoothForget R G) n`, then
  `smoothForget` applied to `DerivedPlus.homologyIso` for the source, then
  `(compactComparison J R L E n).app F`. Both `homologyIso`s are computed with
  Mathlib's chosen injective resolutions. The first identification says that the
  cohomology of the forgetful image of a complex is the forgetful image of its
  cohomology.
  The proof:
  1. `derivedCompIso` for the identity isomorphism is `derivedPostcompIso`,
     since `derivedComplexCongr (Iso.refl _)` is the identity.
  2. The published `derivedCompIso_hom_homology` gives the cohomology of
     the first factor, up to the classical comparison for `Iso.refl`.
  3. `inclusionRestrictionComparison_homology` gives the cohomology of the
     other two factors, starting with `derivedNatTrans`.
  4. The previous theorem cancels the classical comparison against
     `derivedNatTrans`.

So, after the stated identifications, `compactComplexComparison` induces in every
degree `n ≥ 0` the degree-wise map `compactComparison J R L E n`. It is not
proved that these maps are isomorphisms.

## Provenance and scope

Derived infrastructure. As recorded in `TwistedCompactComparison` and
`DiscreteSheafDerivedComparison`, `compactComparison J R L E q` has the shape
of Berkovich's maps `H^q_c(X{G}, F) → H^q_c(X, b^*F)` of Corollary 1.5.2(i)
(Berkovich, *Etale equivariant sheaves on p-adic analytic spaces*, unfinished
1995–1996 manuscript, printed pp.11–12 = PDF pp.11–12, read in the original by
Worker 26: "For any étale abelian sheaf `F` on `X(G)` there are canonical
isomorphisms `H^q_c(X{G}, F) ⥲ H^q_c(X, b^*F)`, `g ≥ 0`" [sic, for `q ≥ 0`]).
Berkovich states only maps of cohomology groups. This module shows that the
derived-category map `compactComplexComparison` induces them in every
degree. The comparison of `homologyHom` with `mapHomologyIso` is a general
fact about exact functors, with no source claim.

Not constructed or proved here: that the comparison is an isomorphism, the
spectral sequence of Corollary 1.5.2(i), and any analytic instance.

Universes: in the first section `C : Type uC`, `D : Type uD`, `E : Type uE` with
morphisms in `vC`, `vD`, `vE`. In the second, as in
`DiscreteSheafDerivedComparison`.

Source registration: Berkovich,
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`,
folder SHA-256
`e046cadfb9dcec4b0cf6624f80d6316bf532416153b82023f5100bd1ab0726cd`, member
`Berkovich--Etale equivariant sheaves on p-adic analytic spaces (unfinished manuscript)--1996.pdf`.
