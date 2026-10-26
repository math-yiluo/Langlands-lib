# Smooth Godement comparison for left exact functors and invariants

Author: Worker 61. The module imports my `Langlands.Cohomology.LeftExactHomology`
(`homologyNatTrans`, `derivedNatTrans`, `comparisonNatTrans_comp_derivedNatTrans`), my
`Langlands.Cohomology.SmoothGodementComparison.Transformation` (`comparisonTrans`) and
`Langlands.Cohomology.DivisibleSystem.Invariants` (`smoothQuotientInvariants` and the
instance that `SmoothRep.toRep` preserves finite limits). It uses my
`Langlands.Cohomology.AcyclicResolution.Comparison` (`comparisonNatTrans`,
`comparisonNatTrans_app`, `comparison_zero`, `homologyZeroIso`, `cyclesZeroIso`,
`isIso_comparisonNatTrans_zero`, `comparisonNatIso`), the published
`EquivariantGodementCohomology.homologyZeroIso` and `cyclesIso`, and the published
`SmoothGodementCohomology` and `SmoothSheafCohomology` objects. From Mathlib it uses
`Functor.rightDerived`, `Functor.rightDerivedZeroIsoSelf`, `Rep.invariantsFunctor` and
`Rep.resFunctor`.

Composition `f ≫ g` is `f` followed by `g`.

## Setting

All declarations are in the namespace `Langlands.Cohomology.SmoothGodementComparison`, with
the variables of `Transformation`: `R : Type u` a commutative ring, `G : Type u` a
topological group acting on a topological space `X : Type u` by continuous maps, with
`[HasStableNeighbourhoods G X]`. `R`, `G`, `X` are implicit here. `Godement.smoothComplexFunctor R G X`
is the smooth Godement complex of a smooth equivariant module sheaf, with augmentation
`CokernelComplex.augmentationNat (Godement.smoothZeroFunctor R G X)
(Godement.smoothCoaugmentation R G X)`. As in `Transformation`, the explicit hypothesis

`hK : ∀ F, QuasiIso (CokernelComplex.augmentationMap … F)`

says that every smooth Godement augmentation is a quasi-isomorphism.
`Transformation.quasiIso_augmentationMap` derives it from the published
`CokernelResolutionStatement`, which is not proved.

## Any additive functor of smooth sheaves

Let `T : SmoothTopologicalSheaf R G X ⥤ B` be an additive functor to an abelian category
`B : Type u'` (`Category.{v'} B`).

- `godementCohomology T q := Godement.smoothComplexFunctor R G X ⋙
  T.mapHomologicalComplex _ ⋙ homologyFunctor B _ q` is the degree-`q` cohomology of `T`
  applied termwise to the smooth Godement complex.
- `sheafComparisonTrans hK T q : godementCohomology T q ⟶ T.rightDerived q` is
  `AcyclicResolution.comparisonNatTrans` for `T` and the smooth Godement resolution.
  `sheafComparisonTrans_app`: its component at `F` is `AcyclicResolution.comparison T I φ q`
  for every injective resolution `I` of `F` and every `φ` with augmentation followed by `φ`
  equal to `I.ι`. `sheafComparisonTrans_compactSections`: for
  `T = smoothSheafCompactSections R G X` it is `comparisonTrans hK q` (by definition).

From here on `T` is also left exact (`[PreservesFiniteLimits T]`).

- `homologyZeroIso_eq_app T F`: the degree-zero identification
  `AcyclicResolution.homologyZeroIso T` for the smooth Godement augmentation of `F` is the
  component at `F` of the published `EquivariantGodementCohomology.homologyZeroIso` for the
  smooth Godement complex and `T`. Both are inverse to the identification of `T F` with the
  degree-zero cycles. Their `hom` maps agree because both composites with the inclusion of
  the cycles are `T` of the degree-zero augmentation. This is the proof of
  `Transformation.homologyZeroIso_eq` with compact sections replaced by `T`.
- `sheafComparisonTrans_zero`: `sheafComparisonTrans hK T 0` is
  `(EquivariantGodementCohomology.homologyZeroIso … T).hom ≫ T.rightDerivedZeroIsoSelf.inv`.
  Proof: `AcyclicResolution.comparison_zero` at each `F` and `homologyZeroIso_eq_app`. The
  instance `isIso_sheafComparisonTrans_zero` says it is an isomorphism.
- `sheafComparisonIso hK T hcomp hacyc q : godementCohomology T q ≅ T.rightDerived q`, with
  `sheafComparisonIso_hom` (`simp`): it is `AcyclicResolution.comparisonNatIso`, taking two
  hypotheses, neither proved here. One is
  `hcomp : AcyclicResolutionComparisonStatement.{u + 1, u, u', v'}`, the published statement
  that acyclic resolutions compute right derived functors. The other is
  `hacyc : ∀ F i n, IsZero ((T.rightDerived (n + 1)).obj
  (((Godement.smoothComplexFunctor R G X).obj F).X i))`, the `T`-acyclicity of every term of
  every smooth Godement complex.

## Invariant compact sections

- `invariantComparisonTrans hK q :
  SmoothGodementCohomology.smoothGodementInvariantCompactCohomology R G X q ⟶
  SmoothSheafCohomology.invariantCompactDerived R G X q` is
  `sheafComparisonTrans hK (SmoothSheafCohomology.invariantCompactSections R G X) q`. The two
  published objects are by definition `godementCohomology` and the right derived functors of
  invariant compact sections. Before this module they had no comparison map.
- `invariantComparisonTrans_zero`: in degree zero it is
  `(smoothGodementInvariantCompactCohomologyZeroIso R G X).hom ≫
  (invariantCompactDerivedZeroIso R G X).inv`, the published degree-zero identifications.
  Instance `isIso_invariantComparisonTrans_zero`.

## Left exact functors of smooth representations

Let `Φ : SmoothRep.{u, u, u} R G ⥤ E` be additive and left exact (`[Φ.Additive]`,
`[PreservesFiniteLimits Φ]`), with `E : Type u'` abelian (`Category.{v'} E`). Then
`smoothSheafCompactSections R G X ⋙ Φ` is left exact, and the results above apply to it.

- `godementEdge Φ q : godementCohomology (smoothSheafCompactSections R G X ⋙ Φ) q ⟶
  smoothGodementCompactCohomology R G X q ⋙ Φ` is
  `LeftExactHomology.homologyNatTrans Φ _ q` whiskered by the compactly supported smooth
  Godement complex. It maps the cohomology of `Φ` applied to compact sections of the smooth
  Godement complex to `Φ` of its cohomology.
- `derivedEdge Φ q : (smoothSheafCompactSections R G X ⋙ Φ).rightDerived q ⟶
  compactDerived R G X q ⋙ Φ` is `LeftExactHomology.derivedNatTrans Φ
  (smoothSheafCompactSections R G X) q`.
- `sheafComparisonTrans_comp_derivedEdge hK Φ q`: the square
  `sheafComparisonTrans hK (smoothSheafCompactSections R G X ⋙ Φ) q ≫ derivedEdge Φ q =
  godementEdge Φ q ≫ whiskerRight (comparisonTrans hK q) Φ` commutes. This is
  `LeftExactHomology.comparisonNatTrans_comp_derivedNatTrans` for compact sections and the
  smooth Godement resolution.
- Instances: `godementEdge Φ 0` and `derivedEdge Φ 0` are isomorphisms. If `Φ` also
  preserves homology (`[Φ.PreservesHomology]`, e.g. an exact `Φ`), `godementEdge Φ q` and
  `derivedEdge Φ q` are isomorphisms for all `q`.

## Invariants

- `smoothInvariants R G := SmoothRep.toRep ⋙ Rep.invariantsFunctor R G` (an `abbrev`): the
  `G`-invariants of a smooth representation, as an `R`-module.
- `smoothSubgroupInvariants R G K := SmoothRep.toRep ⋙ Rep.resFunctor K.subtype ⋙
  Rep.invariantsFunctor R K` (an `abbrev`) for a subgroup `K` of `G`: the `K`-invariants, as
  an `R`-module. For compact open `K` these are the level-`K` invariants. Nothing about `K`
  is assumed.
- The published `smoothQuotientInvariants R H` (`DivisibleSystem.Invariants`) for a normal
  subgroup `H`: the `H`-invariants as a representation of `G ⧸ H`.

All three are additive and left exact by instance inference, since `SmoothRep.toRep`,
`Rep.resFunctor`, `Rep.invariantsFunctor` and `Rep.quotientToInvariantsFunctor` preserve
finite limits. The module states three specialized squares, which check that these
instances are found:

- `invariantCompactSections_eq R G X`: `SmoothSheafCohomology.invariantCompactSections R G X =
  smoothSheafCompactSections R G X ⋙ smoothInvariants R G`, by `rfl`.
- `invariantComparisonTrans_comp_derivedEdge hK q`: the square for `Φ = smoothInvariants R G`,
  whose first map is `invariantComparisonTrans hK q`.
- `subgroupInvariants_comparisonTrans_comp_derivedEdge hK K q` and
  `quotientInvariants_comparisonTrans_comp_derivedEdge hK H q`: the squares for
  `smoothSubgroupInvariants R G K` and `smoothQuotientInvariants R H`.

## Provenance and interpretation

Provenance: derived. The module specializes the generic constructions of
`AcyclicResolution.Comparison` and `LeftExactHomology` to the smooth Godement resolution and
to invariants. The specializations are framework infrastructure and not definitions taken
from a source.

The use is Harris, *Galois properties of cohomological automorphic forms on GL(n)* (1999),
§2, printed pp.304–305. Cohomology is computed by the global sections of Berkovich's smooth
equivariant Godement-type resolution (Lemma 2.2, Lemma 2.2 bis, (2.3)). For an open normal
pro-p subgroup `H` acting trivially on the cohomology, Harris states that, since p is prime
to ℓ, the functor `H⁰(H, ·)` is exact on ℓ-primary torsion modules. Hence the inclusion of
the complex of `H`-invariants into the complex in (2.3) is a quasi-isomorphism, and the
cohomology is computed by complexes of `Z/ℓ^mZ[S(ẽ)/H]`-modules. In this module `G` plays
the role of `S(ẽ)` and compact sections the role of the sections over `U(ẽ)`.
`godementCohomology (smoothSheafCompactSections R G X ⋙ smoothQuotientInvariants R H) q` is
the cohomology of the `H`-invariants of the Godement complex, as representations of `G ⧸ H`.
`godementEdge` compares it with the `H`-invariants of the cohomology, and
`sheafComparisonTrans` and `derivedEdge` relate both to derived functors. In Harris's
argument `H` acts trivially on the cohomology, so the `H`-invariants of the cohomology are
the cohomology itself. The exactness of `H`-invariants on ℓ-primary torsion modules is not
formalized. It would enter as `[Φ.PreservesHomology]`, which `smoothQuotientInvariants R H`
does not satisfy for general `R` and `H`. The triviality of the `H`-action is not formalized either.

## Scope

- No invertibility in positive degrees is proved. `sheafComparisonIso` takes
  `AcyclicResolutionComparisonStatement` and the acyclicity of the Godement terms as
  hypotheses. The isomorphism instances for `godementEdge` and `derivedEdge` in positive
  degrees assume `[Φ.PreservesHomology]`.
- The hypothesis `hK` is kept explicit, as in `Transformation`.
- Nothing about the topology of `K` or `H`, and no condition on `R`, is used.
