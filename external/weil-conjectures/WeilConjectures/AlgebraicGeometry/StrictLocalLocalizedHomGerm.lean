/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.StrictLocalInjectiveSourceComparison
import WeilConjectures.AlgebraicGeometry.SourceCocycleExactRestriction

/-! # Localized Hom classes and restriction of a complex on the base

Source: Stacks Project, Tags 03Q8 and 03Q9, injective-complex computation.
-/

@[expose] public section

universe v

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry CochainComplex CochainComplex.HomComplex

namespace AlgebraicGeometry.Etale

/-- Evaluation of localized Hom classes as cohomology of the complex of sections.
Source: Stacks Project, Tag 03Q8, computation by an injective complex.
(blueprint: lem-weil-pbc-strict-local-localized-hom-germ). -/
@[irreducible] noncomputable def sourceLocalizedSectionsIso {S : Scheme.{v}}
    (K : DerivedCategory.Plus (Sheaf S.smallEtaleTopology AddCommGrpCat.{v + 1}))
    (L : CochainComplex (Sheaf S.smallEtaleTopology AddCommGrpCat.{v + 1}) ℤ)
    [L.IsKInjective] (r : K.obj ≅ DerivedCategory.Q.obj L) (n : ℤ) (W : S.Etale) :
    (strictLocalCohomologyPresheaf K n).obj (op W) ≅
      (HomologicalComplex.homologyFunctor AddCommGrpCat.{v + 1} (.up ℤ) n).obj
        ((((sheafSections S.smallEtaleTopology AddCommGrpCat.{v + 1}).obj
          (op W)).mapHomologicalComplex (.up ℤ)).obj L) :=
  sourcePlusHomIso ((strictLocalFreeSheaf S.smallEtaleTopology).obj W) K L r n ≪≫
    (sourceClassDerivedHomIso ((strictLocalFreeSheaf S.smallEtaleTopology).obj W) L n).symm ≪≫
    (leftHomologyData
      ((CochainComplex.singleFunctor _ 0).obj
        ((strictLocalFreeSheaf S.smallEtaleTopology).obj W)) L n).homologyIso.symm ≪≫
    (HomologicalComplex.homologyFunctor AddCommGrpCat.{v + 1} (.up ℤ) n).mapIso
      (sourceFreeSectionsComplexIso W L)

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Restricting a neighbourhood section commutes with a map of sheaves.
Source: Stacks Project, Tag 03Q9, the canonical restriction construction.
(blueprint: lem-weil-pbc-strict-local-localized-hom-germ). -/
theorem strictHenselizationSectionRestriction_naturality {S : Scheme.{v}}
    {Ω : Type v} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
    (i : SmallModel.{v} (Scheme.strictHenselizationNeighbourhoods s))
    {F G : Sheaf S.smallEtaleTopology AddCommGrpCat.{v + 1}} (b : F ⟶ G) :
    ((sheafSections S.smallEtaleTopology AddCommGrpCat.{v + 1}).obj
      (op ((strictLocalNeighbourhoods s).obj i))).map b ≫
        strictHenselizationSectionRestriction s G i =
    strictHenselizationSectionRestriction s F i ≫
      (upperStar AddCommGrpCat.{v + 1} (Scheme.strictLocalizationToBase s) ⋙
        Sheaf.Γ (Scheme.strictLocalization s).smallEtaleTopology
          AddCommGrpCat.{v + 1}).map b := by
  unfold strictHenselizationSectionRestriction
  let g := Scheme.strictLocalizationToBase s
  let W := (strictLocalNeighbourhoods s).obj i
  let V := Scheme.Etale.mk (𝟙 (Scheme.strictLocalization s))
  have hu := (upperStarLowerStarAdjunction AddCommGrpCat.{v + 1} g).unit.naturality b
  have he := congrArg (fun t ↦ t.hom.app (op W)) hu
  dsimp only [Functor.id_map, ObjectProperty.FullSubcategory.comp_hom,
    NatTrans.comp_app] at he
  change b.hom.app (op W) ≫ _ = _
  rw [← Category.assoc, ← Category.assoc]
  erw [he]
  simp only [Category.assoc]
  have hn := ((upperStar AddCommGrpCat.{v + 1} g).map b).hom.naturality
    (strictHenselizationNeighbourhoodSection s i).op
  erw [← reassoc_of% hn]
  have ht := (Sheaf.ΓNatIsoSheafSections _ _
    (IsTerminal.isTerminalOfObj
      (MorphismProperty.Over.forget @AlgebraicGeometry.Etale ⊤
        (Scheme.strictLocalization s)) V Over.mkIdTerminal)).inv.naturality
    ((upperStar AddCommGrpCat.{v + 1} g).map b)
  change ((upperStar AddCommGrpCat.{v + 1} g).map b).hom.app (op V) ≫ _ = _ at ht
  erw [ht]
  rfl

/-- The natural transformation of pointed neighbourhood section restriction.
Source: Stacks Project, Tag 03Q9, the canonical restriction construction.
(blueprint: lem-weil-pbc-strict-local-localized-hom-germ). -/
@[irreducible] noncomputable def strictLocalSectionRestrictionNat {S : Scheme.{v}}
    {Ω : Type v} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
    (i : SmallModel.{v} (Scheme.strictHenselizationNeighbourhoods s)) :
    (sheafSections S.smallEtaleTopology AddCommGrpCat.{v + 1}).obj
        (op ((strictLocalNeighbourhoods s).obj i)) ⟶
      upperStar AddCommGrpCat.{v + 1} (Scheme.strictLocalizationToBase s) ⋙
        Sheaf.Γ (Scheme.strictLocalization s).smallEtaleTopology
          AddCommGrpCat.{v + 1} where
  app F := strictHenselizationSectionRestriction s F i
  naturality {_ _} b := strictHenselizationSectionRestriction_naturality s i b

set_option backward.isDefEq.respectTransparency false in
/-- The restriction on the complex of sections, transported to strict-local homology.
The construction applies to any complex; its definition contains no choice of a class.
Source: Stacks Project, Tag 03Q9, restriction of the complex to the strict local scheme.
(blueprint: lem-weil-pbc-strict-local-localized-hom-germ). -/
@[irreducible] noncomputable def strictLocalComplexSectionRestriction {S : Scheme.{v}}
    {Ω : Type v} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
    (K : DerivedCategory.Plus (Sheaf S.smallEtaleTopology AddCommGrpCat.{v + 1}))
    (L : CochainComplex (Sheaf S.smallEtaleTopology AddCommGrpCat.{v + 1}) ℤ)
    (r : K.obj ≅ DerivedCategory.Q.obj L) (n : ℤ)
    (i : SmallModel.{v} (Scheme.strictHenselizationNeighbourhoods s)) :
    (HomologicalComplex.homologyFunctor AddCommGrpCat.{v + 1} (.up ℤ) n).obj
        ((((sheafSections S.smallEtaleTopology AddCommGrpCat.{v + 1}).obj
          (op ((strictLocalNeighbourhoods s).obj i))).mapHomologicalComplex (.up ℤ)).obj L) ⟶
      (Sheaf.Γ (Scheme.strictLocalization s).smallEtaleTopology
        AddCommGrpCat.{v + 1}).obj
        ((DerivedCategory.Plus.homologyFunctor _ n).obj
          ((upperStar AddCommGrpCat.{v + 1}
            (Scheme.strictLocalizationToBase s)).mapDerivedCategoryPlus.obj K)) := by
  let U := upperStar AddCommGrpCat.{v + 1} (Scheme.strictLocalizationToBase s)
  let G := Sheaf.Γ (Scheme.strictLocalization s).smallEtaleTopology
    AddCommGrpCat.{v + 1}
  have := strictHenselization_globalSections_preservesFiniteColimits s
  let C := (U.mapHomologicalComplex (.up ℤ)).obj L
  let a := (NatTrans.mapHomologicalComplex (strictLocalSectionRestrictionNat s i)
    (.up ℤ)).app L
  exact (DerivedCategory.homologyFunctorFactors AddCommGrpCat.{v + 1} n).inv.app _ ≫
    (DerivedCategory.homologyFunctor AddCommGrpCat.{v + 1} n).map
      (DerivedCategory.Q.map a ≫ G.mapDerivedCategoryFactors.inv.app C ≫
        G.mapDerivedCategory.map
          (U.mapDerivedCategoryFactors.inv.app L ≫ U.mapDerivedCategory.map r.inv)) ≫
    (G.mapDerivedCategoryHomologyFunctorIso n).inv.app (U.mapDerivedCategory.obj K.obj)

set_option backward.isDefEq.respectTransparency false in
private theorem sourceLeg_eq_sectionRestriction {S : Scheme.{v}}
    {Ω : Type v} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
    (K : DerivedCategory.Plus (Sheaf S.smallEtaleTopology AddCommGrpCat.{v + 1}))
    (n : ℤ) (i : SmallModel.{v} (Scheme.strictHenselizationNeighbourhoods s)) :
    (strictLocalCohomologySourceLegs s K n).app (op i) =
      (strictLocalCohomologyGermMap K n).app (op ((strictLocalNeighbourhoods s).obj i)) ≫
        strictHenselizationSectionRestriction s
          ((DerivedCategory.Plus.homologyFunctor _ n).obj K) i ≫
        (Sheaf.Γ (Scheme.strictLocalization s).smallEtaleTopology
          AddCommGrpCat.{v + 1}).map
          (((upperStar AddCommGrpCat.{v + 1}
            (Scheme.strictLocalizationToBase s)).mapDerivedCategoryPlusHomologyFunctorIso
              n).hom.app K) := by
  classical
  dsimp only [strictLocalCohomologySourceLegs, strictLocalCohomologySourceIso,
    Iso.trans_hom, Functor.mapIso_hom]
  erw [(Scheme.pointSmallEtale s).toPresheafFiber_naturality_assoc]
  have hr := (Classical.choose_spec (existsUnique_strictHenselizationStalkRestriction s
    ((DerivedCategory.Plus.homologyFunctor _ n).obj K))).1 i
  change _ ≫ ( _ ≫ Classical.choose _ ) ≫ _ = _ at ⊢
  erw [hr]
  rfl

set_option backward.isDefEq.respectTransparency true in
/-- Localizing Hom into a K-injective representative and then restricting its sections
computes the canonical cohomology germ leg. This is a statement only about a complex on
S; it has no direct-image functor, pullback square, mate, or fibre cohomology.

Source: Stacks Project, Tag 03Q8, cohomology via injective complexes, and Tag 03Q9,
construction of restriction to the strict henselization.
(blueprint: lem-weil-pbc-strict-local-localized-hom-germ).

Proof: represent a localized Hom class by a cocycle from Z[W][0] to L[n]. Such
representatives exist and are unique modulo homotopy because L is K-injective.
Evaluation at the free generator identifies its class with the cohomology of L(W).
The map to H^n(K)(W) applies homology to this cocycle, so sends it to exactly its
homology section. Naturality of the presheaf fibre moves this map across the germ
of W. The characterizing equation for strictHenselizationStalkRestriction replaces
the resulting germ restriction by strictHenselizationSectionRestriction on that
homology section. Exact inverse image and exact strict-local global sections commute
with homology; their comparison isomorphisms send this section to the class of the
restricted cocycle. Boundaries map to boundaries, so the equality descends to
cohomology. The quotient and localization factorization isomorphisms, and the
homology shift isomorphism, give precisely the displayed transport. Naturality of
these isomorphisms with r completes the equality. Nothing requires acyclicity of
the pulled-back complex. The same argument treats zero classes and every integer n. -/
theorem sourceLocalizedSectionsIso_germ {S : Scheme.{v}}
    {Ω : Type v} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
    (K : DerivedCategory.Plus (Sheaf S.smallEtaleTopology AddCommGrpCat.{v + 1}))
    (L : CochainComplex (Sheaf S.smallEtaleTopology AddCommGrpCat.{v + 1}) ℤ)
    [L.IsKInjective] (r : K.obj ≅ DerivedCategory.Q.obj L) (n : ℤ)
    (i : SmallModel.{v} (Scheme.strictHenselizationNeighbourhoods s)) :
    (strictLocalCohomologySourceLegs s K n).app (op i) =
      (sourceLocalizedSectionsIso K L r n ((strictLocalNeighbourhoods s).obj i)).hom ≫
        strictLocalComplexSectionRestriction s K L r n i := by
  rw [sourceLeg_eq_sectionRestriction]
  ext β
  let W := (strictLocalNeighbourhoods s).obj i
  let A := (strictLocalFreeSheaf S.smallEtaleTopology).obj W
  let e := sourcePlusHomIso A K L r n ≪≫ (sourceClassDerivedHomIso A L n).symm
  have heval (c : CohomologyClass ((CochainComplex.singleFunctor _ 0).obj A) L n) :
      (sourceLocalizedSectionsIso K L r n W).hom (e.inv c) =
        ((HomologicalComplex.homologyFunctor AddCommGrpCat.{v + 1} (.up ℤ) n).map
          (sourceFreeSectionsComplexIso W L).hom)
          ((leftHomologyData ((CochainComplex.singleFunctor _ 0).obj A) L n).homologyIso.inv
            c) := by
    unfold sourceLocalizedSectionsIso
    change (e ≪≫ (leftHomologyData ((CochainComplex.singleFunctor _ 0).obj A)
      L n).homologyIso.symm ≪≫
      (HomologicalComplex.homologyFunctor AddCommGrpCat.{v + 1} (.up ℤ) n).mapIso
        (sourceFreeSectionsComplexIso W L)).hom (e.inv c) = _
    simp only [Iso.trans_hom, ConcreteCategory.comp_apply]
    have hcancel : e.hom (e.inv c) = c := by
      simpa only [ConcreteCategory.comp_apply, ConcreteCategory.id_apply] using
        ConcreteCategory.congr_hom e.inv_hom_id c
    rw [hcancel]
    rfl
  obtain ⟨c, hc⟩ := (ConcreteCategory.bijective_of_isIso e.inv).2 β
  obtain ⟨z, rfl⟩ := CohomologyClass.mk_surjective c
  obtain ⟨f, hf, rfl⟩ := Cocycle.fromSingleMk_surjective z n (zero_add n) (n + 1) rfl
  subst β
  change _ = (strictLocalComplexSectionRestriction s K L r n i)
    ((sourceLocalizedSectionsIso K L r n W).hom (e.inv _))
  rw [heval]
  change ((Sheaf.Γ (Scheme.strictLocalization s).smallEtaleTopology
    AddCommGrpCat.{v + 1}).map
      (((upperStar AddCommGrpCat.{v + 1}
        (Scheme.strictLocalizationToBase s)).mapDerivedCategoryPlusHomologyFunctorIso
          n).hom.app K))
    ((strictHenselizationSectionRestriction s
      ((DerivedCategory.Plus.homologyFunctor _ n).obj K) i)
      ((strictLocalCohomologyGermMap K n).app (op W)
        ((sourcePlusHomIso A K L r n).inv
          ((sourceClassDerivedHomIso A L n).hom
            (CohomologyClass.mk
              (Cocycle.fromSingleMk f (zero_add n) (n + 1) rfl hf)))))) = _
  erw [sourceLocalizedCocycleHomology K L r n W f hf]
  have h := sourceCocycleExactRestriction s K L r n W
    (strictLocalSectionRestrictionNat s i) f hf
  dsimp only at h
  simp only [strictLocalSectionRestrictionNat, strictLocalComplexSectionRestriction] at h ⊢
  exact h.symm

end AlgebraicGeometry.Etale
