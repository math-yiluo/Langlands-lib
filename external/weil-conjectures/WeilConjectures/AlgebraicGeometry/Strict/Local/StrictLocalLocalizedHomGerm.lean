/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve.CohomologyGerms

public import WeilConjectures.AlgebraicGeometry.Strict.Henselization.StrictHenselizationSchemeSectionsExact
public import WeilConjectures.AlgebraicGeometry.Strict.Local.StrictLocalSectionCone
public import WeilConjectures.AlgebraicGeometry.Strict.Local.StrictLocalInjectiveSourceComparison
import WeilConjectures.AlgebraicGeometry.Source.SourceCocycleExactRestriction
public import WeilConjectures.AlgebraicGeometry.StrictLocalLocalizedHomGerm

/-! # Localized Hom classes and restriction of a complex on the base

Source: Stacks Project, Tags 03Q8 and 03Q9, injective-complex computation.
-/

/- This original-model counterpart follows the proved calculation in
WeilConjectures.AlgebraicGeometry.StrictLocalLocalizedHomGerm.
The spectrum and structure morphism are those of the small coordinate-ring colimit. -/

@[expose] public section

universe v

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry CochainComplex CochainComplex.HomComplex

namespace AlgebraicGeometry.Etale

attribute [local irreducible] smallModel_sourcePlusHomIso
  smallModel_sourceClassDerivedHomIso smallModel_sourceFreeSectionsComplexIso

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Restricting a neighbourhood section commutes with a map of sheaves.
Source: Stacks Project, Tag 03Q9, the canonical restriction construction.
(blueprint: lem-weil-pbc-strict-local-localized-hom-germ). -/
theorem smallModel_strictHenselizationSectionRestriction_naturality {S : Scheme.{v}}
    {Ω : Type v} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
    (i : SmallModel.{v} (Scheme.strictHenselizationNeighbourhoods s))
    {F G : Sheaf S.smallEtaleTopology AddCommGrpCat.{v + 1}} (b : F ⟶ G) :
    ((sheafSections S.smallEtaleTopology AddCommGrpCat.{v + 1}).obj
      (op ((strictLocalNeighbourhoods s).obj i))).map b ≫
        (strictLocalSectionCone s).restriction G i =
    (strictLocalSectionCone s).restriction F i ≫
      (upperStar AddCommGrpCat.{v + 1} (Scheme.strictHenselizationStructuralMap s) ⋙
        Sheaf.Γ (Scheme.strictHenselizationScheme s).smallEtaleTopology
          AddCommGrpCat.{v + 1}).map b := by
  unfold PointedEtaleSectionCone.restriction
  let g := Scheme.strictHenselizationStructuralMap s
  let W := (strictLocalNeighbourhoods s).obj i
  let V := Scheme.Etale.mk (𝟙 (Scheme.strictHenselizationScheme s))
  have hu := (upperStarLowerStarAdjunction AddCommGrpCat.{v + 1} g).unit.naturality b
  have he := congrArg (fun t ↦ t.hom.app (op W)) hu
  dsimp only [Functor.id_map, ObjectProperty.FullSubcategory.comp_hom,
    NatTrans.comp_app] at he
  change b.hom.app (op W) ≫ _ = _
  rw [← Category.assoc, ← Category.assoc]
  erw [he]
  simp only [Category.assoc]
  have hn := ((upperStar AddCommGrpCat.{v + 1} g).map b).hom.naturality
    (strictLocalNeighbourhoodSection s i).op
  erw [← reassoc_of% hn]
  have ht := (Sheaf.ΓNatIsoSheafSections _ _
    (IsTerminal.isTerminalOfObj
      (MorphismProperty.Over.forget @AlgebraicGeometry.Etale ⊤
        (Scheme.strictHenselizationScheme s)) V Over.mkIdTerminal)).inv.naturality
    ((upperStar AddCommGrpCat.{v + 1} g).map b)
  change ((upperStar AddCommGrpCat.{v + 1} g).map b).hom.app (op V) ≫ _ = _ at ht
  erw [ht]
  rfl

/-- Evaluation of localized Hom classes as cohomology of the complex of sections, in the
small coordinate-ring colimit model.
Source: Stacks Project, Tag 03Q8, computation by an injective complex.
(blueprint: lem-weil-pbc-strict-local-localized-hom-germ). -/
@[irreducible] noncomputable def smallModel_sourceLocalizedSectionsIso {S : Scheme.{v}}
    (K : DerivedCategory.Plus (Sheaf S.smallEtaleTopology AddCommGrpCat.{v + 1}))
    (L : CochainComplex (Sheaf S.smallEtaleTopology AddCommGrpCat.{v + 1}) ℤ)
    [L.IsKInjective] (r : K.obj ≅ DerivedCategory.Q.obj L) (n : ℤ) (W : S.Etale) :
    (strictLocalCohomologyPresheaf K n).obj (op W) ≅
      (HomologicalComplex.homologyFunctor AddCommGrpCat.{v + 1} (.up ℤ) n).obj
        ((((sheafSections S.smallEtaleTopology AddCommGrpCat.{v + 1}).obj
          (op W)).mapHomologicalComplex (.up ℤ)).obj L) :=
  smallModel_sourcePlusHomIso ((strictLocalFreeSheaf S.smallEtaleTopology).obj W) K L r n ≪≫
    (smallModel_sourceClassDerivedHomIso
      ((strictLocalFreeSheaf S.smallEtaleTopology).obj W) L n).symm ≪≫
    (leftHomologyData
      ((CochainComplex.singleFunctor _ 0).obj
        ((strictLocalFreeSheaf S.smallEtaleTopology).obj W)) L n).homologyIso.symm ≪≫
    (HomologicalComplex.homologyFunctor AddCommGrpCat.{v + 1} (.up ℤ) n).mapIso
      (smallModel_sourceFreeSectionsComplexIso W L)

/-- The natural transformation of pointed neighbourhood section restriction, in the small
coordinate-ring colimit model.
Source: Stacks Project, Tag 03Q9, the canonical restriction construction.
(blueprint: lem-weil-pbc-strict-local-localized-hom-germ). -/
@[irreducible] noncomputable def smallModel_strictLocalSectionRestrictionNat {S : Scheme.{v}}
    {Ω : Type v} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
    (i : SmallModel.{v} (Scheme.strictHenselizationNeighbourhoods s)) :
    (sheafSections S.smallEtaleTopology AddCommGrpCat.{v + 1}).obj
        (op ((strictLocalNeighbourhoods s).obj i)) ⟶
      upperStar AddCommGrpCat.{v + 1} (Scheme.strictHenselizationStructuralMap s) ⋙
        Sheaf.Γ (Scheme.strictHenselizationScheme s).smallEtaleTopology
          AddCommGrpCat.{v + 1} where
  app F := (strictLocalSectionCone s).restriction F i
  naturality {_ _} b := smallModel_strictHenselizationSectionRestriction_naturality s i b

set_option backward.isDefEq.respectTransparency false in
/-- The restriction on the complex of sections, transported to strict-local homology, in the
small coordinate-ring colimit model.
Source: Stacks Project, Tag 03Q9, restriction of the complex to the strict local scheme.
(blueprint: lem-weil-pbc-strict-local-localized-hom-germ). -/
@[irreducible] noncomputable def smallModel_strictLocalComplexSectionRestriction
    {S : Scheme.{v}} {Ω : Type v} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
    (K : DerivedCategory.Plus (Sheaf S.smallEtaleTopology AddCommGrpCat.{v + 1}))
    (L : CochainComplex (Sheaf S.smallEtaleTopology AddCommGrpCat.{v + 1}) ℤ)
    (r : K.obj ≅ DerivedCategory.Q.obj L) (n : ℤ)
    (i : SmallModel.{v} (Scheme.strictHenselizationNeighbourhoods s)) :
    (HomologicalComplex.homologyFunctor AddCommGrpCat.{v + 1} (.up ℤ) n).obj
        ((((sheafSections S.smallEtaleTopology AddCommGrpCat.{v + 1}).obj
          (op ((strictLocalNeighbourhoods s).obj i))).mapHomologicalComplex (.up ℤ)).obj L) ⟶
      (Sheaf.Γ (Scheme.strictHenselizationScheme s).smallEtaleTopology
        AddCommGrpCat.{v + 1}).obj
        ((DerivedCategory.Plus.homologyFunctor _ n).obj
          ((upperStar AddCommGrpCat.{v + 1}
            (Scheme.strictHenselizationStructuralMap s)).mapDerivedCategoryPlus.obj K)) := by
  let U := upperStar AddCommGrpCat.{v + 1} (Scheme.strictHenselizationStructuralMap s)
  let G := Sheaf.Γ (Scheme.strictHenselizationScheme s).smallEtaleTopology
    AddCommGrpCat.{v + 1}
  have := strictHenselizationScheme_globalSections_preservesFiniteColimits s
  let C := (U.mapHomologicalComplex (.up ℤ)).obj L
  let a := (NatTrans.mapHomologicalComplex (smallModel_strictLocalSectionRestrictionNat s i)
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
    (smallModel_strictLocalCohomologySourceLegs s K n).app (op i) =
      (strictLocalCohomologyGermMap K n).app (op ((strictLocalNeighbourhoods s).obj i)) ≫
        (strictLocalSectionCone s).restriction
          ((DerivedCategory.Plus.homologyFunctor _ n).obj K) i ≫
        (Sheaf.Γ (Scheme.strictHenselizationScheme s).smallEtaleTopology
          AddCommGrpCat.{v + 1}).map
          (((upperStar AddCommGrpCat.{v + 1}
            (Scheme.strictHenselizationStructuralMap s)).mapDerivedCategoryPlusHomologyFunctorIso
              n).hom.app K) := by
  exact smallModel_strictLocalCohomologySourceLegs_app s K n i

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
theorem smallModel_sourceLocalizedSectionsIso_germ {S : Scheme.{v}}
    {Ω : Type v} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
    (K : DerivedCategory.Plus (Sheaf S.smallEtaleTopology AddCommGrpCat.{v + 1}))
    (L : CochainComplex (Sheaf S.smallEtaleTopology AddCommGrpCat.{v + 1}) ℤ)
    [L.IsKInjective] (r : K.obj ≅ DerivedCategory.Q.obj L) (n : ℤ)
    (i : SmallModel.{v} (Scheme.strictHenselizationNeighbourhoods s)) :
    (smallModel_strictLocalCohomologySourceLegs s K n).app (op i) =
      (smallModel_sourceLocalizedSectionsIso K L r n ((strictLocalNeighbourhoods s).obj i)).hom ≫
        smallModel_strictLocalComplexSectionRestriction s K L r n i := by
  rw [sourceLeg_eq_sectionRestriction]
  ext β
  let W := (strictLocalNeighbourhoods s).obj i
  let A := (strictLocalFreeSheaf S.smallEtaleTopology).obj W
  let e := smallModel_sourcePlusHomIso A K L r n ≪≫ (smallModel_sourceClassDerivedHomIso A L n).symm
  have heval (c : CohomologyClass ((CochainComplex.singleFunctor _ 0).obj A) L n) :
      (smallModel_sourceLocalizedSectionsIso K L r n W).hom (e.inv c) =
        ((HomologicalComplex.homologyFunctor AddCommGrpCat.{v + 1} (.up ℤ) n).map
          (smallModel_sourceFreeSectionsComplexIso W L).hom)
          ((leftHomologyData ((CochainComplex.singleFunctor _ 0).obj A) L n).homologyIso.inv
            c) := by
    unfold smallModel_sourceLocalizedSectionsIso
    change (e ≪≫ (leftHomologyData ((CochainComplex.singleFunctor _ 0).obj A)
      L n).homologyIso.symm ≪≫
      (HomologicalComplex.homologyFunctor AddCommGrpCat.{v + 1} (.up ℤ) n).mapIso
        (smallModel_sourceFreeSectionsComplexIso W L)).hom (e.inv c) = _
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
  change _ = (smallModel_strictLocalComplexSectionRestriction s K L r n i)
    ((smallModel_sourceLocalizedSectionsIso K L r n W).hom (e.inv _))
  rw [heval]
  change ((Sheaf.Γ (Scheme.strictHenselizationScheme s).smallEtaleTopology
    AddCommGrpCat.{v + 1}).map
      (((upperStar AddCommGrpCat.{v + 1}
        (Scheme.strictHenselizationStructuralMap s)).mapDerivedCategoryPlusHomologyFunctorIso
          n).hom.app K))
    (((strictLocalSectionCone s).restriction
      ((DerivedCategory.Plus.homologyFunctor _ n).obj K) i)
      ((strictLocalCohomologyGermMap K n).app (op W)
        ((smallModel_sourcePlusHomIso A K L r n).inv
          ((smallModel_sourceClassDerivedHomIso A L n).hom
            (CohomologyClass.mk
              (Cocycle.fromSingleMk f (zero_add n) (n + 1) rfl hf)))))) = _
  erw [smallModel_sourceLocalizedCocycleHomology K L r n W f hf]
  have h := smallModel_sourceCocycleExactRestriction s K L r n W
    (smallModel_strictLocalSectionRestrictionNat s i) f hf
  dsimp only at h
  simp only [smallModel_strictLocalSectionRestrictionNat,
    smallModel_strictLocalComplexSectionRestriction] at h ⊢
  exact h.symm

end AlgebraicGeometry.Etale
