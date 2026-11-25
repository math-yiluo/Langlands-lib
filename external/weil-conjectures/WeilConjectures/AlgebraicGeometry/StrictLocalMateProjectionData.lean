/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.StrictLocalCohomologyGerms

/-! # Projection restriction formulas for the strict-local mate

Source: Stacks Project, Tag 03Q9, final injective-complex paragraph.
-/

@[expose] public section

universe v

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

namespace AlgebraicGeometry.Etale

/-- The global-sections map of the degree-n homology of the derived strict-local mate.
Source: Stacks, Tag 03Q9, final proof paragraph
(blueprint: def-weil-pbc-strict-local-mate-projection-data). -/
noncomputable abbrev strictLocalBaseChangeHomologyMap
    {X S : Scheme.{v}} (f : X ⟶ S)
    {Ω : Type v} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{v + 1}))
    (n : ℤ) :
    (Sheaf.Γ (Scheme.strictLocalization s).smallEtaleTopology
      AddCommGrpCat.{v + 1}).obj
      ((DerivedCategory.Plus.homologyFunctor _ n).obj
        ((upperStar AddCommGrpCat.{v + 1}
          (Scheme.strictLocalizationToBase s)).mapDerivedCategoryPlus.obj
          ((rightDerivedLowerStarPlus AddCommGrpCat.{v + 1} f).obj K))) ⟶
    (Sheaf.Γ (Scheme.strictLocalization s).smallEtaleTopology
      AddCommGrpCat.{v + 1}).obj
      ((DerivedCategory.Plus.homologyFunctor _ n).obj
        ((rightDerivedLowerStarPlus AddCommGrpCat.{v + 1}
          (pullback.snd f (Scheme.strictLocalizationToBase s))).obj
          ((upperStar AddCommGrpCat.{v + 1}
            (pullback.fst f (Scheme.strictLocalizationToBase s))).mapDerivedCategoryPlus.obj
            K))) :=
  ((Sheaf.Γ (Scheme.strictLocalization s).smallEtaleTopology
    AddCommGrpCat.{v + 1}).map
    ((DerivedCategory.Plus.homologyFunctor _ n).map
      ((mateEquiv (upperStarLowerStarAdjunction AddCommGrpCat.{v + 1} f).derivedPlus
        (upperStarLowerStarAdjunction AddCommGrpCat.{v + 1}
          (pullback.snd f (Scheme.strictLocalizationToBase s))).derivedPlus
        (TwoSquare.mk _ _ _ _ (pullbackSquareComparison AddCommGrpCat.{v + 1}
          (IsPullback.of_hasPullback f
            (Scheme.strictLocalizationToBase s)).toCommSq).hom))
            |>.app K)))

/-- Exact strict-local sections and Leray identify the target with limit cohomology.
Source: Stacks, Tags 03Q9 and 03QO
(blueprint: def-weil-pbc-strict-local-mate-projection-data). -/
noncomputable def strictLocalBaseChangeTargetIso
    {X S : Scheme.{v}} (f : X ⟶ S)
    {Ω : Type v} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{v + 1}))
    (n : ℤ) :
    (Sheaf.Γ (Scheme.strictLocalization s).smallEtaleTopology
      AddCommGrpCat.{v + 1}).obj
      ((DerivedCategory.Plus.homologyFunctor _ n).obj
        ((rightDerivedLowerStarPlus AddCommGrpCat.{v + 1}
          (pullback.snd f (Scheme.strictLocalizationToBase s))).obj
          ((upperStar AddCommGrpCat.{v + 1}
            (pullback.fst f (Scheme.strictLocalizationToBase s))).mapDerivedCategoryPlus.obj
            K))) ≅
    (cohomology AddCommGrpCat.{v + 1}
      (pullback f (Scheme.strictLocalizationToBase s)) n).obj
      ((upperStar AddCommGrpCat.{v + 1}
        (pullback.fst f (Scheme.strictLocalizationToBase s))).mapDerivedCategory.obj
        K.obj) :=
  strictHenselizationLerayHomologyIso s f n _

/-- Hypercohomology identifications, their transitions, and their compatibility with
projection restriction. There is no source colimit assertion in this data.
Source: Stacks, Tag 03Q9, final proof paragraph
(blueprint: def-weil-pbc-strict-local-mate-projection-data). -/
structure StrictLocalMateProjectionData
    {X S : Scheme.{v}} (f : X ⟶ S)
    {Ω : Type v} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{v + 1}))
    (n : ℤ) (Q : StrictLocalNeighbourhoodGeometry f s) where
  e : ∀ i : SmallModel.{v} (Scheme.strictHenselizationNeighbourhoods s),
        (strictLocalCohomologyNeighbourhoodFunctor s
      ((rightDerivedLowerStarPlus AddCommGrpCat.{v + 1} f).obj K) n).obj (op i) ≅
    (cohomology AddCommGrpCat.{v + 1} ((strictLocalNeighbourhoodDiagram f s).obj i) n).obj
      ((upperStar AddCommGrpCat.{v + 1} ((strictLocalNeighbourhoodProjection f s).app
        i)).mapDerivedCategory.obj K.obj)
  transition : ∀ {i j : SmallModel.{v} (Scheme.strictHenselizationNeighbourhoods s)} (a : i ⟶ j),
        (strictLocalCohomologyNeighbourhoodFunctor s
      ((rightDerivedLowerStarPlus AddCommGrpCat.{v + 1} f).obj K) n).map a.op =
      (e j).hom ≫
      (Etale.cohomology AddCommGrpCat.{v + 1} ((strictLocalNeighbourhoodDiagram f s).obj j) n).map
        ((Etale.mapDerivedUpperStarLowerStarAdjunction AddCommGrpCat.{v + 1}
          ((strictLocalNeighbourhoodDiagram f s).map a)).unit.app
            ((Etale.upperStar AddCommGrpCat.{v + 1} ((strictLocalNeighbourhoodProjection f s).app
        j)).mapDerivedCategory.obj
              K.obj)) ≫
      (DerivedCategory.homologyFunctor AddCommGrpCat.{v + 1} n).map
        ((Etale.rightDerivedLowerStarCompRightDerivedGlobalSectionsIso
          AddCommGrpCat.{v + 1} ((strictLocalNeighbourhoodDiagram f s).map a)).hom.app
            ((Etale.upperStar AddCommGrpCat.{v + 1} ((strictLocalNeighbourhoodDiagram f s).map
        a)).mapDerivedCategory.obj
              ((Etale.upperStar AddCommGrpCat.{v + 1} ((strictLocalNeighbourhoodProjection f
        s).app j)).mapDerivedCategory.obj
                K.obj))) ≫
      (Etale.cohomology AddCommGrpCat.{v + 1} ((strictLocalNeighbourhoodDiagram f s).obj i) n).map
        ((Functor.mapDerivedCategoryNatIso
          (Etale.upperStarComp AddCommGrpCat.{v + 1} ((strictLocalNeighbourhoodDiagram f s).map a)
        ((strictLocalNeighbourhoodProjection f s).app j)
            ((strictLocalNeighbourhoodProjection f s).app i) ((Category.comp_id
        ((strictLocalNeighbourhoodProjection f s).app i)).symm.trans
        ((strictLocalNeighbourhoodProjection f s).naturality a).symm)) ≪≫
          (Functor.mapDerivedCategoryCompIso
            (Etale.upperStar AddCommGrpCat.{v + 1} ((strictLocalNeighbourhoodProjection f s).app j))
            (Etale.upperStar AddCommGrpCat.{v + 1} ((strictLocalNeighbourhoodDiagram f s).map
        a))).symm).inv.app K.obj) ≫
      (e i).inv
  restriction : ∀ i : SmallModel.{v} (Scheme.strictHenselizationNeighbourhoods s),
        ((strictLocalCohomologySourceLegs s
      ((rightDerivedLowerStarPlus AddCommGrpCat.{v + 1} f).obj K) n).app (op i)) ≫
        ((Sheaf.Γ (Scheme.strictLocalization s).smallEtaleTopology
        AddCommGrpCat.{v + 1}).map
        ((DerivedCategory.Plus.homologyFunctor _ n).map
          ((mateEquiv (upperStarLowerStarAdjunction AddCommGrpCat.{v + 1} f).derivedPlus
            (upperStarLowerStarAdjunction AddCommGrpCat.{v + 1}
              (pullback.snd f (Scheme.strictLocalizationToBase s))).derivedPlus
            (TwoSquare.mk _ _ _ _ (pullbackSquareComparison AddCommGrpCat.{v + 1}
              (IsPullback.of_hasPullback f
                (Scheme.strictLocalizationToBase s)).toCommSq).hom))
                |>.app K))) =
      (e i).hom ≫
      (Etale.cohomology AddCommGrpCat.{v + 1} ((strictLocalNeighbourhoodDiagram f s).obj i) n).map
        ((Etale.mapDerivedUpperStarLowerStarAdjunction AddCommGrpCat.{v + 1}
          (Q.legs.app i)).unit.app
            ((Etale.upperStar AddCommGrpCat.{v + 1} ((strictLocalNeighbourhoodProjection f s).app
        i)).mapDerivedCategory.obj
              K.obj)) ≫
      (DerivedCategory.homologyFunctor AddCommGrpCat.{v + 1} n).map
        ((Etale.rightDerivedLowerStarCompRightDerivedGlobalSectionsIso
          AddCommGrpCat.{v + 1} (Q.legs.app i)).hom.app
            ((Etale.upperStar AddCommGrpCat.{v + 1} (Q.legs.app i)).mapDerivedCategory.obj
              ((Etale.upperStar AddCommGrpCat.{v + 1} ((strictLocalNeighbourhoodProjection f
        s).app i)).mapDerivedCategory.obj
                K.obj))) ≫
      (Etale.cohomology AddCommGrpCat.{v + 1} (pullback f (Scheme.strictLocalizationToBase
        s)) n).map
        ((Functor.mapDerivedCategoryNatIso
          (Etale.upperStarComp AddCommGrpCat.{v + 1} (Q.legs.app i)
        ((strictLocalNeighbourhoodProjection f s).app i) (pullback.fst f
        (Scheme.strictLocalizationToBase s))
            (Q.over i).symm) ≪≫
          (Functor.mapDerivedCategoryCompIso
            (Etale.upperStar AddCommGrpCat.{v + 1} ((strictLocalNeighbourhoodProjection f s).app i))
            (Etale.upperStar AddCommGrpCat.{v + 1} (Q.legs.app i))).symm).inv.app K.obj) ≫
      (strictLocalBaseChangeTargetIso f s K n).inv


end AlgebraicGeometry.Etale
