/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProperBaseChange.SpecializationCospecializationArrows
public import WeilConjectures.AlgebraicGeometry.Strict.Henselization.StrictHenselizationSchemeSectionsExact

/-! # The canonical derived restriction to the small strict-local model

Source: Stacks Project, Tags 03Q9, 03QO and 0GJ2.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Etale

/-- The unique pointed-neighbourhood restriction, natural in the sheaf.
Source: Stacks Project, Tag 03Q9, the restriction construction. -/
noncomputable def strictLocalRestrictionNat
    {S : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ S) :
    (Scheme.pointSmallEtale s).sheafFiber (A := AddCommGrpCat.{u + 1}) ⟶
      upperStar AddCommGrpCat.{u + 1} (Scheme.strictHenselizationStructuralMap s) ⋙
        Sheaf.Γ (Scheme.strictHenselizationScheme s).smallEtaleTopology
          AddCommGrpCat.{u + 1} where
  app F := Classical.choose ((strictLocalSectionCone s).existsUnique_restriction F)
  naturality {F G} a := by
    let N := (equivSmallModel.{u} (Scheme.strictHenselizationNeighbourhoods s)).inverse ⋙
      Scheme.strictHenselizationAffineInclusion s ⋙ ObjectProperty.ι
        (fun n : (Scheme.pointSmallEtale s).fiber.Elements ↦ IsAffine n.1.left)
    have hN : N.Initial := (Scheme.strictHenselization_properties s).1
    let c := ((Scheme.pointSmallEtale s).presheafFiberCocone F.obj).whisker N.op
    let hc : IsColimit c :=
      (Functor.Final.isColimitWhiskerEquiv N.op _).symm
        ((Scheme.pointSmallEtale s).isColimitPresheafFiberCocone F.obj)
    apply hc.hom_ext
    intro j
    have hrF := (Classical.choose_spec
      ((strictLocalSectionCone s).existsUnique_restriction F)).1
    have hrG := (Classical.choose_spec
      ((strictLocalSectionCone s).existsUnique_restriction G)).1
    change (Scheme.pointSmallEtale s).toPresheafFiber
        ((Scheme.AffineEtale.Spec S).obj
          ((equivSmallModel.{u} (Scheme.strictHenselizationNeighbourhoods s)).inverse.obj
            j.unop).1)
        ((equivSmallModel.{u} (Scheme.strictHenselizationNeighbourhoods s)).inverse.obj
          j.unop).2 F.obj ≫ _ = _
    erw [← Category.assoc,
      (Scheme.pointSmallEtale s).toPresheafFiber_naturality a.hom, Category.assoc]
    erw [hrG j.unop]
    have hrF' : c.ι.app j ≫
        Classical.choose ((strictLocalSectionCone s).existsUnique_restriction F) =
        (strictLocalSectionCone s).restriction F j.unop := hrF j.unop
    conv_rhs => rw [← Category.assoc, hrF']
    dsimp only [PointedEtaleSectionCone.restriction]
    simp only [Category.assoc]
    let g := Scheme.strictHenselizationStructuralMap s
    let W := (Scheme.AffineEtale.Spec S).obj
      ((equivSmallModel.{u} (Scheme.strictHenselizationNeighbourhoods s)).inverse.obj
        j.unop).1
    let V := Scheme.Etale.mk (𝟙 (Scheme.strictHenselizationScheme s))
    have hu := (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} g).unit.naturality a
    have he := congrArg (fun b ↦ b.hom.app (Opposite.op W)) hu
    dsimp only [Functor.id_map, ObjectProperty.FullSubcategory.comp_hom,
      NatTrans.comp_app] at he
    rw [← Category.assoc, ← Category.assoc]
    erw [he]
    simp only [Category.assoc]
    have hn := ((upperStar AddCommGrpCat.{u + 1} g).map a).hom.naturality
      (strictLocalNeighbourhoodSection s j.unop).op
    erw [← reassoc_of% hn]
    have ht := ((Sheaf.ΓNatIsoSheafSections _ _
      (IsTerminal.isTerminalOfObj
        (MorphismProperty.Over.forget @AlgebraicGeometry.Etale ⊤
          (Scheme.strictHenselizationScheme s)) V Over.mkIdTerminal)).inv).naturality
      ((upperStar AddCommGrpCat.{u + 1} g).map a)
    change ((upperStar AddCommGrpCat.{u + 1} g).map a).hom.app (Opposite.op V) ≫ _ = _ at ht
    erw [ht]
    rfl

/-- Derive the uniquely specified restriction and use exactness of inverse image and
strict-local sections to separate the two derived functors.
Source: Stacks Project, Tags 03Q9 and 03QO. -/
noncomputable def strictLocalDerivedRestriction
    {S : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ S) :
    (Scheme.pointSmallEtale s).sheafFiber.mapDerivedCategoryPlus ⟶
      (upperStar AddCommGrpCat.{u + 1}
        (Scheme.strictHenselizationStructuralMap s)).mapDerivedCategoryPlus ⋙
      (Sheaf.Γ (Scheme.strictHenselizationScheme s).smallEtaleTopology
        AddCommGrpCat.{u + 1}).rightDerivedFunctorPlus :=
  (Scheme.pointSmallEtale s).sheafFiber.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus.inv ≫
    Functor.rightDerivedFunctorPlusNatTrans (strictLocalRestrictionNat s) ≫
    (upperStar AddCommGrpCat.{u + 1} (Scheme.strictHenselizationStructuralMap s) ⋙
      Sheaf.Γ (Scheme.strictHenselizationScheme s).smallEtaleTopology
        AddCommGrpCat.{u + 1}).rightDerivedFunctorPlusIsoMapDerivedCategoryPlus.hom ≫
    (Functor.mapDerivedCategoryPlusCompIso _ _).hom ≫
    Functor.whiskerLeft
      (upperStar AddCommGrpCat.{u + 1}
        (Scheme.strictHenselizationStructuralMap s)).mapDerivedCategoryPlus
      (Sheaf.Γ (Scheme.strictHenselizationScheme s).smallEtaleTopology
        AddCommGrpCat.{u + 1}).rightDerivedFunctorPlusIsoMapDerivedCategoryPlus.inv

/-- The comparison is germ restriction, exchange for the strict-base square, and Leray.
Source: Stacks Project, Tag 0GJV, proof of lemma-specialization-cospecialization.
(blueprint: def-weil-pbc-small-model-derived-restriction). -/
noncomputable def strictLocalSheafComparison
    {X S : Scheme.{u}} (f : X ⟶ S)
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S) :=
  (strictLocalDerivedRestriction s).app
      ((rightDerivedLowerStarPlus AddCommGrpCat.{u + 1} f).obj
        ((_root_.DerivedCategory.Plus.singleFunctor _ 0).obj G)) ≫
    (Sheaf.Γ (Scheme.strictHenselizationScheme s).smallEtaleTopology
      AddCommGrpCat.{u + 1}).rightDerivedFunctorPlus.map
      ((derivedBaseChangeMapPlus AddCommGrpCat.{u + 1}
        (IsPullback.of_hasPullback f (Scheme.strictHenselizationStructuralMap s)).toCommSq).app
        ((_root_.DerivedCategory.Plus.singleFunctor _ 0).obj G)) ≫
    (etaleLerayPlus (strictBaseChangeMap f s)).hom.app _ ≫
    (Sheaf.Γ (pullback f (Scheme.strictHenselizationStructuralMap s)).smallEtaleTopology
      AddCommGrpCat.{u + 1}).rightDerivedFunctorPlus.map
      ((Functor.mapDerivedCategoryPlusSingleFunctor
        (upperStar AddCommGrpCat.{u + 1}
          (pullback.fst f (Scheme.strictHenselizationStructuralMap s))) 0).hom.app G)

end AlgebraicGeometry.Etale
