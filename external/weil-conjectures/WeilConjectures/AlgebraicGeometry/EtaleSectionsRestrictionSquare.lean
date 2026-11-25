/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.SixFunctors.Etale.Derived.GlobalSections
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunction
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek

/-! # The sections comparison restriction square

Source: Stacks Project, Tag 03Q9, final injective-complex paragraph.
(blueprint: lem-weil-pbc-sections-comparison-restriction-square).
-/

@[expose] public section

universe v

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

namespace AlgebraicGeometry.Etale

/-- The comparison from termwise sections to derived sections respects restriction
along one morphism, before taking homology or changing a complex by an isomorphism.

Source: Stacks Project, Tag 03Q9, final injective-complex paragraph.
(blueprint: lem-weil-pbc-sections-comparison-restriction-square).

Proof: in the homotopy category the derived adjunction unit factors the image of
its underived unit followed by the direct-image derived unit. Apply derived
sections and use naturality of its unit to move the underived adjunction unit
past that unit. The composition right-derived unit factorization and the
underived isomorphism of pushforward sections with sections identify the result
with the underived restriction followed by the sections derived unit. Cancel
only the exact inverse-image localization comparison. Transport from homotopy
classes to complexes by the naturality of quotientCompQhIso. This gives the
square for every complex, including unbounded and zero complexes, without
assuming that either sections comparison is invertible. -/
theorem sectionsComparison_restriction_square {X Y : Scheme.{v}} (a : X ⟶ Y)
    (C : CochainComplex (Sheaf Y.smallEtaleTopology AddCommGrpCat.{v + 1}) ℤ) :
  let restriction :=
    Functor.whiskerRight (upperStarLowerStarAdjunction AddCommGrpCat.{v + 1} a).unit
          (Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{v + 1}) ≫
        (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft (upperStar AddCommGrpCat.{v + 1} a)
          (lowerStarCompGlobalSectionsIso AddCommGrpCat.{v + 1} a).hom
  let toDerived (Z : Scheme.{v})
      (B : CochainComplex (Sheaf Z.smallEtaleTopology AddCommGrpCat.{v + 1}) ℤ) :=
    (DerivedCategory.quotientCompQhIso AddCommGrpCat.{v + 1}).inv.app
        (((Sheaf.Γ Z.smallEtaleTopology AddCommGrpCat.{v + 1}).mapHomologicalComplex
          (.up ℤ)).obj B) ≫
      (Sheaf.Γ Z.smallEtaleTopology AddCommGrpCat.{v + 1}).rightDerivedFunctorUnit.app
        ((HomotopyCategory.quotient _ _).obj B) ≫
      (Sheaf.Γ Z.smallEtaleTopology AddCommGrpCat.{v + 1}).rightDerivedFunctor.map
        ((DerivedCategory.quotientCompQhIso _).hom.app B)
  toDerived Y C ≫
    (Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{v + 1}).rightDerivedFunctor.map
      ((mapDerivedUpperStarLowerStarAdjunction AddCommGrpCat.{v + 1} a).unit.app
        (DerivedCategory.Q.obj C)) ≫
    (rightDerivedLowerStarCompRightDerivedGlobalSectionsIso
      AddCommGrpCat.{v + 1} a).hom.app
        ((upperStar AddCommGrpCat.{v + 1} a).mapDerivedCategory.obj
          (DerivedCategory.Q.obj C)) =
    DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex restriction (.up ℤ)).app C) ≫
      toDerived X
        (((upperStar AddCommGrpCat.{v + 1} a).mapHomologicalComplex (.up ℤ)).obj C) ≫
      (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{v + 1}).rightDerivedFunctor.map
        ((upperStar AddCommGrpCat.{v + 1} a).mapDerivedCategoryFactors.inv.app C) := by
  intro restriction toDerived
  let F := upperStar AddCommGrpCat.{v + 1} a
  let R := lowerStar AddCommGrpCat.{v + 1} a
  let G := Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{v + 1}
  let H := Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{v + 1}
  let adj := upperStarLowerStarAdjunction AddCommGrpCat.{v + 1} a
  let e := lowerStarCompGlobalSectionsIso AddCommGrpCat.{v + 1} a
  let K := (HomotopyCategory.quotient _ (.up ℤ)).obj C
  -- Factor the derived adjunction unit on the homotopy class of C.
  have hη : (mapDerivedUpperStarLowerStarAdjunction AddCommGrpCat.{v + 1} a).unit.app
        (DerivedCategory.Qh.obj K) ≫
      R.rightDerivedFunctor.map (F.mapDerivedCategoryFactorsh.hom.app K) =
      DerivedCategory.Qh.map ((adj.mapHomotopyCategory (.up ℤ)).unit.app K) ≫
        R.rightDerivedFunctorUnit.app ((F.mapHomotopyCategory (.up ℤ)).obj K) :=
    (adj.mapHomotopyCategory (.up ℤ)).derivedη_fac_app
      (HomotopyCategory.quasiIso _ (.up ℤ)) F.mapDerivedCategoryFactorsh.hom
      R.rightDerivedFunctorUnit K
  -- The Leray comparison carries the composite derived unit to the sections unit.
  have hc : (Functor.rightDerivedFunctorCompUnit R G).app
        ((F.mapHomotopyCategory (.up ℤ)).obj K) ≫
      (Functor.rightDerivedFunctorCompIso' R G e).hom.app
        (DerivedCategory.Qh.obj ((F.mapHomotopyCategory (.up ℤ)).obj K)) =
      DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory e.hom (.up ℤ)).app
        ((F.mapHomotopyCategory (.up ℤ)).obj K)) ≫
      H.rightDerivedFunctorUnit.app ((F.mapHomotopyCategory (.up ℤ)).obj K) := by
    simp [Functor.rightDerivedFunctorCompIso', Functor.rightDerivedFunctorCompIso,
      Functor.rightDerivedFunctorNatIso, Functor.rightDerivedFunctorNatTrans]
    rfl
  have hi : (Functor.mapHomotopyCategoryCompIso (Iso.refl (R ⋙ G)) (.up ℤ)).inv.app
      ((F.mapHomotopyCategory (.up ℤ)).obj K) = 𝟙 _ := by
    rw [← cancel_epi
      ((Functor.mapHomotopyCategoryCompIso (Iso.refl (R ⋙ G)) (.up ℤ)).hom.app
        ((F.mapHomotopyCategory (.up ℤ)).obj K)), Iso.hom_inv_id_app]
    change 𝟙 _ = _ ≫ 𝟙 _
    rw [Functor.mapHomotopyCategoryCompIso_refl_hom_app, Category.comp_id]
  dsimp [Functor.rightDerivedFunctorCompUnit] at hc
  erw [hi] at hc
  erw [DerivedCategory.Qh.map_id] at hc
  simp only [Category.id_comp, Category.comp_id, Category.assoc] at hc
  -- Use naturality to establish the square before transporting to complexes.
  have hh : G.rightDerivedFunctorUnit.app K ≫
      G.rightDerivedFunctor.map
        ((mapDerivedUpperStarLowerStarAdjunction AddCommGrpCat.{v + 1} a).unit.app
          (DerivedCategory.Qh.obj K)) ≫
      (Functor.rightDerivedFunctorCompIso' R G e).hom.app
        (F.mapDerivedCategory.obj (DerivedCategory.Qh.obj K)) ≫
      H.rightDerivedFunctor.map (F.mapDerivedCategoryFactorsh.hom.app K) =
      DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (.up ℤ)).map
        ((NatTrans.mapHomologicalComplex restriction (.up ℤ)).app C)) ≫
      H.rightDerivedFunctorUnit.app ((F.mapHomotopyCategory (.up ℤ)).obj K) := by
    rw [← NatTrans.naturality]
    simp only [Functor.comp_map]
    erw [← G.rightDerivedFunctor.map_comp_assoc, hη,
      Functor.map_comp, Category.assoc]
    erw [← G.rightDerivedFunctorUnit.naturality_assoc]
    erw [hc]
    simp only [Functor.comp_map]
    erw [← DerivedCategory.Qh.map_comp_assoc]
    congr 2
    erw [Adjunction.mapHomotopyCategory_unit_app_quotient,
      Functor.mapHomotopyCategory_map]
    simp only [NatTrans.mapHomotopyCategory_app]
    erw [← Functor.map_comp]
    congr 1
  -- Only the exact inverse-image localization comparison is cancelled.
  rw [← cancel_mono (H.rightDerivedFunctor.map
    (F.mapDerivedCategoryFactors.hom.app C))]
  simp only [toDerived, Category.assoc]
  dsimp only [K] at hh
  rw [Functor.mapDerivedCategoryFactorsh_hom_app] at hh
  dsimp only [DerivedCategory.quotientCompQhIso,
    HomologicalComplexUpToQuasiIso.quotientCompQhIso] at hh ⊢
  repeat erw [CategoryTheory.Functor.map_id] at hh
  repeat erw [Category.id_comp] at hh
  repeat erw [Category.comp_id] at hh
  repeat erw [CategoryTheory.Functor.map_id]
  repeat erw [Category.id_comp]
  erw [← H.rightDerivedFunctor.map_comp, Iso.inv_hom_id_app,
    CategoryTheory.Functor.map_id, Category.comp_id]
  exact hh

end AlgebraicGeometry.Etale
