/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.SingleComplexOpenTensorRestrictionIso
public import Mathlib.Algebra.Homology.Localization

import all Mathlib.Algebra.Homology.Localization

/-! # The representative of ordinary open tensor restriction

Source: Stacks Project, Tags 08HY and 08DW.
(blueprint: lem-pc-open-tensor-restriction-representative).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry
open SingleComplexBaseChange
private theorem localize_termwise_comparison
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory.{w} B] [HasDerivedCategory.{w} D]
    (F : C ⥤ B) (G : C ⥤ A) (T : A ⥤ D) (R : B ⥤ D)
    [F.Additive] [G.Additive] [T.Additive] [R.Additive]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    (e : F ⋙ R ≅ G ⋙ T) (P : CochainComplex C ℤ) :
    let a := (NatTrans.mapHomologicalComplex e.inv (.up ℤ)).app P
    let N := (F.mapHomologicalComplex (.up ℤ)).obj P
    let h := Functor.mapHomotopyCategoryCompIso e (.up ℤ) ≪≫
      (Functor.mapHomotopyCategoryCompIso (Iso.refl (G ⋙ T)) (.up ℤ)).symm
    DerivedCategory.Qh.map (h.inv.app ((HomotopyCategory.quotient C (.up ℤ)).obj P)) ≫
        R.mapDerivedCategoryFactorsh.inv.app
          ((F.mapHomotopyCategory (.up ℤ)).obj
            ((HomotopyCategory.quotient C (.up ℤ)).obj P)) =
      DerivedCategory.Q.map a ≫ R.mapDerivedCategoryFactors.inv.app N := by
  dsimp only
  let a := (NatTrans.mapHomologicalComplex e.inv (.up ℤ)).app P
  let N := (F.mapHomologicalComplex (.up ℤ)).obj P
  have hh : R.mapDerivedCategoryFactorsh.hom.app
      ((HomotopyCategory.quotient B (.up ℤ)).obj N) =
      R.mapDerivedCategoryFactors.hom.app N := by
    rw [Functor.mapDerivedCategoryFactorsh_hom_app]
    change R.mapDerivedCategory.map (𝟙 _) ≫
      R.mapDerivedCategoryFactors.hom.app N ≫ 𝟙 _ ≫
      DerivedCategory.Qh.map (𝟙 _) = _
    rw [R.mapDerivedCategory.map_id, DerivedCategory.Qh.map_id]
    simp only [Category.id_comp]
    exact Category.comp_id _
  have hi : R.mapDerivedCategoryFactorsh.inv.app
      ((HomotopyCategory.quotient B (.up ℤ)).obj N) =
      R.mapDerivedCategoryFactors.inv.app N := by
    apply (cancel_mono (R.mapDerivedCategoryFactors.hom.app N)).mp
    rw [← hh, Iso.inv_hom_id_app, hh, Iso.inv_hom_id_app]
    rfl
  have ha : (Functor.mapHomotopyCategoryCompIso e (.up ℤ) ≪≫
      (Functor.mapHomotopyCategoryCompIso (Iso.refl (G ⋙ T)) (.up ℤ)).symm).inv.app
      ((HomotopyCategory.quotient C (.up ℤ)).obj P) =
      (HomotopyCategory.quotient D (.up ℤ)).map a := by
    change (HomotopyCategory.quotient D (.up ℤ)).map (𝟙 _) ≫
      (HomotopyCategory.quotient D (.up ℤ)).map a = _
    rw [(HomotopyCategory.quotient D (.up ℤ)).map_id, Category.id_comp]
  erw [ha, hi]
  have hq := DerivedCategory.quotientCompQhIso_hom_naturality a
  change DerivedCategory.Qh.map ((HomotopyCategory.quotient D (.up ℤ)).map a) ≫ 𝟙 _ =
    𝟙 _ ≫ DerivedCategory.Q.map a at hq
  simpa only [Category.comp_id, Category.id_comp] using
    congrArg (fun t ↦ t ≫ R.mapDerivedCategoryFactors.inv.app N) hq


attribute [local irreducible] openPinnedTensorRestrictionIso

-- Compare the homotopy and complex localization factors without unfolding the pinned iso.
/-- The ordinary tensor restriction map is the localization of the termwise map
followed by the inverse exact restriction factor.

Proof: expand singleComplexOpenTensorRestrictionMap. At the homotopy quotient
of P, mapHomotopyCategoryCompIso is the quotient of mapHomologicalComplexCompIso.
The identity composition comparison has identity components, so the inverse
pinned homotopy comparison is the quotient of the displayed chain map. Use
quotientCompQhIso naturality for this chain map. Expand
mapDerivedCategoryFactorsh_hom_app for the target restriction, then invert that
identity. Its quotient-comparison factors cancel those of naturality, giving
Q.map of the termwise map followed by mapDerivedCategoryFactors.inv. No exactness
of tensor pullback is asserted or used: only open restriction is exact. This
works for every complex, including the zero complex and top or empty opens.
Source: Stacks Project, Tags 08HY, 08DW and 015F; homotopy and exact localization
factorization identities.
(blueprint: lem-pc-open-tensor-restriction-representative). -/
theorem openTensorRestriction_representative
    [d : ∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X X' : Scheme.{u}} (g' : X' ⟶ X)
    (U : X.Opens) (U' : X'.Opens) (j : U'.toScheme ⟶ U.toScheme)
    (hj : j ≫ U.ι = U'.ι ≫ g')
    (P : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ) :
    letI : (schemeOpenRestriction X U).Additive := schemeOpenRestriction_additive X U
    letI : (schemeOpenRestriction X' U').Additive := schemeOpenRestriction_additive X' U'
    letI : ∀ {Y Z : Scheme.{u}} (k : Y ⟶ Z),
      (Scheme.Modules.tensorPullback k).Additive := fun k ↦ tensorPullbackAdditive k
    letI : (Scheme.Modules.tensorPullback g').Additive := tensorPullbackAdditive g'
    letI : (Scheme.Modules.tensorPullback j).Additive := tensorPullbackAdditive j
    letI : (schemeOpenRestriction X U).PreservesZeroMorphisms :=
      Functor.preservesZeroMorphisms_of_additive _
    letI : (schemeOpenRestriction X' U').PreservesZeroMorphisms :=
      Functor.preservesZeroMorphisms_of_additive _
    letI : (Scheme.Modules.tensorPullback g').PreservesZeroMorphisms :=
      Functor.preservesZeroMorphisms_of_additive _
    letI : (Scheme.Modules.tensorPullback j).PreservesZeroMorphisms :=
      Functor.preservesZeroMorphisms_of_additive _
    let e : Scheme.Modules.tensorPullback g' ⋙ schemeOpenRestriction X' U' ≅
        schemeOpenRestriction X U ⋙ Scheme.Modules.tensorPullback j :=
      openPinnedTensorRestrictionIso g' U U' j hj
    let a := (NatTrans.mapHomologicalComplex e.inv (.up ℤ)).app P
    let N : CochainComplex (SheafOfModules.{u} (moduleRings X'.toRingedSpace)) ℤ :=
    ((Scheme.Modules.tensorPullback g').mapHomologicalComplex (.up ℤ)).obj P
    singleComplexOpenTensorRestrictionMap g' U U' j hj P =
      DerivedCategory.Q.map a ≫
        (schemeOpenRestriction X' U').mapDerivedCategoryFactors.inv.app N := by
  rfl

end AlgebraicGeometry
