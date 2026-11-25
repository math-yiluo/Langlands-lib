/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.OpenPinnedSingleDegreeZeroCounitIso
public import WeilConjectures.AlgebraicGeometry.PinnedPullbackCompositionShifts
import all WeilConjectures.AlgebraicGeometry.OpenPinnedSourceCounitTriangle

/-! # Counit comparison for one open leg
Source: Stacks Project, Tags 08DW and 0D5S. -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory Limits
noncomputable section
namespace AlgebraicGeometry
private theorem targetHomotopyComparison
    {C D E : Type*} [Category C] [Preadditive C] [Category D] [Preadditive D]
    [Category E] [Preadditive E]
    {F : C ⥤ D} {G R : D ⥤ E} {H : C ⥤ E}
    [F.Additive] [G.Additive] [R.Additive] [H.Additive]
    (e : G ≅ R) (a : F ⋙ G ≅ H) (P : HomotopyCategory C (.up ℤ)) :
    (Functor.mapHomotopyCategoryCompIso a (.up ℤ)).hom.app P ≫
        (Functor.mapHomotopyCategoryCompIso
          (Functor.isoWhiskerLeft F e.symm ≪≫ a) (.up ℤ)).inv.app P =
      (NatTrans.mapHomotopyCategory e.hom (.up ℤ)).app
        ((F.mapHomotopyCategory (.up ℤ)).obj P) := by
  obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective P
  change (HomotopyCategory.quotient E (.up ℤ)).map
      ((Functor.mapHomologicalComplexCompIso a (.up ℤ)).hom.app K) ≫
    (HomotopyCategory.quotient E (.up ℤ)).map
      ((Functor.mapHomologicalComplexCompIso
        (Functor.isoWhiskerLeft F e.symm ≪≫ a) (.up ℤ)).inv.app K) =
    (HomotopyCategory.quotient E (.up ℤ)).map
      ((NatTrans.mapHomologicalComplex e.hom (.up ℤ)).app
        ((F.mapHomologicalComplex (.up ℤ)).obj K))
  rw [← Functor.map_comp]
  congr 1
  ext n
  simp [Functor.mapHomologicalComplexCompIso, NatIso.mapHomologicalComplex,
    NatTrans.mapHomologicalComplex]

private theorem targetOpenFactor
    {C : Type*} [Category C] {A B D E : C}
    (i : B ⟶ A) [Epi i] (h : A ⟶ B) (ε : A ⟶ D) (r : B ⟶ E)
    (v : D ⟶ E) (vi : E ⟶ D)
    (hih : i ≫ h = 𝟙 B) (hε : i ≫ ε = r ≫ vi) (hv : vi ≫ v = 𝟙 E) :
    h ≫ r = ε ≫ v := by
  apply (cancel_epi i).mp
  rw [← Category.assoc, hih, Category.id_comp, ← Category.assoc, hε,
    Category.assoc, hv, Category.comp_id]

private theorem targetTriangleAlgebra
    {C : Type*} [Category C] {A B D E F G H I : C}
    (a : A ⟶ B) (b : B ⟶ D) (d : D ⟶ E)
    (l : A ⟶ F) (n : F ⟶ D) (m : F ⟶ G) (e : G ⟶ E)
    (c : A ⟶ H) (ε : H ⟶ I) (h : G ⟶ I) (t : I ⟶ E)
    (hn : a ≫ b = l ≫ n) (ho : n ≫ d = m ≫ e)
    (hc : c ≫ ε = l ≫ m ≫ h) (ht : h ≫ t = e) :
    a ≫ b ≫ d = c ≫ ε ≫ t := by
  calc
    a ≫ b ≫ d = (a ≫ b) ≫ d := by simp only [Category.assoc]
    _ = (l ≫ n) ≫ d := by rw [hn]
    _ = l ≫ (m ≫ e) := by rw [Category.assoc, ho]
    _ = l ≫ m ≫ (h ≫ t) := by rw [ht]
    _ = (l ≫ m ≫ h) ≫ t := by simp only [Category.assoc]
    _ = c ≫ ε ≫ t := by rw [← hc, Category.assoc]

variable [∀ Y : Scheme.{u}, HasDerivedCategory.{w}
  (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
  [∀ {Y Z : Scheme.{u}} (k : Y ⟶ Z), (Scheme.Modules.tensorPullback k).Additive]

/-- Termwise comparison for restricting the target of a composite tensor pullback.
Source: Stacks Project, Tags 08DW and 0D5S.
(blueprint: lem-pc-open-pinned-target-counit-triangle). -/
def openPinnedHomotopyTargetCompositionIso
    {X X' : Scheme.{u}} (k : X' ⟶ X) (U' : X'.Opens) :
    (Scheme.Modules.tensorPullback (U'.ι ≫ k)).mapHomotopyCategory (.up ℤ) ≅
      (Scheme.Modules.tensorPullback k).mapHomotopyCategory (.up ℤ) ⋙
        (schemeOpenRestriction X' U').mapHomotopyCategory (.up ℤ) := by
  dsimp only [Scheme.Modules, Scheme.ringCatSheaf] at *
  exact (Functor.mapHomotopyCategoryCompIso
    (Functor.isoWhiskerLeft _ (openPinnedTensorOpenIso X' U').symm ≪≫
      (Scheme.Modules.tensorPullbackCompositionIso U'.ι k (U'.ι ≫ k) rfl).symm)
    (.up ℤ)).symm

-- Compare the chosen functors through their interfaces, without expanding sheaf data.
attribute [local irreducible] Scheme.Modules.tensorPullbackCompositionIso
  Scheme.Modules.tensorPullback Scheme.Modules.tensorPullbackObj
attribute [local instance_reducible] Scheme.Modules TopCat.Sheaf
attribute [local implicit_reducible] DerivedCategory
  HomotopyCategory DerivedCategory.Q DerivedCategory.Qh
attribute [local irreducible] singleComplexOpenPullbackIso openPinnedTensorOpenIso

-- The four factorization equations compare several selected localization functors.
/-- The target-open leg of the derived counit composition calculation.
Source: Stacks Project, Tags 08DW and 0D5S.
(blueprint: lem-pc-open-pinned-target-counit-triangle).
Proof: naturality of the open-pullback comparison moves the counit for k
past its component. The factorization equation of leftDerivedUnique identifies
that comparison followed by the exact restriction factor with the counit for
U' inclusion followed by the localized underived open tensor comparison.
The selected composition comparison factors the successive counits through
its composite counit. Combine these two equations and functoriality of Qh.
This uses no source open or commuting square, and applies to every complex,
including zero complexes and the empty open. -/
theorem open_pinned_target_counit_triangle
    {X X' : Scheme.{u}} (k : X' ⟶ X) (U' : X'.Opens)
    (P : HomotopyCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace)) (.up ℤ)) :
    (singleComplexOpenPullbackIso X' U').hom.app
        ((derivedPullback k).obj (DerivedCategory.Qh.obj P)) ≫
      (schemeOpenRestriction X' U').mapDerivedCategory.map
        ((pinnedPullbackCounit.{u, w} k).app P) ≫
      (schemeOpenRestriction X' U').mapDerivedCategoryFactorsh.hom.app
        ((Scheme.Modules.tensorPullback k).mapHomotopyCategory (.up ℤ) |>.obj P) =
    (pinnedPullbackComposition.{u, w} U'.ι k).hom.app (DerivedCategory.Qh.obj P) ≫
      (pinnedPullbackCounit.{u, w} (U'.ι ≫ k)).app P ≫
      DerivedCategory.Qh.map ((openPinnedHomotopyTargetCompositionIso k U').hom.app P) := by
  have : (schemeOpenRestriction X' U').Additive := schemeOpenRestriction_additive X' U'
  let E : HomotopyCategory
      (SheafOfModules.{u} (moduleRings X'.toRingedSpace)) (.up ℤ) :=
    ((Scheme.Modules.tensorPullback k).mapHomotopyCategory (.up ℤ)).obj P
  let e := openPinnedTensorOpenIso X' U'
  let q := DerivedCategory.Qh
    (C := SheafOfModules.{u} (moduleRings U'.toScheme.toRingedSpace))
  let v := (NatTrans.mapHomotopyCategory e.hom (.up ℤ)).app E
  let vi := (NatTrans.mapHomotopyCategory e.inv (.up ℤ)).app E
  have ho := openCounit.{u, w} X' U' E
  have hi := mappedHomotopyInvHom e E q
  have ho' := targetOpenFactor
    ((singleComplexOpenPullbackIso X' U').inv.app (DerivedCategory.Qh.obj E))
    ((singleComplexOpenPullbackIso X' U').hom.app (DerivedCategory.Qh.obj E))
    ((pinnedPullbackCounit.{u, w} U'.ι).app E)
    ((schemeOpenRestriction X' U').mapDerivedCategoryFactorsh.hom.app E)
    (q.map v) (q.map vi)
    ((singleComplexOpenPullbackIso X' U').inv_hom_id_app (DerivedCategory.Qh.obj E)) ho hi
  have hc := compositionCounit.{u, w} U'.ι k P
  have ht := targetHomotopyComparison e
    (Scheme.Modules.tensorPullbackCompositionIso U'.ι k (U'.ι ≫ k) rfl).symm P
  have hg := congrArg q.map ht
  simp only [q.map_comp] at hg
  have hn := (singleComplexOpenPullbackIso X' U').hom.naturality
    ((pinnedPullbackCounit.{u, w} k).app P)
  exact targetTriangleAlgebra _ _ _ _ _ _ _ _ _ _ _ hn.symm ho' hc hg

end AlgebraicGeometry
