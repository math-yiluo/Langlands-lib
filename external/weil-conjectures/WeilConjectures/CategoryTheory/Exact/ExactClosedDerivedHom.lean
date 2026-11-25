/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.DualizableTransfer
public import WeilConjectures.AlgebraicGeometry.IntegralResidueDerivedMonoidal
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.ClosedTriangulated
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
import all WeilConjectures.CategoryTheory.ExactMonoidalEquivalenceDerived
/-! # Exact closed functors preserve unbounded derived internal Hom -/
@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
universe u c d
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed
namespace CategoryTheory
namespace Functor
/-- The canonical internal-Hom comparison component, shared without unfolding the closed
adjunction. Source: the tensor-Hom evaluation transpose
(blueprint: lem-sf-exact-closed-derived-hom). -/
@[irreducible]
def closedComparison {C D : Type*} [Category C] [Category D]
    [MonoidalCategory C] [MonoidalCategory D] [MonoidalClosed C] [MonoidalClosed D]
    (F : C ⥤ D) [F.LaxMonoidal] (K M : C) :
    F.obj ((ihom K).obj M) ⟶ (ihom (F.obj K)).obj (F.obj M) :=
  (LaxMonoidal.ihomComparison F K).app M
end Functor
section Square
open Category Functor.LaxMonoidal
variable {A B E H : Type*} [Category A] [Category B] [Category E] [Category H]
  [MonoidalCategory A] [MonoidalCategory B] [MonoidalCategory E] [MonoidalCategory H]
  [MonoidalClosed A] [MonoidalClosed B] [MonoidalClosed E] [MonoidalClosed H]
  (Q : A ⥤ B) (R : E ⥤ H) (F : A ⥤ E) (G : B ⥤ H)
  [Q.LaxMonoidal] [R.LaxMonoidal] [F.LaxMonoidal] [G.LaxMonoidal]
  (e : Q ⋙ G ≅ F ⋙ R) [NatTrans.IsMonoidal e.hom] (K M : A)
private theorem comparison_square :
    G.map ((ihomComparison Q K).app M) ≫
        (ihomComparison G (Q.obj K)).app (Q.obj M) ≫
        (pre (e.inv.app K)).app (G.obj (Q.obj M)) ≫
        (ihom (R.obj (F.obj K))).map (e.hom.app M) =
      e.hom.app ((ihom K).obj M) ≫
        R.map ((ihomComparison F K).app M) ≫
        (ihomComparison R (F.obj K)).app (F.obj M) := by
  have q := ihomComparison_app_comp_map_app e.inv K M
  have q' := congrArg (fun f ↦ e.hom.app ((ihom K).obj M) ≫ f ≫
    (ihom (R.obj (F.obj K))).map (e.hom.app M)) q
  simp only [Functor.comp_obj, ihomComparison_comp_app] at q'
  simp only [← Functor.map_comp, Iso.inv_hom_id_app, Category.assoc,
    Iso.hom_inv_id_app_assoc] at q'
  erw [Functor.map_id, Category.comp_id] at q'
  exact q'.symm
end Square
end CategoryTheory
namespace CategoryTheory.Functor
variable {C : Type c} [Category.{u + 1} C] [Abelian C]
  [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C] [MonoidalPreadditive C]
  [MonoidalClosed C] [BraidedCategory C] [Abelian.HasFunctorialFlatResolution C]
  {D : Type d} [Category.{u + 1} D] [Abelian D]
  [IsGrothendieckAbelian.{u + 1} D] [MonoidalCategory D] [MonoidalPreadditive D]
  [MonoidalClosed D] [BraidedCategory D] [Abelian.HasFunctorialFlatResolution D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [F.PreservesFlat] [F.IsLeftAdjoint] [F.Monoidal]
@[instance_reducible]
private noncomputable def homotopyClosed :
    MonoidalClosed (HomotopyCategory C (.up ℤ)) where
  closed P := ⟨HomotopyCategory.internalHom P, HomotopyCategory.tensorHomAdjunction P⟩
attribute [local instance] homotopyClosed
@[instance_reducible]
private noncomputable def mapHomotopyMonoidal :
    (F.mapHomotopyCategory (.up ℤ)).Monoidal := by
  letI : (F.mapHomotopyCategory (.up ℤ)).OplaxMonoidal :=
    Functor.mapHomotopyCategoryOplaxMonoidal F
  have : IsIso (Functor.OplaxMonoidal.η (F.mapHomotopyCategory (.up ℤ))) := by
    rw [Functor.mapHomotopyCategory_η]
    infer_instance
  have (X Y : HomotopyCategory C (.up ℤ)) :
      IsIso (Functor.OplaxMonoidal.δ (F.mapHomotopyCategory (.up ℤ)) X Y) :=
    inferInstanceAs (IsIso (((Functor.OplaxMonoidal.mapHomotopyCategoryδNatTrans
      (.up ℤ) F).app X).app Y))
  exact .ofOplaxMonoidal _

attribute [local instance] mapHomotopyMonoidal

omit [Abelian.HasFunctorialFlatResolution C] [Abelian.HasFunctorialFlatResolution D]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F] [F.PreservesFlat] in
private theorem mapHomotopyFactors_monoidal :
    NatTrans.IsMonoidal (F.mapHomotopyCategoryFactors (.up ℤ)).hom := by
  apply ExactMonoidalEquivalenceDerived.monoidal_of_oplax
  · change 𝟙 _ ≫ (HomotopyCategory.quotient D (.up ℤ)).map
        (OplaxMonoidal.η (F.mapHomologicalComplex (.up ℤ))) ≫ 𝟙 _ =
      (F.mapHomotopyCategory (.up ℤ)).map (𝟙 _) ≫
        (HomotopyCategory.quotient D (.up ℤ)).map
          (OplaxMonoidal.η (F.mapHomologicalComplex (.up ℤ)))
    rw [Category.id_comp, Category.comp_id, CategoryTheory.Functor.map_id, Category.id_comp]
  · intro K L
    change 𝟙 _ ≫ (HomotopyCategory.quotient D (.up ℤ)).map
        (OplaxMonoidal.δ (F.mapHomologicalComplex (.up ℤ)) K L) ≫ 𝟙 _ =
      ((F.mapHomotopyCategory (.up ℤ)).map (𝟙 _) ≫
        (HomotopyCategory.quotient D (.up ℤ)).map
          (((Functor.OplaxMonoidal.mapHomologicalComplexδNatTrans (.up ℤ) F).app K).app L)) ≫
        (𝟙 _ ⊗ₘ 𝟙 _)
    rw [Category.id_comp, Category.comp_id, CategoryTheory.Functor.map_id,
      Category.id_comp]
    erw [tensorHom_id, id_whiskerRight, Category.comp_id]
    rfl

attribute [local instance] CochainComplex.monoidalClosed
omit [Abelian.HasFunctorialFlatResolution C] in
/-- The canonical strong tensor structure on an exact derived functor, transported from
its K-flat left derived functor. Source: Stacks 07A4
(blueprint: lem-sf-exact-closed-derived-hom). -/
@[irreducible]
noncomputable def exactClosedDerivedMonoidal : F.mapDerivedCategory.Monoidal :=
  letI := F.residueDerivedMonoidal
  Functor.Monoidal.transport F.leftDerivedFunctorIsoMapDerivedCategory
attribute [local instance] exactClosedDerivedMonoidal
private theorem derivedFactorsh_monoidal :
    NatTrans.IsMonoidal F.mapDerivedCategoryFactorsh.hom := by
  unfold exactClosedDerivedMonoidal
  letI := F.residueDerivedMonoidal
  letI := Functor.Monoidal.transport F.leftDerivedFunctorIsoMapDerivedCategory
  have hc : NatTrans.IsMonoidal F.leftDerivedFunctorCounit := by
    have := DerivedCategory.isIso_ε_Qh D
    apply ExactMonoidalEquivalenceDerived.square_monoidal DerivedCategory.Qh DerivedCategory.Qh
      (F.mapHomotopyCategory (.up ℤ)) F.leftDerivedFunctor F.leftDerivedFunctorCounit
    · rfl
    · exact F.residueDerivedMonoidal_counit
  have hm : NatTrans.IsMonoidal F.leftDerivedFunctorIsoMapDerivedCategory.hom :=
    Functor.Monoidal.natTransIsMonoidal_of_transport F.leftDerivedFunctorIsoMapDerivedCategory
  have hi : NatTrans.IsMonoidal F.leftDerivedFunctorIsoMapDerivedCategory.inv := inferInstance
  have h : F.mapDerivedCategoryFactorsh.hom =
      (Functor.isoWhiskerLeft DerivedCategory.Qh
        F.leftDerivedFunctorIsoMapDerivedCategory.symm).hom ≫
          F.leftDerivedFunctorCounit := by
    apply NatTrans.ext
    funext K
    have hf := NatTrans.congr_app F.leftDerivedFunctorIsoMapDerivedCategory_hom_fac K
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app] at hf
    simp only [NatTrans.comp_app, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
      Iso.symm_hom, ← hf, Iso.inv_hom_id_app_assoc]
  rw [h]
  dsimp only [Functor.isoWhiskerLeft_hom, Iso.symm_hom]
  apply NatTrans.IsMonoidal.comp
variable {L : D ⥤ C} [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
  (adj : L ⊣ F) [∀ P : C, IsIso (Functor.LaxMonoidal.ihomComparison F P)]
end CategoryTheory.Functor
