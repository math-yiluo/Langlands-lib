/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.Localization
public import Mathlib.Logic.Small.Defs
import all Mathlib.Logic.Small.Defs
import all Mathlib.Algebra.Homology.Localization
import all WeilConjectures.AlgebraicGeometry.SectionDerivedPushpullNormalization
public import WeilConjectures.AlgebraicGeometry.QuotientSectionTensor.QuotientSectionTensorData
import WeilConjectures.SixFunctors.Supporting.ModCondensedCachedInstances
import all WeilConjectures.AlgebraicGeometry.QuotientSectionTensor.QuotientSectionPullTransportScalarComputation
import WeilConjectures.AlgebraicGeometry.QuotientSectionTensor.QuotientSectionPullTransportGeometricComputation

/-! # Pullback compatibility on scalar-computed representatives

## References

* Stacks 06YY, 0D6D and 07A6
-/

@[expose] public noncomputable section
set_option autoImplicit false
-- Share the large inferred cochain structures while checking the diagram proof.
set_option Elab.async false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false

attribute [local irreducible] CategoryTheory.Functor.leftDerivedFunctor
  CategoryTheory.Functor.mapDerivedCategory
  HasDerivedCategory.standard
  DerivedCategory.monoidalClosed CategoryTheory.Mod.monoidalClosed
  AlgebraicGeometry.ProEtale.upperStarFromPoint
  CategoryTheory.Sheaf.monoidalCategory
  DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj ChangeOfRings
open scoped AlgebraicGeometry.ProEtale.CondensedRing.CachedModInstances

namespace AlgebraicGeometry.ProEtale.QuotientSectionTensor

open QuotientChange IntegralQuotient

attribute [local instance] ModuleRingedComparison.sectionFunctorAdditive

attribute [local semireducible] QuotientChange.L
attribute [local implicit_reducible] QuotientChange.L
  InternalAbelianSheafModule.sectionRingSheaf
  DerivedCategory.Q DerivedCategory.Qh
  CategoryTheory.catToReflQuiver
  GrothendieckTopology.monoidalCategory_sheaf_of_essentiallySmall
  GrothendieckTopology.braidedCategory_sheaf_of_essentiallySmall
  GrothendieckTopology.symmetricCategory_sheaf_of_essentiallySmall
  AlgebraicGeometry.ProEtale.sheafMonoidalCategory
  AlgebraicGeometry.ProEtale.sheafBraidedCategory
  AlgebraicGeometry.ProEtale.sheafSymmetricCategory

-- Extract a normalization field without repeating its large remaining conjunction.
-- Give lifted comparisons iterated functor types at their construction boundary.
private def complex_iso
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    [Preadditive A] [Preadditive B] [Preadditive C] [Preadditive D]
    {F : A ⥤ B} {G : B ⥤ D} {H : A ⥤ C} {I : C ⥤ D}
    [F.Additive] [G.Additive] [H.Additive] [I.Additive]
    (e : F ⋙ G ≅ H ⋙ I) :
    F.mapHomologicalComplex (.up ℤ) ⋙ G.mapHomologicalComplex (.up ℤ) ≅
      H.mapHomologicalComplex (.up ℤ) ⋙ I.mapHomologicalComplex (.up ℤ) :=
  Functor.mapHomologicalComplexCompIso e (.up ℤ) ≪≫
    (Functor.mapHomologicalComplexCompIso (Iso.refl (H ⋙ I)) (.up ℤ)).symm

private def complex_comp_iso
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    [Preadditive A] [Preadditive B] [Preadditive C] [Preadditive D]
    {F : A ⥤ B} {G : B ⥤ D} {H : A ⥤ C} {I : C ⥤ D}
    [F.Additive] [G.Additive] [H.Additive] [I.Additive]
    (e : F ⋙ G ≅ H ⋙ I) :
    F.mapHomologicalComplex (.up ℤ) ⋙ G.mapHomologicalComplex (.up ℤ) ≅
      H.mapHomologicalComplex (.up ℤ) ⋙ I.mapHomologicalComplex (.up ℤ) :=
  complex_iso e

private theorem complex_iso_hom_app
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    [Preadditive A] [Preadditive B] [Preadditive C] [Preadditive D]
    {F : A ⥤ B} {G : B ⥤ D} {H : A ⥤ C} {I : C ⥤ D}
    [F.Additive] [G.Additive] [H.Additive] [I.Additive]
    (e : F ⋙ G ≅ H ⋙ I) (P : CochainComplex A ℤ) :
    (complex_iso e).hom.app P = (NatIso.mapHomologicalComplex e (.up ℤ)).hom.app P := by
  apply HomologicalComplex.hom_ext
  intro n
  simp only [complex_iso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    HomologicalComplex.comp_f, Functor.mapHomologicalComplexCompIso_hom_app_f,
    Functor.mapHomologicalComplexCompIso_inv_app_f, Iso.refl_inv, NatTrans.id_app,
    NatIso.mapHomologicalComplex_hom_app_f]
  erw [Category.comp_id]

private theorem complex_comp_iso_hom_app
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    [Preadditive A] [Preadditive B] [Preadditive C] [Preadditive D]
    {F : A ⥤ B} {G : B ⥤ D} {H : A ⥤ C} {I : C ⥤ D}
    [F.Additive] [G.Additive] [H.Additive] [I.Additive]
    (e : F ⋙ G ≅ H ⋙ I) (P : CochainComplex A ℤ) :
    (complex_comp_iso e).hom.app P =
      (Functor.mapHomologicalComplexCompIso e (.up ℤ)).hom.app P := by
  change (complex_iso e).hom.app P = _
  rw [complex_iso_hom_app]
  rfl

private theorem complex_square
    {A B C D A' B' C' D' : Type*}
    [Category A] [Category B] [Category C] [Category D]
    [Category A'] [Category B'] [Category C'] [Category D']
    [Preadditive A] [Preadditive B] [Preadditive C] [Preadditive D]
    [Preadditive A'] [Preadditive B'] [Preadditive C'] [Preadditive D']
    (G : A ⥤ B) (H : C ⥤ D) (S : A ⥤ C) (T : B ⥤ D)
    (g : A' ⥤ B') (h : C' ⥤ D') (s : A' ⥤ C') (t : B' ⥤ D')
    (EA : A ⥤ A') (EB : B ⥤ B') (EC : C ⥤ C') (ED : D ⥤ D')
    [G.Additive] [H.Additive] [S.Additive] [T.Additive]
    [g.Additive] [h.Additive] [s.Additive] [t.Additive]
    [EA.Additive] [EB.Additive] [EC.Additive] [ED.Additive]
    (α : S ⋙ EC ≅ EA ⋙ s) (β : T ⋙ ED ≅ EB ⋙ t)
    (γ : G ⋙ EB ≅ EA ⋙ g) (δ : H ⋙ ED ≅ EC ⋙ h)
    (b : S ⋙ H ≅ G ⋙ T) (c : s ⋙ h ≅ g ⋙ t)
    (ho : ∀ M, ED.map (b.hom.app M) ≫ β.hom.app (G.obj M) ≫ t.map (γ.hom.app M) =
      δ.hom.app (S.obj M) ≫ h.map (α.hom.app M) ≫ c.hom.app (EA.obj M))
    (P : CochainComplex A ℤ) :
    (ED.mapHomologicalComplex (.up ℤ)).map
        ((complex_comp_iso b).hom.app P) ≫
      (complex_iso β).hom.app
        ((G.mapHomologicalComplex (.up ℤ)).obj P) ≫
      (t.mapHomologicalComplex (.up ℤ)).map
        ((complex_iso γ).hom.app P) =
    (complex_iso δ).hom.app
        ((S.mapHomologicalComplex (.up ℤ)).obj P) ≫
      (h.mapHomologicalComplex (.up ℤ)).map
        ((complex_iso α).hom.app P) ≫
      (complex_comp_iso c).hom.app
        ((EA.mapHomologicalComplex (.up ℤ)).obj P) := by
  simp only [complex_iso_hom_app, complex_comp_iso_hom_app]
  apply HomologicalComplex.hom_ext
  intro n
  dsimp only [Functor.mapHomologicalComplex] at *
  simpa only [HomologicalComplex.comp_f,
    Functor.mapHomologicalComplex_map_f,
    NatIso.mapHomologicalComplex_hom_app_f,
    Functor.mapHomologicalComplexCompIso_hom_app_f,
    Functor.mapHomologicalComplex_obj_X, Functor.comp_obj] using ho (P.X n)

private theorem qh_map_quotient
    {A : Type*} [Category* A] [Abelian A] [HasDerivedCategory A]
    {P Q : CochainComplex A ℤ} (t : P ⟶ Q) :
    DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (.up ℤ)).map t) =
      DerivedCategory.Q.map t := by
  have h := DerivedCategory.quotientCompQhIso_hom_naturality t
  change DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (.up ℤ)).map t) ≫
    𝟙 _ = 𝟙 _ ≫ DerivedCategory.Q.map t at h
  simpa only [Category.id_comp, Category.comp_id] using h

private theorem qh_compositor
    {A B C : Type*} [Category A] [Category B] [Category C]
    [Preadditive A] [Preadditive B] [Abelian C] [HasDerivedCategory C]
    (F : A ⥤ B) (G : B ⥤ C) (H : A ⥤ C)
    [F.Additive] [G.Additive] [H.Additive]
    (e : F ⋙ G ≅ H) (P : CochainComplex A ℤ) :
    DerivedCategory.Qh.map
        ((Functor.mapHomotopyCategoryCompIso e (.up ℤ)).hom.app
          ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) =
      DerivedCategory.Q.map ((Functor.mapHomologicalComplexCompIso e (.up ℤ)).hom.app P)
    := by
  change DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (.up ℤ)).map _) = _
  exact qh_map_quotient _

-- Reindex normalization while all four ordinary functors remain abstract.
private theorem cochain_normalization
    {A : Type*} [Category* A] [Abelian A] [HasDerivedCategory A]
    {B : Type*} [Category* B] [Abelian B] [HasDerivedCategory B]
    {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]
    {D : Type*} [Category* D] [Abelian D] [HasDerivedCategory D]
    (S : A ⥤ C) (T : B ⥤ D) (G : A ⥤ B) (H : C ⥤ D)
    [S.Additive] [T.Additive] [G.Additive] [H.Additive]
    (sd : DerivedCategory A ⥤ DerivedCategory C)
    (td : DerivedCategory B ⥤ DerivedCategory D)
    (gd : DerivedCategory A ⥤ DerivedCategory B)
    (hd : DerivedCategory C ⥤ DerivedCategory D)
    (εS : DerivedCategory.Qh ⋙ sd ⟶ S.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (εT : DerivedCategory.Qh ⋙ td ⟶ T.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (εG : DerivedCategory.Qh ⋙ gd ⟶ G.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (εH : DerivedCategory.Qh ⋙ hd ⟶ H.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (b : sd ⋙ hd ≅ gd ⋙ td) (bC : S ⋙ H ≅ G ⋙ T)
    (hn : ∀ P : HomotopyCategory A (.up ℤ),
      b.hom.app (DerivedCategory.Qh.obj P) ≫ td.map (εG.app P) ≫
          εT.app ((G.mapHomotopyCategory (.up ℤ)).obj P) ≫
          DerivedCategory.Qh.map ((Functor.mapHomotopyCategoryCompIso
            (Iso.refl (G ⋙ T)) (.up ℤ)).hom.app P) =
        hd.map (εS.app P) ≫ εH.app ((S.mapHomotopyCategory (.up ℤ)).obj P) ≫
          DerivedCategory.Qh.map
            ((Functor.mapHomotopyCategoryCompIso bC (.up ℤ)).hom.app P))
    (P : CochainComplex A ℤ) :
    @Eq (hd.obj (sd.obj (DerivedCategory.Q.obj P)) ⟶
      DerivedCategory.Q.obj ((T.mapHomologicalComplex (.up ℤ)).obj
        ((G.mapHomologicalComplex (.up ℤ)).obj P)))
      (b.hom.app (DerivedCategory.Q.obj P) ≫
        td.map (εG.app ((HomotopyCategory.quotient _ _).obj P)) ≫
        εT.app ((HomotopyCategory.quotient _ _).obj
          ((G.mapHomologicalComplex (.up ℤ)).obj P)))
      (hd.map (εS.app ((HomotopyCategory.quotient _ _).obj P)) ≫
        εH.app ((HomotopyCategory.quotient _ _).obj
          ((S.mapHomologicalComplex (.up ℤ)).obj P)) ≫
        DerivedCategory.Q.map ((complex_comp_iso bC).hom.app P)) := by
  have hh := hn ((HomotopyCategory.quotient _ _).obj P)
  rw [Functor.mapHomotopyCategoryCompIso_refl_hom_app] at hh
  erw [CategoryTheory.Functor.map_id, Category.comp_id] at hh
  rw [qh_compositor] at hh
  simp only [complex_comp_iso_hom_app]
  exact hh

private theorem paste_computation
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    (T : A ⥤ B) (E : A ⥤ C) (H : B ⥤ D) (T' : C ⥤ D)
    (β : T ⋙ H ⟶ E ⋙ T')
    {x y : A} {z : B} {U V W : C} {Z Z' Z'' : D}
    (e : x ⟶ y) (f : T.obj y ⟶ z)
    (a : E.obj x ⟶ U) (s : U ⟶ V) (p : E.obj y ⟶ W) (o : W ⟶ V)
    (r : H.obj z ⟶ Z) (w : Z ⟶ Z'')
    (t : T'.obj W ⟶ Z'') (v : T'.obj V ⟶ Z') (j : Z'' ⟶ Z')
    (hs : E.map e ≫ p ≫ o = a ≫ s)
    (ht : H.map f ≫ r ≫ w = β.app y ≫ T'.map p ≫ t)
    (hn : T'.map o ≫ v = t ≫ j) :
    β.app x ≫ T'.map a ≫ T'.map s ≫ v =
      H.map (T.map e ≫ f) ≫ r ≫ w ≫ j := by
  rw [← T'.map_comp_assoc, ← hs]
  simp only [Functor.map_comp, Category.assoc]
  rw [hn]
  have hb : H.map (T.map e) ≫ β.app y = β.app x ≫ T'.map (E.map e) :=
    β.naturality e
  rw [← reassoc_of% hb, ← reassoc_of% ht]

-- Pasting is checked over abstract categories before any sheaf functor is inserted.
section
variable {C0 : Type*} [Category* C0]
variable {C1 : Type*} [Category* C1]
variable {C2 : Type*} [Category* C2]
variable {C3 : Type*} [Category* C3]
variable {S0 : Type*} [Category* S0]
variable {S1 : Type*} [Category* S1]
variable {S2 : Type*} [Category* S2]
variable {S3 : Type*} [Category* S3]
variable {D0 : Type*} [Category* D0]
variable {D1 : Type*} [Category* D1]
variable {D2 : Type*} [Category* D2]
variable {D3 : Type*} [Category* D3]
variable {E0 : Type*} [Category* E0]
variable {E1 : Type*} [Category* E1]
variable {E2 : Type*} [Category* E2]
variable {E3 : Type*} [Category* E3]

private theorem paste_diagram_reverse
    (G : C0 ⥤ C1)
    (H : C2 ⥤ C3)
    (S : C0 ⥤ C2)
    (T : C1 ⥤ C3)
    (g : S0 ⥤ S1)
    (h : S2 ⥤ S3)
    (s : S0 ⥤ S2)
    (t : S1 ⥤ S3)
    (e0 : C0 ⥤ S0)
    (e1 : C1 ⥤ S1)
    (e2 : C2 ⥤ S2)
    (e3 : C3 ⥤ S3)
    (Q0 : C0 ⥤ D0)
    (Q1 : C1 ⥤ D1)
    (Q2 : C2 ⥤ D2)
    (Q3 : C3 ⥤ D3)
    (q0 : S0 ⥤ E0)
    (q1 : S1 ⥤ E1)
    (q2 : S2 ⥤ E2)
    (q3 : S3 ⥤ E3)
    (A : D0 ⥤ D2)
    (B : D1 ⥤ D3)
    (F : D0 ⥤ D1)
    (J : D2 ⥤ D3)
    (a : E0 ⥤ E2)
    (b : E1 ⥤ E3)
    (f : E0 ⥤ E1)
    (j : E2 ⥤ E3)
    (k0 : D0 ⥤ E0)
    (k1 : D1 ⥤ E1)
    (k2 : D2 ⥤ E2)
    (k3 : D3 ⥤ E3)
    (α : S ⋙ e2 ≅ e0 ⋙ s)
    (β : T ⋙ e3 ≅ e1 ⋙ t)
    (γ : G ⋙ e1 ≅ e0 ⋙ g)
    (δ : H ⋙ e3 ≅ e2 ⋙ h)
    (bC : S ⋙ H ≅ G ⋙ T)
    (cC : s ⋙ h ≅ g ⋙ t)
    (σ0 : A ⋙ k2 ≅ k0 ⋙ a)
    (σ1 : B ⋙ k3 ≅ k1 ⋙ b)
    (π0 : F ⋙ k1 ≅ k0 ⋙ f)
    (π1 : J ⋙ k3 ≅ k2 ⋙ j)
    (bD : A ⋙ J ≅ F ⋙ B)
    (dD : a ⋙ j ≅ f ⋙ b)
    (κ0 : Q0 ⋙ k0 ≅ e0 ⋙ q0)
    (κ1 : Q1 ⋙ k1 ≅ e1 ⋙ q1)
    (κ2 : Q2 ⋙ k2 ≅ e2 ⋙ q2)
    (κ3 : Q3 ⋙ k3 ≅ e3 ⋙ q3)
    (εS : ∀ P, A.obj (Q0.obj P) ⟶ Q2.obj (S.obj P))
    (εT : ∀ P, B.obj (Q1.obj P) ⟶ Q3.obj (T.obj P))
    (εG : ∀ P, F.obj (Q0.obj P) ⟶ Q1.obj (G.obj P))
    (εH : ∀ P, J.obj (Q2.obj P) ⟶ Q3.obj (H.obj P))
    (εs : q0 ⋙ a ⟶ s ⋙ q2)
    (εt : q1 ⋙ b ⟶ t ⋙ q3)
    (εg : q0 ⋙ f ⟶ g ⋙ q1)
    (εh : q2 ⋙ j ⟶ h ⋙ q3)
    (hS : ∀ P, k2.map (εS P) ≫ κ2.hom.app (S.obj P) ≫ q2.map (α.hom.app P) =
      σ0.hom.app (Q0.obj P) ≫ a.map (κ0.hom.app P) ≫ εs.app (e0.obj P))
    (hT : ∀ P, k3.map (εT P) ≫ κ3.hom.app (T.obj P) ≫ q3.map (β.hom.app P) =
      σ1.hom.app (Q1.obj P) ≫ b.map (κ1.hom.app P) ≫ εt.app (e1.obj P))
    (hG : ∀ P, k1.map (εG P) ≫ κ1.hom.app (G.obj P) ≫ q1.map (γ.hom.app P) =
      π0.hom.app (Q0.obj P) ≫ f.map (κ0.hom.app P) ≫ εg.app (e0.obj P))
    (hH : ∀ P, k3.map (εH P) ≫ κ3.hom.app (H.obj P) ≫ q3.map (δ.hom.app P) =
      π1.hom.app (Q2.obj P) ≫ j.map (κ2.hom.app P) ≫ εh.app (e2.obj P))
    (hOrd : ∀ P, e3.map (bC.hom.app P) ≫ β.hom.app (G.obj P) ≫ t.map (γ.hom.app P) =
      δ.hom.app (S.obj P) ≫ h.map (α.hom.app P) ≫ cC.hom.app (e0.obj P))
    (hInt : ∀ P, bD.hom.app (Q0.obj P) ≫ B.map (εG P) ≫ εT (G.obj P) =
      J.map (εS P) ≫ εH (S.obj P) ≫ Q3.map (bC.hom.app P))
    (hSect : ∀ P, dD.hom.app (q0.obj P) ≫ b.map (εg.app P) ≫ εt.app (g.obj P) =
      j.map (εs.app P) ≫ εh.app (s.obj P) ≫ q3.map (cC.hom.app P))
    (P : C0) [IsIso (εS P)] [IsIso (εh.app (s.obj (e0.obj P)))] :
    k3.map (bD.hom.app (Q0.obj P)) ≫ σ1.hom.app (F.obj (Q0.obj P)) ≫
        b.map (π0.hom.app (Q0.obj P)) =
      π1.hom.app (A.obj (Q0.obj P)) ≫ j.map (σ0.hom.app (Q0.obj P)) ≫
        dD.hom.app (k0.obj (Q0.obj P)) := by
  have hSiso : IsIso (σ0.hom.app (Q0.obj P) ≫ a.map (κ0.hom.app P) ≫
      εs.app (e0.obj P)) := by
    rw [← hS]
    infer_instance
  have : IsIso (a.map (κ0.hom.app P) ≫ εs.app (e0.obj P)) :=
    IsIso.of_isIso_comp_left (σ0.hom.app (Q0.obj P)) _
  have : IsIso (εs.app (e0.obj P)) :=
    IsIso.of_isIso_comp_left (a.map (κ0.hom.app P)) _
  let tail := b.map (εg.app (e0.obj P)) ≫ εt.app (g.obj (e0.obj P))
  have ht : IsIso (dD.hom.app (q0.obj (e0.obj P)) ≫ tail) := by
    dsimp only [tail]
    rw [hSect]
    infer_instance
  have : IsIso tail :=
    IsIso.of_isIso_comp_left (dD.hom.app (q0.obj (e0.obj P))) tail
  apply (cancel_mono (b.map (f.map (κ0.hom.app P)) ≫ tail)).mp
  have hl := paste_computation B k1 k3 b σ1.hom (εG P) (εT (G.obj P))
    (π0.hom.app (Q0.obj P)) (f.map (κ0.hom.app P) ≫ εg.app (e0.obj P))
    (κ1.hom.app (G.obj P)) (q1.map (γ.hom.app P))
    (κ3.hom.app (T.obj (G.obj P))) (q3.map (β.hom.app (G.obj P)))
    (εt.app (e1.obj (G.obj P))) (εt.app (g.obj (e0.obj P)))
    (q3.map (t.map (γ.hom.app P))) (hG P) (hT (G.obj P)) (εt.naturality (γ.hom.app P))
  have hr := paste_computation J k2 k3 j π1.hom (εS P) (εH (S.obj P))
    (σ0.hom.app (Q0.obj P)) (a.map (κ0.hom.app P) ≫ εs.app (e0.obj P))
    (κ2.hom.app (S.obj P)) (q2.map (α.hom.app P))
    (κ3.hom.app (H.obj (S.obj P))) (q3.map (δ.hom.app (S.obj P)))
    (εh.app (e2.obj (S.obj P))) (εh.app (s.obj (e0.obj P)))
    (q3.map (h.map (α.hom.app P))) (hS P) (hH (S.obj P)) (εh.naturality (α.hom.app P))
  simp only [Functor.map_comp, Category.assoc] at hl hr
  have hn : j.map (a.map (κ0.hom.app P)) ≫ dD.hom.app (q0.obj (e0.obj P)) =
      dD.hom.app (k0.obj (Q0.obj P)) ≫ b.map (f.map (κ0.hom.app P)) :=
    dD.hom.naturality (κ0.hom.app P)
  have hi := congrArg k3.map (hInt P)
  simp only [Functor.map_comp] at hi
  have hk : k3.map (Q3.map (bC.hom.app P)) ≫ κ3.hom.app (T.obj (G.obj P)) =
      κ3.hom.app (H.obj (S.obj P)) ≫ q3.map (e3.map (bC.hom.app P)) :=
    κ3.hom.naturality (bC.hom.app P)
  have ho := congrArg q3.map (hOrd P)
  simp only [Functor.map_comp] at ho
  dsimp only [tail]
  simp only [Category.assoc]
  rw [hl, reassoc_of% hi, reassoc_of% hk, ho, ← reassoc_of% hr,
    ← hSect, reassoc_of% hn]

end

-- Share the specified abelian and localization structures without changing category types.
universe ua va wa ub vb wb
private structure DerivedStructures (A : Type ua) [Category.{va} A] where
  abelian : Abelian A
  derived : letI := abelian; HasDerivedCategory.{wa} A

@[reducible] private def structure_pair
    {A : Type ua} {B : Type ub} [Category.{va} A] [Category.{vb} B]
    [abA : Abelian A] [abB : Abelian B]
    [derA : HasDerivedCategory.{wa} A] [derB : HasDerivedCategory.{wb} B]
    (_F : DerivedCategory A ⥤ DerivedCategory B) :
    DerivedStructures.{ua, va, wa} A × DerivedStructures.{ub, vb, wb} B :=
  ⟨⟨abA, derA⟩, ⟨abB, derB⟩⟩

-- Lift ordinary comparisons inside the generic cochain diagram constructor.
section
variable {A0 : Type*} [Category* A0] [abA0 : Abelian A0]
  [derA0 : HasDerivedCategory A0]
variable {A1 : Type*} [Category* A1] [abA1 : Abelian A1]
  [derA1 : HasDerivedCategory A1]
variable {A2 : Type*} [Category* A2] [abA2 : Abelian A2]
  [derA2 : HasDerivedCategory A2]
variable {A3 : Type*} [Category* A3] [abA3 : Abelian A3]
  [derA3 : HasDerivedCategory A3]
variable {B0 : Type*} [Category* B0] [abB0 : Abelian B0]
  [derB0 : HasDerivedCategory B0]
variable {B1 : Type*} [Category* B1] [abB1 : Abelian B1]
  [derB1 : HasDerivedCategory B1]
variable {B2 : Type*} [Category* B2] [abB2 : Abelian B2]
  [derB2 : HasDerivedCategory B2]
variable {B3 : Type*} [Category* B3] [abB3 : Abelian B3]
  [derB3 : HasDerivedCategory B3]
variable (G₀ : A0 ⥤ A1) [G₀.Additive]
variable (H₀ : A2 ⥤ A3) [H₀.Additive]
variable (S₀ : A0 ⥤ A2) [S₀.Additive]
variable (T₀ : A1 ⥤ A3) [T₀.Additive]
variable (g₀ : B0 ⥤ B1) [g₀.Additive]
variable (h₀ : B2 ⥤ B3) [h₀.Additive]
variable (s₀ : B0 ⥤ B2) [s₀.Additive]
variable (t₀ : B1 ⥤ B3) [t₀.Additive]
variable (e₀ : A0 ⥤ B0) [e₀.Additive]
variable (e₁ : A1 ⥤ B1) [e₁.Additive]
variable (e₂ : A2 ⥤ B2) [e₂.Additive]
variable (e₃ : A3 ⥤ B3) [e₃.Additive]

private theorem cochain_computation_reverse
    (A : (DerivedCategory A0) ⥤ (DerivedCategory A2))
    (B : (DerivedCategory A1) ⥤ (DerivedCategory A3))
    (F : (DerivedCategory A0) ⥤ (DerivedCategory A1))
    (J : (DerivedCategory A2) ⥤ (DerivedCategory A3))
    (a : (DerivedCategory B0) ⥤ (DerivedCategory B2))
    (b : (DerivedCategory B1) ⥤ (DerivedCategory B3))
    (f : (DerivedCategory B0) ⥤ (DerivedCategory B1))
    (j : (DerivedCategory B2) ⥤ (DerivedCategory B3))
    (k0 : (DerivedCategory A0) ⥤ (DerivedCategory B0))
    (k1 : (DerivedCategory A1) ⥤ (DerivedCategory B1))
    (k2 : (DerivedCategory A2) ⥤ (DerivedCategory B2))
    (k3 : (DerivedCategory A3) ⥤ (DerivedCategory B3))
    (α : S₀ ⋙ e₂ ≅ e₀ ⋙ s₀)
    (β : T₀ ⋙ e₃ ≅ e₁ ⋙ t₀)
    (γ : G₀ ⋙ e₁ ≅ e₀ ⋙ g₀)
    (δ : H₀ ⋙ e₃ ≅ e₂ ⋙ h₀)
    (bC : S₀ ⋙ H₀ ≅ G₀ ⋙ T₀)
    (cC : s₀ ⋙ h₀ ≅ g₀ ⋙ t₀)
    (σ0 : A ⋙ k2 ≅ k0 ⋙ a)
    (σ1 : B ⋙ k3 ≅ k1 ⋙ b)
    (π0 : F ⋙ k1 ≅ k0 ⋙ f)
    (π1 : J ⋙ k3 ≅ k2 ⋙ j)
    (bD : A ⋙ J ≅ F ⋙ B)
    (dD : a ⋙ j ≅ f ⋙ b)
    (κ0 : (DerivedCategory.Q : CochainComplex A0 ℤ ⥤ DerivedCategory A0) ⋙ k0 ≅
      (e₀.mapHomologicalComplex (.up ℤ)) ⋙ (DerivedCategory.Q : CochainComplex B0 ℤ ⥤
      DerivedCategory B0))
    (κ1 : (DerivedCategory.Q : CochainComplex A1 ℤ ⥤ DerivedCategory A1) ⋙ k1 ≅
      (e₁.mapHomologicalComplex (.up ℤ)) ⋙ (DerivedCategory.Q : CochainComplex B1 ℤ ⥤
      DerivedCategory B1))
    (κ2 : (DerivedCategory.Q : CochainComplex A2 ℤ ⥤ DerivedCategory A2) ⋙ k2 ≅
      (e₂.mapHomologicalComplex (.up ℤ)) ⋙ (DerivedCategory.Q : CochainComplex B2 ℤ ⥤
      DerivedCategory B2))
    (κ3 : (DerivedCategory.Q : CochainComplex A3 ℤ ⥤ DerivedCategory A3) ⋙ k3 ≅
      (e₃.mapHomologicalComplex (.up ℤ)) ⋙ (DerivedCategory.Q : CochainComplex B3 ℤ ⥤
      DerivedCategory B3))
    (εS : ∀ P, A.obj ((DerivedCategory.Q : CochainComplex A0 ℤ ⥤ DerivedCategory A0).obj P) ⟶
      (DerivedCategory.Q : CochainComplex A2 ℤ ⥤ DerivedCategory A2).obj
      ((S₀.mapHomologicalComplex (.up ℤ)).obj P))
    (εT : ∀ P, B.obj ((DerivedCategory.Q : CochainComplex A1 ℤ ⥤ DerivedCategory A1).obj P) ⟶
      (DerivedCategory.Q : CochainComplex A3 ℤ ⥤ DerivedCategory A3).obj
      ((T₀.mapHomologicalComplex (.up ℤ)).obj P))
    (εG : ∀ P, F.obj ((DerivedCategory.Q : CochainComplex A0 ℤ ⥤ DerivedCategory A0).obj P) ⟶
      (DerivedCategory.Q : CochainComplex A1 ℤ ⥤ DerivedCategory A1).obj
      ((G₀.mapHomologicalComplex (.up ℤ)).obj P))
    (εH : ∀ P, J.obj ((DerivedCategory.Q : CochainComplex A2 ℤ ⥤ DerivedCategory A2).obj P) ⟶
      (DerivedCategory.Q : CochainComplex A3 ℤ ⥤ DerivedCategory A3).obj
      ((H₀.mapHomologicalComplex (.up ℤ)).obj P))
    (εs : (DerivedCategory.Q : CochainComplex B0 ℤ ⥤ DerivedCategory B0) ⋙ a ⟶
      (s₀.mapHomologicalComplex (.up ℤ)) ⋙ (DerivedCategory.Q : CochainComplex B2 ℤ ⥤
      DerivedCategory B2))
    (εt : (DerivedCategory.Q : CochainComplex B1 ℤ ⥤ DerivedCategory B1) ⋙ b ⟶
      (t₀.mapHomologicalComplex (.up ℤ)) ⋙ (DerivedCategory.Q : CochainComplex B3 ℤ ⥤
      DerivedCategory B3))
    (εg : (DerivedCategory.Q : CochainComplex B0 ℤ ⥤ DerivedCategory B0) ⋙ f ⟶
      (g₀.mapHomologicalComplex (.up ℤ)) ⋙ (DerivedCategory.Q : CochainComplex B1 ℤ ⥤
      DerivedCategory B1))
    (εh : (DerivedCategory.Q : CochainComplex B2 ℤ ⥤ DerivedCategory B2) ⋙ j ⟶
      (h₀.mapHomologicalComplex (.up ℤ)) ⋙ (DerivedCategory.Q : CochainComplex B3 ℤ ⥤
      DerivedCategory B3))
    (hS : ∀ P, k2.map (εS P) ≫ κ2.hom.app ((S₀.mapHomologicalComplex (.up ℤ)).obj P) ≫
      (DerivedCategory.Q : CochainComplex B2 ℤ ⥤ DerivedCategory B2).map ((complex_iso α).hom.app
      P) = σ0.hom.app ((DerivedCategory.Q : CochainComplex A0 ℤ ⥤ DerivedCategory A0).obj P) ≫
      a.map (κ0.hom.app P) ≫ εs.app ((e₀.mapHomologicalComplex (.up ℤ)).obj P))
    (hT : ∀ P, k3.map (εT P) ≫ κ3.hom.app ((T₀.mapHomologicalComplex (.up ℤ)).obj P) ≫
      (DerivedCategory.Q : CochainComplex B3 ℤ ⥤ DerivedCategory B3).map ((complex_iso β).hom.app
      P) = σ1.hom.app ((DerivedCategory.Q : CochainComplex A1 ℤ ⥤ DerivedCategory A1).obj P) ≫
      b.map (κ1.hom.app P) ≫ εt.app ((e₁.mapHomologicalComplex (.up ℤ)).obj P))
    (hG : ∀ P, k1.map (εG P) ≫ κ1.hom.app ((G₀.mapHomologicalComplex (.up ℤ)).obj P) ≫
      (DerivedCategory.Q : CochainComplex B1 ℤ ⥤ DerivedCategory B1).map ((complex_iso γ).hom.app
      P) = π0.hom.app ((DerivedCategory.Q : CochainComplex A0 ℤ ⥤ DerivedCategory A0).obj P) ≫
      f.map (κ0.hom.app P) ≫ εg.app ((e₀.mapHomologicalComplex (.up ℤ)).obj P))
    (hH : ∀ P, k3.map (εH P) ≫ κ3.hom.app ((H₀.mapHomologicalComplex (.up ℤ)).obj P) ≫
      (DerivedCategory.Q : CochainComplex B3 ℤ ⥤ DerivedCategory B3).map ((complex_iso δ).hom.app
      P) = π1.hom.app ((DerivedCategory.Q : CochainComplex A2 ℤ ⥤ DerivedCategory A2).obj P) ≫
      j.map (κ2.hom.app P) ≫ εh.app ((e₂.mapHomologicalComplex (.up ℤ)).obj P))
    (hOrd : ∀ M, e₃.map (bC.hom.app M) ≫ β.hom.app (G₀.obj M) ≫ t₀.map (γ.hom.app M) =
      δ.hom.app (S₀.obj M) ≫ h₀.map (α.hom.app M) ≫ cC.hom.app (e₀.obj M))
    (hInt : ∀ P, bD.hom.app ((DerivedCategory.Q : CochainComplex A0 ℤ ⥤ DerivedCategory A0).obj P)
      ≫ B.map (εG P) ≫ εT ((G₀.mapHomologicalComplex (.up ℤ)).obj P) = J.map (εS P) ≫ εH
      ((S₀.mapHomologicalComplex (.up ℤ)).obj P) ≫ (DerivedCategory.Q : CochainComplex A3 ℤ ⥤
      DerivedCategory A3).map ((complex_comp_iso bC).hom.app P))
    (hSect : ∀ P, dD.hom.app ((DerivedCategory.Q :
        CochainComplex B0 ℤ ⥤ DerivedCategory B0).obj P) ≫
      b.map (εg.app P) ≫ εt.app ((g₀.mapHomologicalComplex (.up ℤ)).obj P) =
      j.map (εs.app P) ≫ εh.app ((s₀.mapHomologicalComplex (.up ℤ)).obj P) ≫
      DerivedCategory.Q.map
        ((Functor.mapHomologicalComplexCompIso cC (.up ℤ)).hom.app P))
    (P : CochainComplex A0 ℤ) [hεS : IsIso (εS P)]
    [IsIso (εh.app ((s₀.mapHomologicalComplex (.up ℤ)).obj
      ((e₀.mapHomologicalComplex (.up ℤ)).obj P)))] :
    k3.map (bD.hom.app (DerivedCategory.Q.obj P)) ≫
        σ1.hom.app (F.obj (DerivedCategory.Q.obj P)) ≫
        b.map (π0.hom.app (DerivedCategory.Q.obj P)) =
      π1.hom.app (A.obj (DerivedCategory.Q.obj P)) ≫
        j.map (σ0.hom.app (DerivedCategory.Q.obj P)) ≫
        dD.hom.app (k0.obj (DerivedCategory.Q.obj P)) := by
  exact paste_diagram_reverse
    (G₀.mapHomologicalComplex (.up ℤ)) (H₀.mapHomologicalComplex (.up ℤ))
    (S₀.mapHomologicalComplex (.up ℤ)) (T₀.mapHomologicalComplex (.up ℤ))
    (g₀.mapHomologicalComplex (.up ℤ)) (h₀.mapHomologicalComplex (.up ℤ))
    (s₀.mapHomologicalComplex (.up ℤ)) (t₀.mapHomologicalComplex (.up ℤ))
    (e₀.mapHomologicalComplex (.up ℤ)) (e₁.mapHomologicalComplex (.up ℤ))
    (e₂.mapHomologicalComplex (.up ℤ)) (e₃.mapHomologicalComplex (.up ℤ)) DerivedCategory.Q
    DerivedCategory.Q DerivedCategory.Q DerivedCategory.Q DerivedCategory.Q DerivedCategory.Q
    DerivedCategory.Q DerivedCategory.Q A B F J a b f j k0 k1 k2 k3 (complex_iso α)
    (complex_iso β) (complex_iso γ) (complex_iso δ) (complex_comp_iso bC)
    (complex_comp_iso cC) σ0 σ1 π0 π1 bD dD κ0 κ1 κ2 κ3 εS εT εG εH εs εt εg εh
    hS hT hG hH
    (complex_square G₀ H₀ S₀ T₀ g₀ h₀ s₀ t₀ e₀ e₁ e₂ e₃ α β γ δ bC cC hOrd)
    hInt (fun P ↦ by
      rw [complex_comp_iso_hom_app]
      exact hSect P) P

end

variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']

variable
  [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (ModuleRingedComparison.modules Λ T)]
  [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (ModuleRingedComparison.modules Λ' T)]

-- Use the fixed derived-equivalence functor in the localization interface itself.
private def section_localization_iso (T : Scheme.{u}) :
    DerivedCategory.Q ⋙ (ModuleRingedComparison.derivedEquivalence Λ T).functor ≅
      (ModuleRingedComparison.equivalence Λ T).functor.mapHomologicalComplex (.up ℤ) ⋙
        DerivedCategory.Q :=
  (ModuleRingedComparison.equivalence Λ T).functor.mapDerivedCategoryFactors

private theorem scalar_computation (a : Λ ⟶ Λ') [IsMonHom a] (T : Scheme.{u})
    (c : ScalarSectionData a T) (h : ScalarSectionNormalized a T c)
    (P : CochainComplex (Modules Λ T) ℤ) :
    @Eq ((ModuleRingedComparison.derivedEquivalence Λ' T).functor.obj
      ((D a T).obj (DerivedCategory.Q.obj P)) ⟶
      DerivedCategory.Q.obj ((c.model.E.mapHomologicalComplex (.up ℤ)).obj
        (((ModuleRingedComparison.equivalence Λ T).functor.mapHomologicalComplex (.up ℤ)).obj
          P)))
      ((ModuleRingedComparison.derivedEquivalence Λ' T).functor.map
        ((scalarCounit a T).app ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) ≫
        (section_localization_iso (Λ := Λ') T).hom.app
          (((extension a T).mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map ((complex_iso c.ordinary).hom.app P))
      (c.derived.hom.app (DerivedCategory.Q.obj P) ≫
        c.model.T.map ((section_localization_iso (Λ := Λ) T).hom.app P) ≫
        c.model.ε.app
          (((ModuleRingedComparison.equivalence Λ T).functor.mapHomologicalComplex
            (.up ℤ)).obj P)) := by
  unfold complex_iso section_localization_iso
  have hh := section_pull_transport_scalar_computation a T c h P
  simp only [compute_eq] at hh
  exact hh

private def section_pull_compute_nat {X Y : Scheme.{u}} (f : X ⟶ Y) :
    DerivedCategory.Q ⋙ ModuleRingedComparison.derivedPullback Λ f ⟶
      (ModuleRingedComparison.pullback Λ f).mapHomologicalComplex (.up ℤ) ⋙
        DerivedCategory.Q :=
  (ModuleRingedComparison.pullback Λ f).mapDerivedCategoryFactors.hom

-- Unfold the two named interfaces once, preserving the fixed derived-functor instances.
private theorem geometric_computation {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P : CochainComplex (Modules Λ Y) ℤ) :
    @Eq ((ModuleRingedComparison.derivedEquivalence Λ X).functor.obj
      ((L Λ f).obj (DerivedCategory.Q.obj P)) ⟶
      DerivedCategory.Q.obj
        (((ModuleRingedComparison.pullback Λ f).mapHomologicalComplex (.up ℤ)).obj
          (((ModuleRingedComparison.equivalence Λ Y).functor.mapHomologicalComplex (.up ℤ)).obj
            P)))
      ((ModuleRingedComparison.derivedEquivalence Λ X).functor.map
        ((pullCounit (Λ := Λ) f).app ((HomotopyCategory.quotient _ _).obj P)) ≫
      (section_localization_iso (Λ := Λ) X).hom.app
        (((CondensedRing.upperStar Λ f).mapHomologicalComplex (.up ℤ)).obj P) ≫
      DerivedCategory.Q.map
        ((complex_iso (ModuleRingedComparison.pullComparison Λ f)).hom.app P))
      ((ModuleRingedComparison.derivedPullComparison Λ f).hom.app (DerivedCategory.Q.obj P) ≫
      (ModuleRingedComparison.derivedPullback Λ f).map
        ((section_localization_iso (Λ := Λ) Y).hom.app P) ≫
      (section_pull_compute_nat (Λ := Λ) f).app
        (((ModuleRingedComparison.equivalence Λ Y).functor.mapHomologicalComplex (.up ℤ)).obj P))
    := by
  rw [complex_iso_hom_app]
  unfold section_localization_iso section_pull_compute_nat
  have hh := section_pull_transport_geometric_computation f P
  simp only [_root_.counit_quotient_transport] at hh
  exact hh

attribute [local irreducible] complex_iso complex_comp_iso section_localization_iso

-- Infer the fixed cochain instances for all eight coefficient categories together.
/-- The normalized scalar and geometric squares commute at a cochain representative
where the internal scalar computation counit is invertible. -/
theorem section_pull_transport_condition_on_computed (a : Λ ⟶ Λ') [IsMonHom a]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (cX : ScalarSectionData a X) (cY : ScalarSectionData a Y)
    (hcX : ScalarSectionNormalized a X cX) (hcY : ScalarSectionNormalized a Y cY)
    (lam : D a Y ⋙ L Λ' f ≅ L Λ f ⋙ D a X) (normalized : PullNormalized a f lam)
    (barLam : cY.model.T ⋙ ModuleRingedComparison.derivedPullback Λ' f ≅
      ModuleRingedComparison.derivedPullback Λ f ⋙ cX.model.T)
    (hnorm : SectionPullNormalized a f cX cY barLam)
    (P : CochainComplex (Modules Λ Y) ℤ)
    [IsIso ((scalarCounit a Y).app ((HomotopyCategory.quotient _ (.up ℤ)).obj P))] :
    (ModuleRingedComparison.derivedFunctor Λ' X).map
        (lam.hom.app (DerivedCategory.Q.obj P)) ≫
        cX.derived.hom.app ((L Λ f).obj (DerivedCategory.Q.obj P)) ≫
        cX.model.T.map ((ModuleRingedComparison.derivedPullComparison Λ f).hom.app
          (DerivedCategory.Q.obj P)) =
      (ModuleRingedComparison.derivedPullComparison Λ' f).hom.app
          ((D a Y).obj (DerivedCategory.Q.obj P)) ≫
        (ModuleRingedComparison.derivedPullback Λ' f).map
          (cY.derived.hom.app (DerivedCategory.Q.obj P)) ≫
        barLam.hom.app ((ModuleRingedComparison.derivedFunctor Λ Y).obj
          (DerivedCategory.Q.obj P)) := by
  obtain ⟨e, he, hd⟩ := hnorm
  let AD := D a Y
  let BD := D a X
  let FD := L Λ f
  let JD := L Λ' f
  let fD := ModuleRingedComparison.derivedPullback Λ f
  let jD := ModuleRingedComparison.derivedPullback Λ' f
  let kD0 := (ModuleRingedComparison.derivedEquivalence Λ Y).functor
  let kD1 := (ModuleRingedComparison.derivedEquivalence Λ X).functor
  let kD2 := (ModuleRingedComparison.derivedEquivalence Λ' Y).functor
  let kD3 := (ModuleRingedComparison.derivedEquivalence Λ' X).functor
  let internalY := structure_pair AD
  let internalX := structure_pair BD
  let sectionY := structure_pair cY.model.T
  let sectionX := structure_pair cX.model.T
  have hInt := cochain_normalization
    (A := Modules Λ Y) (B := Modules Λ X)
    (C := Modules Λ' Y) (D := Modules Λ' X)
    (extension a Y) (extension a X)
    (CondensedRing.upperStar Λ f) (CondensedRing.upperStar Λ' f)
    AD BD FD JD
    (scalarCounit a Y) (scalarCounit a X)
    (pullCounit (Λ := Λ) f) (pullCounit (Λ := Λ') f)
    lam (CondensedRing.pullIso a f).symm normalized
  have : IsIso (section_pull_compute_nat (Λ := Λ') f) := by
    unfold section_pull_compute_nat
    infer_instance
  exact cochain_computation_reverse
    (hεS := by
      exact ‹IsIso ((scalarCounit a Y).app ((HomotopyCategory.quotient _ (.up ℤ)).obj P))›)
    (abA0 := internalY.1.abelian) (derA0 := internalY.1.derived)
    (abA1 := internalX.1.abelian) (derA1 := internalX.1.derived)
    (abA2 := internalY.2.abelian) (derA2 := internalY.2.derived)
    (abA3 := internalX.2.abelian) (derA3 := internalX.2.derived)
    (abB0 := sectionY.1.abelian) (derB0 := sectionY.1.derived)
    (abB1 := sectionX.1.abelian) (derB1 := sectionX.1.derived)
    (abB2 := sectionY.2.abelian) (derB2 := sectionY.2.derived)
    (abB3 := sectionX.2.abelian) (derB3 := sectionX.2.derived)
    (A0 := Modules Λ Y) (A1 := Modules Λ X)
    (A2 := Modules Λ' Y) (A3 := Modules Λ' X)
    (B0 := ModuleRingedComparison.modules Λ Y)
    (B1 := ModuleRingedComparison.modules Λ X)
    (B2 := ModuleRingedComparison.modules Λ' Y)
    (B3 := ModuleRingedComparison.modules Λ' X)
    (G₀ := CondensedRing.upperStar Λ f) (H₀ := CondensedRing.upperStar Λ' f)
    (S₀ := extension a Y) (T₀ := extension a X)
    (g₀ := ModuleRingedComparison.pullback Λ f)
    (h₀ := ModuleRingedComparison.pullback Λ' f)
    (s₀ := cY.model.E) (t₀ := cX.model.E)
    (e₀ := (ModuleRingedComparison.equivalence Λ Y).functor)
    (e₁ := (ModuleRingedComparison.equivalence Λ X).functor)
    (e₂ := (ModuleRingedComparison.equivalence Λ' Y).functor)
    (e₃ := (ModuleRingedComparison.equivalence Λ' X).functor)
    AD BD FD JD
    cY.model.T cX.model.T
    fD jD kD0 kD1 kD2 kD3
    cY.ordinary cX.ordinary (ModuleRingedComparison.pullComparison Λ f)
    (ModuleRingedComparison.pullComparison Λ' f) (CondensedRing.pullIso a f).symm e
    cY.derived cX.derived
    (ModuleRingedComparison.derivedPullComparison Λ f)
    (ModuleRingedComparison.derivedPullComparison Λ' f) lam barLam
    (section_localization_iso (Λ := Λ) Y) (section_localization_iso (Λ := Λ) X)
    (section_localization_iso (Λ := Λ') Y) (section_localization_iso (Λ := Λ') X)
    (fun P ↦ (scalarCounit a Y).app ((HomotopyCategory.quotient _ _).obj P))
    (fun P ↦ (scalarCounit a X).app ((HomotopyCategory.quotient _ _).obj P))
    (fun P ↦ (pullCounit (Λ := Λ) f).app ((HomotopyCategory.quotient _ _).obj P))
    (fun P ↦ (pullCounit (Λ := Λ') f).app ((HomotopyCategory.quotient _ _).obj P))
    cY.model.ε cX.model.ε
    (section_pull_compute_nat (Λ := Λ) f)
    (section_pull_compute_nat (Λ := Λ') f)
    (scalar_computation a Y cY hcY) (scalar_computation a X cX hcX)
    (geometric_computation (Λ := Λ) f) (geometric_computation (Λ := Λ') f)
    he hInt (fun R ↦ by
      have hh := hd R
      rw [Functor.mapHomologicalComplexCompIso_refl_hom_app] at hh
      erw [CategoryTheory.Functor.map_id, Category.comp_id] at hh
      exact hh) P

end AlgebraicGeometry.ProEtale.QuotientSectionTensor
