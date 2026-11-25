/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.AlgebraicGeometry.InternalScalarPullbackNormalizationData
import WeilConjectures.AlgebraicGeometry.SectionDerivedPushpullNormalization
import WeilConjectures.AlgebraicGeometry.SectionOrdinaryPullCompatibility
import WeilConjectures.AlgebraicGeometry.SectionScalarComputationAll

/-! # Computation of a realized scalar pullback comparison

Source: Stacks Project, Tags 03EK, 0D6D and 07A6.
(auxiliary; not a blueprint node)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 4096
-- Keep localization functors shared while comparing their universal maps.
attribute [local irreducible] CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Functor.leftDerivedFunctor
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
open CategoryTheory.InternalAbelianSheafModule

namespace AlgebraicGeometry.ProEtale.QuotientChange

private theorem map_id_cleanup
    {A C D : Type*} [Category A] [Category C] [Category D]
    (F : A ⥤ D) (G : C ⥤ D) {x : A} {y : C} (t : F.obj x ⟶ G.obj y) :
    F.map (𝟙 x) ≫ t ≫ G.map (𝟙 y) ≫ 𝟙 _ = t := by
  simp only [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]

-- Extract a normalization field without repeating its large remaining conjunction.
private theorem fifth_conj {a b c d e tail : Prop} (h : a ∧ b ∧ c ∧ d ∧ e ∧ tail) : e :=
  h.2.2.2.2.1

-- Restrict a homotopy counit while the additive categories remain abstract.
private def cochain_counit
    {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B]
    (F : A ⥤ B) [F.Additive] (D : DerivedCategory A ⥤ DerivedCategory B)
    (ε : DerivedCategory.Qh ⋙ D ⟶ F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh) :
    DerivedCategory.Q ⋙ D ⟶ F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q where
  app P := D.map ((DerivedCategory.quotientCompQhIso _).inv.app P) ≫
    ε.app ((HomotopyCategory.quotient _ (.up ℤ)).obj P) ≫
      (DerivedCategory.quotientCompQhIso _).hom.app _
  naturality P Q f := by
    change D.map (DerivedCategory.Q.map f) ≫
        (D.map (𝟙 _) ≫ ε.app ((HomotopyCategory.quotient _ (.up ℤ)).obj Q) ≫ 𝟙 _) =
      (D.map (𝟙 _) ≫ ε.app ((HomotopyCategory.quotient _ (.up ℤ)).obj P) ≫ 𝟙 _) ≫
        DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map f)
    simp only [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
    exact ε.naturality ((HomotopyCategory.quotient _ (.up ℤ)).map f)

-- Build the equivalence instance while its coefficient categories remain abstract.
private theorem complex_equivalence
    {A B : Type*} [Category A] [Category B] [Preadditive A] [Preadditive B]
    (E : A ≌ B) [E.functor.Additive] :
    (E.functor.mapHomologicalComplex (.up ℤ)).IsEquivalence := by
  change (E.mapHomologicalComplex (.up ℤ)).functor.IsEquivalence
  infer_instance

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

private theorem paste_paths
    {𝒞 : Type*} [Category* 𝒞]
    {A B C D E F Z E₀ A₀ B₀ A₁ A₂ A₃ A₄ C₁ Z₀ P₀ P₁ K₀ K₁ : 𝒞}
    (a : A ⟶ B) (b : B ⟶ C) (c : C ⟶ D)
    (d : D ⟶ E) (e : E ⟶ F) (f : F ⟶ Z)
    (d₀ : C ⟶ E₀) (c₀ : E₀ ⟶ E)
    (B' : A ⟶ A₀) (s₀ : A₀ ⟶ B₀) (g₀ : B₀ ⟶ E₀)
    (u₀ : A₀ ⟶ A₁) (v₀ : A₁ ⟶ A₂) (w₀ : A₂ ⟶ A₃)
    (x₀ : A₃ ⟶ A₄) (y₀ : A₄ ⟶ Z)
    (r₀ : D ⟶ C₁) (s₁ : C₁ ⟶ Z₀)
    (p₀ : A ⟶ P₀) (q₀ : P₀ ⟶ P₁) (k₀ : P₁ ⟶ K₀)
    (l₀ : K₀ ⟶ K₁) (m₀ : K₁ ⟶ Z₀) (z₀ : P₁ ⟶ A₂)
    (j₀ : K₀ ⟶ A₃) (n₀ : Z₀ ⟶ Z)
    (hn : c ≫ d = d₀ ≫ c₀)
    (hr : B' ≫ s₀ ≫ g₀ = a ≫ b ≫ d₀)
    (hl : s₀ ≫ g₀ ≫ c₀ ≫ e ≫ f = u₀ ≫ v₀ ≫ w₀ ≫ x₀ ≫ y₀)
    (hh : a ≫ b ≫ c ≫ r₀ ≫ s₁ = p₀ ≫ q₀ ≫ k₀ ≫ l₀ ≫ m₀)
    (hi : B' ≫ u₀ ≫ v₀ = p₀ ≫ q₀ ≫ z₀)
    (hk : z₀ ≫ w₀ = k₀ ≫ j₀)
    (ho : j₀ ≫ x₀ ≫ y₀ = l₀ ≫ m₀ ≫ n₀) :
    a ≫ b ≫ c ≫ d ≫ e ≫ f = a ≫ b ≫ c ≫ r₀ ≫ s₁ ≫ n₀ := by
  rw [reassoc_of% hn, ← reassoc_of% hr, hl, reassoc_of% hh,
    reassoc_of% hi, reassoc_of% hk, ho]

-- Pasting two computation squares uses only one naturality square in the middle.
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

private theorem paste_diagram
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
    (equiv0 : e0.IsEquivalence)
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
    (realization : ∀ M, k3.map (bD.hom.app M) ≫ σ1.hom.app (F.obj M) ≫ b.map (π0.hom.app M) =
      π1.hom.app (A.obj M) ≫ j.map (σ0.hom.app M) ≫ dD.hom.app (k0.obj M))
    : ∀ P, dD.hom.app (q0.obj P) ≫ b.map (εg.app P) ≫ εt.app (g.obj P) =
      j.map (εs.app P) ≫ εh.app (s.obj P) ≫ q3.map (cC.hom.app P) := by
  let := equiv0
  let θ₁ : q0 ⋙ a ⋙ j ⟶ g ⋙ t ⋙ q3 :=
    Functor.whiskerLeft q0 dD.hom ≫
      Functor.whiskerRight εg b ≫ Functor.whiskerLeft g εt
  let θ₂ : q0 ⋙ a ⋙ j ⟶ g ⋙ t ⋙ q3 :=
    Functor.whiskerRight εs j ≫ Functor.whiskerLeft s εh ≫ Functor.whiskerRight cC.hom q3
  have hθ : θ₁ = θ₂ := by
    apply ((Functor.whiskeringLeft _ _ _).obj e0).map_injective
    apply NatTrans.ext
    funext P
    change θ₁.app (e0.obj P) = θ₂.app (e0.obj P)
    apply (cancel_epi (j.map (a.map (κ0.hom.app P)))).mp
    apply (cancel_epi (j.map (σ0.hom.app (Q0.obj P)))).mp
    apply (cancel_epi (π1.hom.app (A.obj (Q0.obj P)))).mp
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
    dsimp only [θ₁, θ₂, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app]
    exact paste_paths (π1.hom.app (A.obj (Q0.obj P))) (j.map (σ0.hom.app (Q0.obj P)))
      (j.map (a.map (κ0.hom.app P))) (dD.hom.app (q0.obj (e0.obj P)))
      (b.map (εg.app (e0.obj P))) (εt.app (g.obj (e0.obj P)))
      (dD.hom.app (k0.obj (Q0.obj P))) (b.map (f.map (κ0.hom.app P)))
      (k3.map (bD.hom.app (Q0.obj P))) (σ1.hom.app (F.obj (Q0.obj P)))
      (b.map (π0.hom.app (Q0.obj P))) (k3.map (B.map (εG P)))
      (k3.map (εT (G.obj P))) (κ3.hom.app (T.obj (G.obj P)))
      (q3.map (β.hom.app (G.obj P))) (q3.map (t.map (γ.hom.app P)))
      (j.map (εs.app (e0.obj P))) (εh.app (s.obj (e0.obj P)))
      (k3.map (J.map (εS P))) (k3.map (εH (S.obj P)))
      (κ3.hom.app (H.obj (S.obj P))) (q3.map (δ.hom.app (S.obj P)))
      (q3.map (h.map (α.hom.app P))) (k3.map (Q3.map (bC.hom.app P)))
      (q3.map (e3.map (bC.hom.app P))) (q3.map (cC.hom.app (e0.obj P)))
      hn (realization (Q0.obj P)) hl hr hi hk ho
  intro P
  exact NatTrans.congr_app hθ P

end

-- Share the specified abelian and localization structures without changing category types.
universe ua va wa ub vb wb
private structure DerivedStructures (A : Type ua) [Category.{va} A] where
  abelian : Abelian A
  derived : letI := abelian; HasDerivedCategory.{wa} A

private def structure_pair
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

private theorem cochain_computation
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
    (equiv0 : (e₀.mapHomologicalComplex (.up ℤ)).IsEquivalence)
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
    (realization : ∀ M, k3.map (bD.hom.app M) ≫ σ1.hom.app (F.obj M) ≫ b.map (π0.hom.app M) =
      π1.hom.app (A.obj M) ≫ j.map (σ0.hom.app M) ≫ dD.hom.app (k0.obj M))
    : ∀ P, dD.hom.app ((DerivedCategory.Q :
        CochainComplex B0 ℤ ⥤ DerivedCategory B0).obj P) ≫
      b.map (εg.app P) ≫ εt.app ((g₀.mapHomologicalComplex (.up ℤ)).obj P) =
      j.map (εs.app P) ≫ εh.app ((s₀.mapHomologicalComplex (.up ℤ)).obj P) ≫
      DerivedCategory.Q.map
        ((Functor.mapHomologicalComplexCompIso cC (.up ℤ)).hom.app P) := by
  simpa only [complex_comp_iso_hom_app] using paste_diagram
    (G₀.mapHomologicalComplex (.up ℤ)) (H₀.mapHomologicalComplex (.up ℤ))
    (S₀.mapHomologicalComplex (.up ℤ)) (T₀.mapHomologicalComplex (.up ℤ))
    (g₀.mapHomologicalComplex (.up ℤ)) (h₀.mapHomologicalComplex (.up ℤ))
    (s₀.mapHomologicalComplex (.up ℤ)) (t₀.mapHomologicalComplex (.up ℤ))
    (e₀.mapHomologicalComplex (.up ℤ)) (e₁.mapHomologicalComplex (.up ℤ))
    (e₂.mapHomologicalComplex (.up ℤ)) (e₃.mapHomologicalComplex (.up ℤ)) DerivedCategory.Q
    DerivedCategory.Q DerivedCategory.Q DerivedCategory.Q DerivedCategory.Q DerivedCategory.Q
    DerivedCategory.Q DerivedCategory.Q A B F J a b f j k0 k1 k2 k3 (complex_iso α)
    (complex_iso β) (complex_iso γ) (complex_iso δ) (complex_comp_iso bC) (complex_comp_iso cC) σ0
    σ1 π0 π1 bD dD κ0 κ1 κ2 κ3 εS εT εG εH εs εt εg εh equiv0 hS hT hG hH
    (complex_square G₀ H₀ S₀ T₀ g₀ h₀ s₀ t₀ e₀ e₁ e₂ e₃ α β γ δ bC cC hOrd) hInt realization

end

variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']

private theorem compute_eq (a : Λ ⟶ Λ') [IsMonHom a] (T : Scheme.{u})
    (P : CochainComplex (Modules Λ T) ℤ) :
    compute a T P = (scalarCounit a T).app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj P) := by
  unfold compute
  change (D a T).map (𝟙 _) ≫ _ ≫ DerivedCategory.Qh.map (𝟙 _) ≫ 𝟙 _ = _
  exact map_id_cleanup (D a T) DerivedCategory.Qh _

variable
  [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (ModuleRingedComparison.modules Λ T)]
  [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (ModuleRingedComparison.modules Λ' T)]

-- Use the fixed derived-equivalence functor in the localization interface itself.
private def section_localization_iso (T : Scheme.{u}) :
    DerivedCategory.Q ⋙ (ModuleRingedComparison.derivedEquivalence Λ T).functor ≅
      (ModuleRingedComparison.equivalence Λ T).functor.mapHomologicalComplex (.up ℤ) ⋙
        DerivedCategory.Q :=
  (ModuleRingedComparison.equivalence Λ T).functor.mapDerivedCategoryFactors

private theorem section_localization_iso_hom_app (T : Scheme.{u})
    (P : CochainComplex (Modules Λ T) ℤ) :
    (section_localization_iso (Λ := Λ) T).hom.app P =
      (ModuleRingedComparison.sectionLocalizationComparison Λ T P).hom := by
  unfold section_localization_iso
  rfl

private def section_compute_nat (a : Λ ⟶ Λ') [IsMonHom a] (T : Scheme.{u})
    (s : SectionScalarComparison a T) :
    DerivedCategory.Q ⋙ s.pair.derived ⟶
      s.pair.extension.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
  cochain_counit s.pair.extension s.pair.derived s.pair.counit

private theorem section_compute_eq (a : Λ ⟶ Λ') [IsMonHom a] (T : Scheme.{u})
    (s : SectionScalarComparison a T)
    (P : CochainComplex (ModuleRingedComparison.modules Λ T) ℤ) :
    SheafOfModules.scalarPairComplexComparison s.pair.extension s.pair.extension_additive
      s.pair.derived s.pair.counit P = (section_compute_nat a T s).app P := by
  unfold section_compute_nat cochain_counit SheafOfModules.scalarPairComplexComparison
  rfl

-- Fix the scalar computation interface once for both endpoints of the square.
private theorem scalar_computation (a : Λ ⟶ Λ') [IsMonHom a] (T : Scheme.{u})
    (s : SectionScalarComparison a T) (h : SectionScalarNormalized a T s)
    (P : CochainComplex (Modules Λ T) ℤ) :
    @Eq ((ModuleRingedComparison.derivedEquivalence Λ' T).functor.obj
      ((D a T).obj (DerivedCategory.Q.obj P)) ⟶
      DerivedCategory.Q.obj ((s.pair.extension.mapHomologicalComplex (.up ℤ)).obj
        (((ModuleRingedComparison.equivalence Λ T).functor.mapHomologicalComplex (.up ℤ)).obj
          P)))
      ((ModuleRingedComparison.derivedEquivalence Λ' T).functor.map ((scalarCounit a T).app
          ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) ≫
        (section_localization_iso (Λ := Λ') T).hom.app
          (((extension a T).mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map ((complex_iso s.ordinary).hom.app P))
      (s.derived.hom.app (DerivedCategory.Q.obj P) ≫
        s.pair.derived.map ((section_localization_iso (Λ := Λ) T).hom.app P) ≫
        (section_compute_nat a T s).app
          (((ModuleRingedComparison.equivalence Λ T).functor.mapHomologicalComplex (.up ℤ)).obj
            P)) := by
  unfold complex_iso
  simpa only [compute_eq, section_localization_iso_hom_app, section_compute_eq] using
    section_scalar_computation_all a T s h P

-- Keep the section pullback's named derived functor in its counit interface.
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
      ((scalarSectionPullComparison Λ f).hom.app (DerivedCategory.Q.obj P) ≫
      (ModuleRingedComparison.derivedPullback Λ f).map
        ((section_localization_iso (Λ := Λ) Y).hom.app P) ≫
      (section_pull_compute_nat (Λ := Λ) f).app
        (((ModuleRingedComparison.equivalence Λ Y).functor.mapHomologicalComplex (.up ℤ)).obj P))
    := by
  have hh :=
    (fifth_conj (ModuleRingedComparison.sectionDerivedPushpullNormalization Λ f) P).symm
  change (ModuleRingedComparison.derivedEquivalence Λ X).functor.map
      ((CondensedRing.upperStar Λ f).leftDerivedFunctor.map (𝟙 _) ≫
        _ ≫ DerivedCategory.Qh.map (𝟙 _) ≫ 𝟙 _) ≫ _ = _ at hh
  simp only [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id] at hh
  unfold L CondensedRing.moduleObjectDerivedPullback pullCounit scalarSectionPullComparison
  dsimp only [_root_.id]
  simpa only [section_localization_iso_hom_app, complex_iso_hom_app,
    section_pull_compute_nat,
    ModuleRingedComparison.internalDerivedPullback, ModuleRingedComparison.comparisonSource,
    ModuleRingedComparison.derivedPullback, Functor.comp_obj] using hh

attribute [local irreducible] complex_iso complex_comp_iso section_localization_iso

set_option cleanup.letToHave false in
-- Track the specified localization and termwise-equivalence instances through the diagram.
/-- The K-flat computation equation for supplied ordinary and derived comparisons.
All isomorphisms are supplied as inputs; this theorem selects no data.
Source: Stacks Project, Cohomology on Sites, Tags 03EK, 0D6D and 07A6;
section pullback normalization transport, representative computation step.
(auxiliary; not a blueprint node)

Proof: conjugate the identity restriction/pushforward square through the two
ordinary scalar adjunctions and the two geometric adjunctions. The restriction
comparisons of the endpoint realizations are identities on sections. Their
ordinary scalar comparisons send the internal balanced generators to the section
balanced generators, and both scalar units insert 1. Thus the resulting ordinary
square is precisely c, by injectivity of conjugateEquiv. Coefficient compatibility
of the geometric ring maps identifies its internal form with the inverse of
CondensedRing.pullIso.

Extend each endpoint scalar computation equation to all internal complexes:
resolve its section image by a flat-term K-flat complex, lift the resolution
through the termwise section equivalence, apply the given normalization there,
and use naturality and invertibility of the localized augmentation to cancel.
Paste these scalar computation equations with the geometric representative
pullback equations. PullNormalized identifies the central internal paths.
The ordinary identification replaces the resulting ordinary square by c.
The specified realization equation substitutes d for the realized internal b.
Naturality of the localization comparisons and cancellation now give the
computation equation after precomposition by the termwise section equivalence.
Precomposition by this equivalence is faithful, so the equation holds on every
section complex, in particular on the supplied flat-term K-flat complexes.
No preservation of K-flatness by geometric pullback is required. Zero rings and
empty schemes satisfy the same adjunction and localization identities. -/
theorem section_pull_computation_of_realization (a : Λ ⟶ Λ') [IsMonHom a]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (sX : SectionScalarComparison a X) (sY : SectionScalarComparison a Y)
    (hX : SectionScalarNormalized a X sX) (hY : SectionScalarNormalized a Y sY)
    (b : D a Y ⋙ L Λ' f ≅ L Λ f ⋙ D a X)
    (normalized : PullNormalized a f b)
    (r : ModuleRingedComparison.pushforward Λ' f ⋙
      SheafOfModules.scalarRestriction.{u + 1, u, u + 1}
      (sectionScalarMap.{u + 1, u + 1, u} (Scheme.ProEt.topology Y) (coefficientMap a Y)) ≅
        SheafOfModules.scalarRestriction.{u + 1, u, u + 1}
          (sectionScalarMap.{u + 1, u + 1, u} (Scheme.ProEt.topology X) (coefficientMap a X)) ⋙
            ModuleRingedComparison.pushforward Λ f)
    (identity_on_sections : (∀ (N : ModuleRingedComparison.modules Λ' X) (U : Y.ProEtᵒᵖ)
      (x : ((ModuleRingedComparison.pushforward Λ' f).obj N).val.obj U),
    (r.hom.app N).val.app U x = x))
    (c : sY.pair.extension ⋙ ModuleRingedComparison.pullback Λ' f ≅
    ModuleRingedComparison.pullback Λ f ⋙ sX.pair.extension)
    (conjugate : conjugateEquiv
      (sY.pair.ordinaryAdjunction.comp (ModuleRingedComparison.adjunction Λ' f))
      ((ModuleRingedComparison.adjunction Λ f).comp sX.pair.ordinaryAdjunction) c.inv = r.hom)
    (d : sY.pair.derived ⋙ ModuleRingedComparison.derivedPullback Λ' f ≅
    ModuleRingedComparison.derivedPullback Λ f ⋙ sX.pair.derived)
    (realization : ∀ M : DerivedCategory (Modules Λ Y),
    (ModuleRingedComparison.derivedEquivalence Λ' X).functor.map (b.hom.app M) ≫
        sX.derived.hom.app ((L Λ f).obj M) ≫
        sX.pair.derived.map ((scalarSectionPullComparison Λ f).hom.app M) =
      (scalarSectionPullComparison Λ' f).hom.app ((D a Y).obj M) ≫
        (ModuleRingedComparison.derivedPullback Λ' f).map (sY.derived.hom.app M) ≫
        d.hom.app ((ModuleRingedComparison.derivedEquivalence Λ Y).functor.obj M)) :
    ∀ (P : CochainComplex (ModuleRingedComparison.modules Λ Y) ℤ),
    CochainComplex.IsKFlatIndependentCoefficients (R := ModuleRingedComparison.ring Λ Y) P →
    (∀ n : ℤ, SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
      (R := ModuleRingedComparison.ring Λ Y) (P.X n)) →
    d.hom.app (DerivedCategory.Q.obj P) ≫
        sX.pair.derived.map
          ((ModuleRingedComparison.pullback Λ f).mapDerivedCategoryFactors.hom.app P) ≫
        SheafOfModules.scalarPairComplexComparison.{u + 1, u, u + 1, u + 1}
          sX.pair.extension sX.pair.extension_additive
          sX.pair.derived sX.pair.counit
          (((ModuleRingedComparison.pullback Λ f).mapHomologicalComplex (.up ℤ)).obj P) =
      (ModuleRingedComparison.derivedPullback Λ' f).map
        (SheafOfModules.scalarPairComplexComparison.{u + 1, u, u + 1, u + 1}
          sY.pair.extension sY.pair.extension_additive
          sY.pair.derived sY.pair.counit P) ≫
        (ModuleRingedComparison.pullback Λ' f).mapDerivedCategoryFactors.hom.app
          ((SheafOfModules.scalarComplex.{u + 1, u, u + 1}
              sY.pair.extension sY.pair.extension_additive).obj P) ≫
        DerivedCategory.Q.map ((Functor.mapHomologicalComplexCompIso c (.up ℤ)).hom.app P) := by
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
  let sectionY := structure_pair sY.pair.derived
  let sectionX := structure_pair sX.pair.derived
  have hInt := cochain_normalization
    (A := Modules Λ Y) (B := Modules Λ X)
    (C := Modules Λ' Y) (D := Modules Λ' X)
    (extension a Y) (extension a X)
    (CondensedRing.upperStar Λ f) (CondensedRing.upperStar Λ' f)
    AD BD FD JD
    (scalarCounit a Y) (scalarCounit a X)
    (pullCounit (Λ := Λ) f) (pullCounit (Λ := Λ') f)
    b (CondensedRing.pullIso a f).symm normalized
  have hall := cochain_computation
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
    (s₀ := sY.pair.extension) (t₀ := sX.pair.extension)
    (e₀ := (ModuleRingedComparison.equivalence Λ Y).functor)
    (e₁ := (ModuleRingedComparison.equivalence Λ X).functor)
    (e₂ := (ModuleRingedComparison.equivalence Λ' Y).functor)
    (e₃ := (ModuleRingedComparison.equivalence Λ' X).functor)
    AD BD FD JD
    sY.pair.derived sX.pair.derived
    fD jD kD0 kD1 kD2 kD3
    sY.ordinary sX.ordinary (ModuleRingedComparison.pullComparison Λ f)
    (ModuleRingedComparison.pullComparison Λ' f) (CondensedRing.pullIso a f).symm c
    sY.derived sX.derived
    (scalarSectionPullComparison Λ f) (scalarSectionPullComparison Λ' f) b d
    (section_localization_iso (Λ := Λ) Y) (section_localization_iso (Λ := Λ) X)
    (section_localization_iso (Λ := Λ') Y) (section_localization_iso (Λ := Λ') X)
    (fun P ↦ (scalarCounit a Y).app ((HomotopyCategory.quotient _ _).obj P))
    (fun P ↦ (scalarCounit a X).app ((HomotopyCategory.quotient _ _).obj P))
    (fun P ↦ (pullCounit (Λ := Λ) f).app ((HomotopyCategory.quotient _ _).obj P))
    (fun P ↦ (pullCounit (Λ := Λ') f).app ((HomotopyCategory.quotient _ _).obj P))
    (section_compute_nat a Y sY) (section_compute_nat a X sX)
    (section_pull_compute_nat (Λ := Λ) f)
    (section_pull_compute_nat (Λ := Λ') f)
    (complex_equivalence (ModuleRingedComparison.equivalence Λ Y))
    (scalar_computation a Y sY hY) (scalar_computation a X sX hX)
    (geometric_computation (Λ := Λ) f) (geometric_computation (Λ := Λ') f)
    (section_ordinary_pull_compatibility a f sX sY hX hY r identity_on_sections c conjugate)
    hInt realization
  intro P _ _
  unfold SheafOfModules.scalarPairComplexComparison SheafOfModules.scalarComplex
  dsimp only [section_compute_nat, cochain_counit, section_pull_compute_nat] at hall
  exact hall P

end AlgebraicGeometry.ProEtale.QuotientChange
