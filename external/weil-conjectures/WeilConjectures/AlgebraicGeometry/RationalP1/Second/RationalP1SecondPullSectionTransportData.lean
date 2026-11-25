/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.AlgebraicGeometry.RationalP1.PullSectionTransport
public import WeilConjectures.AlgebraicGeometry.RationalP1.Second.RationalP1SecondPullComparison
public import WeilConjectures.AlgebraicGeometry.RationalP1.Projective.ProjectiveDiagonalPullback
import WeilConjectures.AlgebraicGeometry.RationalP1.Projective.ProjectivePullSectionTensor
import WeilConjectures.AlgebraicGeometry.RationalP1.Tate.RationalTateSection
import WeilConjectures.AlgebraicGeometry.RationalP1.RationalP1TensorShiftNaturality

/-! The concrete tensor/shift transport data for the rational projective-line square. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor

section NativeTensor

attribute [local instance 20000]
  DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory
attribute [local instance 25000]
  AlgebraicGeometry.ProEtale.CondensedRing.projectionModuleMonoidal
  AlgebraicGeometry.ProEtale.CondensedRing.projectionModuleAbelian
  AlgebraicGeometry.ProEtale.CondensedRing.projectionModuleHasDerived
  AlgebraicGeometry.ProEtale.CondensedRing.projectionDerivedMonoidal
attribute [local instance 30000]
  AlgebraicGeometry.ProEtale.CondensedRing.projectionSheafMonoidal
  AlgebraicGeometry.ProEtale.CondensedRing.projectionCoefficientMonObj
  AlgebraicGeometry.ProEtale.CondensedRing.projectionModuleCategory
attribute [local instance 20000] CategoryTheory.traceSheafSymmetric
attribute [local irreducible] DerivedCategory.Qh
  CategoryTheory.Functor.leftDerivedFunctor CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Functor.leftDerivedTensorComparison CategoryTheory.Functor.leftDerivedFunctorCounit
  CategoryTheory.Mod.monoidalClosed CategoryTheory.Sheaf.monObj_sheafCompose_obj
  AlgebraicGeometry.ProEtale.upperStarFromPoint

-- Expose only the canonical structure aliases when checking implicit arguments.
attribute [local implicit_reducible]
  AlgebraicGeometry.ProEtale.sheafSymmetricCategory
  AlgebraicGeometry.ProEtale.sheafBraidedCategory
  CategoryTheory.GrothendieckTopology.symmetricCategory_sheaf_of_essentiallySmall
  CategoryTheory.GrothendieckTopology.braidedCategory_sheaf_of_essentiallySmall
  CategoryTheory.Sheaf.symmetricCategory
  CategoryTheory.Mod.derivedMonoidalCategory

attribute [-instance] AlgebraicGeometry.ProEtale.RationalP1.internalMonoidal
  AlgebraicGeometry.ProEtale.RationalP1.internalTensorCommShift

namespace AlgebraicGeometry.ProEtale.RationalP1
open DiagonalCoefficients CondensedRing

attribute [local irreducible] coefficient line twist firstProjection secondProjection square
attribute [local irreducible] moduleObjectDerivedPullback moduleObjectDerivedPushforward

-- Keep the categorical calculation independent of the large coefficient interfaces.
private theorem section_tensor_twist
    {C D : Type*} [Category C] [Category D]
    [MonoidalCategory C] [MonoidalCategory D]
    (F : C ⥤ D) (G : D ⥤ C) (s : F ⋙ G ≅ 𝟭 C)
    (T : C ⥤ C) (M B : C) (L : D)
    (a : M ⊗ B ≅ T.obj M) (a' : G.obj (F.obj M) ⊗ B ≅ T.obj (G.obj (F.obj M)))
    (eF : F.obj B ≅ L) (eG : G.obj L ≅ B)
    (δF : F.obj (M ⊗ B) ≅ F.obj M ⊗ F.obj B)
    (δG : G.obj (F.obj M ⊗ F.obj B) ≅ G.obj (F.obj M) ⊗ G.obj (F.obj B))
    (δG' : G.obj (F.obj M ⊗ L) ≅ G.obj (F.obj M) ⊗ G.obj L)
    (hδ : G.map δF.hom ≫ δG.hom ≫
      tensorHom (s.hom.app M) (s.hom.app B) = s.hom.app (M ⊗ B))
    (hn : G.map (tensorHom (𝟙 _) eF.hom) ≫ δG'.hom =
      δG.hom ≫ tensorHom (𝟙 _) (G.map eF.hom))
    (he : G.map eF.hom ≫ eG.hom = s.hom.app B)
    (ha : tensorHom (s.hom.app M) (𝟙 B) ≫ a.hom =
      a'.hom ≫ T.map (s.hom.app M)) :
    G.map (F.map a.inv ≫ δF.hom ≫ tensorHom (𝟙 _) eF.hom) ≫
      δG'.hom ≫ tensorHom (𝟙 _) eG.hom ≫ a'.hom ≫ T.map (s.hom.app M) =
      s.hom.app (T.obj M) := by
  simp only [Functor.map_comp, Category.assoc]
  rw [← ha, ← Category.assoc _ δG'.hom, hn]
  simp only [Category.assoc]
  rw [tensorHom_comp_tensorHom_assoc, Category.id_comp, he,
    tensorHom_comp_tensorHom_assoc, Category.id_comp, Category.comp_id]
  rw [reassoc_of% hδ]
  have hs := s.hom.naturality a.inv
  change G.map (F.map a.inv) ≫ s.hom.app (M ⊗ B) =
    s.hom.app (T.obj M) ≫ a.inv at hs
  rw [← Category.assoc, hs, Category.assoc, a.inv_hom_id]
  exact Category.comp_id _

private theorem tensor_comparison_right_naturality
    {C D : Type*} [Category C] [Category D]
    [MonoidalCategory C] [MonoidalCategory D]
    (F : C ⥤ D)
    (δ : (Functor.postcompose₂.obj F).obj (curriedTensor C) ≅
      (((Functor.whiskeringLeft₂ D).obj F).obj F).obj (curriedTensor D))
    (A : C) {B B' : C} (e : B ⟶ B') :
    F.map (tensorHom (𝟙 A) e) ≫ ((δ.app A).app B').hom =
      ((δ.app A).app B).hom ≫ tensorHom (𝟙 (F.obj A)) (F.map e) := by
  have hn := (δ.app A).hom.naturality e
  change F.map (A ◁ e) ≫ ((δ.app A).app B').hom =
    ((δ.app A).app B).hom ≫ F.obj A ◁ F.map e at hn
  simpa only [id_tensorHom] using hn

private def nativeTensorShiftIso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u}) (L : Modules Λ X)
    (A : DerivedCategory (Modules Λ X)) :
    A ⊗ (((DerivedCategory.singleFunctor (Modules Λ X) 0).obj L) ⟦(2 : ℤ)⟧) ≅
      (twist Λ X L).obj A := by
  have e := tensorShiftIso Λ X L A
  unfold internalMonoidal internalTensorBundle nativeTensorBundle at e
  exact e

private theorem nativeTensorShift_naturality
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u}) (L : Modules Λ X)
    {A B : DerivedCategory (Modules Λ X)} (f : A ⟶ B) :
    tensorHom f (𝟙 _) ≫ (nativeTensorShiftIso Λ X L B).hom =
      (nativeTensorShiftIso Λ X L A).hom ≫ (twist Λ X L).map f := by
  have h := tensorShiftIso_naturality Λ X L f
  unfold internalMonoidal internalTensorBundle nativeTensorBundle at h
  exact h

private def nativeTensorComparison
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X S : Scheme.{u}} (f : X ⟶ S) :
    (Functor.postcompose₂.obj (moduleObjectDerivedPullback Λ f)).obj
        (curriedTensor (DerivedCategory (Modules Λ S))) ≅
      (((Functor.whiskeringLeft₂ (DerivedCategory (Modules Λ X))).obj
        (moduleObjectDerivedPullback Λ f)).obj (moduleObjectDerivedPullback Λ f)).obj
          (curriedTensor (DerivedCategory (Modules Λ X))) := by
  have e := traceTensorComparison Λ f
  dsimp only [tracePull, CondensedRing.derivedTensor] at e
  exact e

private theorem pullTwist_hom
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X S : Scheme.{u}} (f : X ⟶ S)
    (LS : Modules Λ S) (LX : Modules Λ X)
    (e : (moduleObjectDerivedPullback Λ f).obj
      (((DerivedCategory.singleFunctor (Modules Λ S) 0).obj LS) ⟦(2 : ℤ)⟧) ≅
      ((DerivedCategory.singleFunctor (Modules Λ X) 0).obj LX) ⟦(2 : ℤ)⟧)
    (A : DerivedCategory (Modules Λ S)) :
    (pullTwistIso Λ f LS LX e A).hom =
      (moduleObjectDerivedPullback Λ f).map (nativeTensorShiftIso Λ S LS A).inv ≫
        (((nativeTensorComparison Λ f).app A).app
          (((DerivedCategory.singleFunctor (Modules Λ S) 0).obj LS) ⟦(2 : ℤ)⟧)).hom ≫
        tensorHom (𝟙 _) e.hom ≫
        (nativeTensorShiftIso Λ X LX ((moduleObjectDerivedPullback Λ f).obj A)).hom := by
  unfold pullTwistIso nativeTensorShiftIso nativeTensorComparison
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, tensorIso_hom,
    Iso.refl_hom]
  unfold internalMonoidal internalTensorBundle nativeTensorBundle
  rfl

private def nativeTensorShiftNatIso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u}) (L : Modules Λ X) :
    tensorRight (((DerivedCategory.singleFunctor (Modules Λ X) 0).obj L) ⟦(2 : ℤ)⟧) ≅
      twist Λ X L :=
  NatIso.ofComponents (nativeTensorShiftIso Λ X L)
    (fun f ↦ by
      change (f ▷ _) ≫ _ = _
      simpa only [tensorHom_id] using nativeTensorShift_naturality Λ X L f)

private def nativeTensorPullNatIso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X S : Scheme.{u}} (f : X ⟶ S)
    (B : DerivedCategory (Modules Λ S)) :
    tensorRight B ⋙ moduleObjectDerivedPullback Λ f ≅
      moduleObjectDerivedPullback Λ f ⋙
        tensorRight ((moduleObjectDerivedPullback Λ f).obj B) :=
  NatIso.ofComponents (fun A ↦ ((nativeTensorComparison Λ f).app A).app B) (by
    intro A A' m
    exact NatTrans.congr_app ((nativeTensorComparison Λ f).hom.naturality m) B)

private def nativePullTwistNatIso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X S : Scheme.{u}} (f : X ⟶ S)
    (LS : Modules Λ S) (LX : Modules Λ X)
    (e : (moduleObjectDerivedPullback Λ f).obj
      (((DerivedCategory.singleFunctor (Modules Λ S) 0).obj LS) ⟦(2 : ℤ)⟧) ≅
      ((DerivedCategory.singleFunctor (Modules Λ X) 0).obj LX) ⟦(2 : ℤ)⟧) :
    twist Λ S LS ⋙ moduleObjectDerivedPullback Λ f ≅
      moduleObjectDerivedPullback Λ f ⋙ twist Λ X LX :=
  Functor.isoWhiskerRight (nativeTensorShiftNatIso Λ S LS).symm _ ≪≫
    nativeTensorPullNatIso Λ f _ ≪≫
    Functor.isoWhiskerLeft _ ((curriedTensor _).flip.mapIso e) ≪≫
    Functor.isoWhiskerLeft _ (nativeTensorShiftNatIso Λ X LX)

private theorem nativePullTwistNatIso_app
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X S : Scheme.{u}} (f : X ⟶ S)
    (LS : Modules Λ S) (LX : Modules Λ X)
    (e : (moduleObjectDerivedPullback Λ f).obj
      (((DerivedCategory.singleFunctor (Modules Λ S) 0).obj LS) ⟦(2 : ℤ)⟧) ≅
      ((DerivedCategory.singleFunctor (Modules Λ X) 0).obj LX) ⟦(2 : ℤ)⟧)
    (A : DerivedCategory (Modules Λ S)) :
    (nativePullTwistNatIso Λ f LS LX e).app A = pullTwistIso Λ f LS LX e A := by
  apply Iso.ext
  rw [pullTwist_hom]
  simp only [nativePullTwistNatIso, nativeTensorPullNatIso, nativeTensorShiftNatIso,
    Iso.app_hom, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, NatIso.ofComponents_hom_app, NatIso.ofComponents_inv_app,
    id_tensorHom]
  rfl

private theorem pullTwist_naturality
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X S : Scheme.{u}} (f : X ⟶ S)
    (LS : Modules Λ S) (LX : Modules Λ X)
    (e : (moduleObjectDerivedPullback Λ f).obj
      (((DerivedCategory.singleFunctor (Modules Λ S) 0).obj LS) ⟦(2 : ℤ)⟧) ≅
      ((DerivedCategory.singleFunctor (Modules Λ X) 0).obj LX) ⟦(2 : ℤ)⟧)
    {A B : DerivedCategory (Modules Λ S)} (m : A ⟶ B) :
    (moduleObjectDerivedPullback Λ f).map ((twist Λ S LS).map m) ≫
        (pullTwistIso Λ f LS LX e B).hom =
      (pullTwistIso Λ f LS LX e A).hom ≫
        (twist Λ X LX).map ((moduleObjectDerivedPullback Λ f).map m) := by
  have h := (nativePullTwistNatIso Λ f LS LX e).hom.naturality m
  simpa only [← Iso.app_hom, nativePullTwistNatIso_app, Functor.comp_map] using h

private theorem map_tensor_shift_cancel
    {C D : Type*} [Category C] [Category D] (G : C ⥤ D)
    {A B X Y Z : C} {W : D}
    (f : A ⟶ B) (g : B ⟶ X) (h : X ⟶ Y) (e : Y ≅ Z) (k : G.obj Y ⟶ W) :
    G.map (f ≫ g ≫ h ≫ e.hom) ≫ G.map e.inv ≫ k =
      G.map (f ≫ g ≫ h) ≫ k := by
  simp only [Functor.map_comp, Category.assoc]
  rw [← G.map_comp_assoc e.hom e.inv, e.hom_inv_id, G.map_id, Category.id_comp]

-- The explicit categorical calculation shares the native tensor structures throughout.
private theorem pullTwist_section
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (Y : Scheme.{u})
    (f : diagonalSurface Y ⟶ ProjectiveLine Y)
    (h : diagonalImmersion Y ≫ f = 𝟙 (ProjectiveLine Y))
    (LS : Modules Λ (ProjectiveLine Y)) (LX : Modules Λ (diagonalSurface Y))
    (eF : (moduleObjectDerivedPullback Λ f).obj
      (((DerivedCategory.singleFunctor _ 0).obj LS) ⟦(2 : ℤ)⟧) ≅
      ((DerivedCategory.singleFunctor _ 0).obj LX) ⟦(2 : ℤ)⟧)
    (eG : (moduleObjectDerivedPullback Λ (diagonalImmersion Y)).obj
      (((DerivedCategory.singleFunctor _ 0).obj LX) ⟦(2 : ℤ)⟧) ≅
      ((DerivedCategory.singleFunctor _ 0).obj LS) ⟦(2 : ℤ)⟧)
    (he : (moduleObjectDerivedPullback Λ (diagonalImmersion Y)).map eF.hom ≫ eG.hom =
      (pullSectionIso Λ Y f h).hom.app
        (((DerivedCategory.singleFunctor _ 0).obj LS) ⟦(2 : ℤ)⟧))
    (A : DerivedCategory (Modules Λ (ProjectiveLine Y))) :
    (moduleObjectDerivedPullback Λ (diagonalImmersion Y)).map
        (pullTwistIso Λ f LS LX eF A).hom ≫
      (pullTwistIso Λ (diagonalImmersion Y) LX LS eG
        ((moduleObjectDerivedPullback Λ f).obj A)).hom ≫
      (twist Λ (ProjectiveLine Y) LS).map ((pullSectionIso Λ Y f h).hom.app A) =
      (pullSectionIso Λ Y f h).hom.app ((twist Λ (ProjectiveLine Y) LS).obj A) := by
  let F := moduleObjectDerivedPullback Λ f
  let G := moduleObjectDerivedPullback Λ (diagonalImmersion Y)
  let B := ((DerivedCategory.singleFunctor _ 0).obj LS) ⟦(2 : ℤ)⟧
  let L := ((DerivedCategory.singleFunctor _ 0).obj LX) ⟦(2 : ℤ)⟧
  let a := nativeTensorShiftIso Λ (ProjectiveLine Y) LS A
  let a' := nativeTensorShiftIso Λ (ProjectiveLine Y) LS (G.obj (F.obj A))
  let u := nativeTensorShiftIso Λ (diagonalSurface Y) LX (F.obj A)
  have hn : G.map (tensorHom (𝟙 (F.obj A)) eF.hom) ≫
      (((nativeTensorComparison Λ (diagonalImmersion Y)).app (F.obj A)).app L).hom =
      (((nativeTensorComparison Λ (diagonalImmersion Y)).app (F.obj A)).app
        (F.obj B)).hom ≫ tensorHom (𝟙 _) (G.map eF.hom) := by
    simpa only [tracePull] using
      tensor_comparison_right_naturality (tracePull Λ (diagonalImmersion Y))
        (nativeTensorComparison Λ (diagonalImmersion Y)) (F.obj A) eF.hom
  have ht := section_tensor_twist F G (pullSectionIso Λ Y f h)
    (twist Λ (ProjectiveLine Y) LS) A B L a a' eF eG
    (((nativeTensorComparison Λ f).app A).app B)
    (((nativeTensorComparison Λ (diagonalImmersion Y)).app (F.obj A)).app (F.obj B))
    (((nativeTensorComparison Λ (diagonalImmersion Y)).app (F.obj A)).app L)
    (by exact pullSectionIso_tensor Λ Y f h A B) hn he
    (nativeTensorShift_naturality Λ (ProjectiveLine Y) LS
      ((pullSectionIso Λ Y f h).hom.app A))
  simp only [pullTwist_hom, Category.assoc]
  exact (map_tensor_shift_cancel G _ _ _ u _).trans ht

private theorem pullSectionTransportData_of_hom
    {C D : Type*} [Category C] [Category D]
    {F₁ F₂ : C ⥤ D} {G : D ⥤ C}
    {s₁ : F₁ ⋙ G ≅ 𝟭 C} {s₂ : F₂ ⋙ G ≅ 𝟭 C}
    (T : C ⥤ C) (U : D ⥤ D) (M : C)
    (e₁ : F₁.obj (T.obj M) ≅ U.obj (F₁.obj M))
    (e₂ : F₂.obj (T.obj M) ≅ U.obj (F₂.obj M))
    (b : F₁.obj M ≅ F₂.obj M)
    (d : ∀ N, G.obj (U.obj N) ≅ T.obj (G.obj N))
    (h₁ : G.map e₁.hom ≫ (d (F₁.obj M)).hom ≫ T.map (s₁.hom.app M) =
      s₁.hom.app (T.obj M))
    (h₂ : G.map e₂.hom ≫ (d (F₂.obj M)).hom ≫ T.map (s₂.hom.app M) =
      s₂.hom.app (T.obj M))
    (hb : G.map (U.map b.inv) ≫ (d (F₁.obj M)).hom =
      (d (F₂.obj M)).hom ≫ T.map (G.map b.inv)) :
    ∃ _ : PullSectionTransportData (G := G) (s₁ := s₁) (s₂ := s₂) T U M e₁ e₂ b,
      True := by
  refine ⟨{ d₁ := d (F₁.obj M), d₂ := d (F₂.obj M), h₁ := ?_, h₂ := h₂, hb := ?_ },
    trivial⟩
  · rw [← h₁]
    simp only [← G.map_comp_assoc, e₁.inv_hom_id, G.map_id, Category.id_comp]
  · simpa only [Category.assoc] using
      congrArg (fun m ↦ G.map e₂.hom ≫ m ≫ T.map (s₁.hom.app M)) hb

set_option linter.unusedVariables false in
-- The calculation below is elaborated with the native tensor instances of this section.
private theorem second_pull_section_transport_data_aux
    (l : ℕ) [Fact l.Prime] (c : Option (PadicAlgCl.FiniteIntermediateField l))
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (hpl : p ≠ l)
    (Y : Scheme.{u}) [Y.Over (Spec (.of k))]
    [hproj : ∀ x : ProjectiveLine Y, Invertible (l : (ProjectiveLine Y).residueField x)]
    [hdiag : ∀ x : diagonalSurface Y, Invertible (l : (diagonalSurface Y).residueField x)]
    (K : DerivedCategory (Modules (coefficient l c).X Y)) :
    ∃ data : PullSectionTransportData
      (F₁ := moduleObjectDerivedPullback (coefficient l c).X (firstProjection Y))
      (F₂ := moduleObjectDerivedPullback (coefficient l c).X (secondProjection Y))
      (G := moduleObjectDerivedPullback (coefficient l c).X (diagonalImmersion Y))
      (s₁ := pullSectionIso (coefficient l c).X Y (firstProjection Y)
        (by unfold firstProjection; exact pullback.diagonal_fst _))
      (s₂ := pullSectionIso (coefficient l c).X Y (secondProjection Y)
        (by unfold secondProjection; exact pullback.diagonal_snd _))
      (T := twist (coefficient l c).X (ProjectiveLine Y)
        (line l c (ProjectiveLine Y)))
      (U := twist (coefficient l c).X (diagonalSurface Y)
        (line l c (diagonalSurface Y)))
      (M := ((moduleObjectDerivedPullback (coefficient l c).X (ProjectiveLine Y ↘ Y)).obj K))
      (e₁ := pullTwistIso (coefficient l c).X (firstProjection Y) _ _
        (shiftedLineComparison l c (firstProjection Y))
        ((moduleObjectDerivedPullback (coefficient l c).X (ProjectiveLine Y ↘ Y)).obj K))
      (e₂ := pullTwistIso (coefficient l c).X (secondProjection Y) _ _
        (secondLineComparison l c k p hpl Y)
        ((moduleObjectDerivedPullback (coefficient l c).X (ProjectiveLine Y ↘ Y)).obj K))
      (b := (ambientPullbackComparison (coefficient l c).X (square Y)).symm.app K), True := by
  let Λ := (coefficient l c).X
  let F₁ := moduleObjectDerivedPullback Λ (firstProjection Y)
  let F₂ := moduleObjectDerivedPullback Λ (secondProjection Y)
  let G := moduleObjectDerivedPullback Λ (diagonalImmersion Y)
  let T := twist Λ (ProjectiveLine Y) (line l c (ProjectiveLine Y))
  let U := twist Λ (diagonalSurface Y) (line l c (diagonalSurface Y))
  let M := (moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y)).obj K
  let s₁ := pullSectionIso Λ Y (firstProjection Y)
    (by unfold firstProjection; exact pullback.diagonal_fst _)
  let s₂ := pullSectionIso Λ Y (secondProjection Y)
    (by unfold secondProjection; exact pullback.diagonal_snd _)
  let eD := shiftedLineComparison l c (diagonalImmersion Y)
  let e₁ := pullTwistIso Λ (firstProjection Y) _ _
    (shiftedLineComparison l c (firstProjection Y)) M
  let e₂ := pullTwistIso Λ (secondProjection Y) _ _ (secondLineComparison l c k p hpl Y) M
  let d (N : DerivedCategory (Modules Λ (diagonalSurface Y))) :=
    pullTwistIso Λ (diagonalImmersion Y) (line l c (diagonalSurface Y))
      (line l c (ProjectiveLine Y)) eD N
  have h₁ : G.map e₁.hom ≫ (d (F₁.obj M)).hom ≫ T.map (s₁.hom.app M) =
      s₁.hom.app (T.obj M) :=
    pullTwist_section Λ Y (firstProjection Y) _ _ _ _ eD
      (shiftedLineComparison_section l c Y (firstProjection Y) _) M
  have he₂ : G.map (secondLineComparison l c k p hpl Y).hom ≫ eD.hom =
      s₂.hom.app (((DerivedCategory.singleFunctor _ 0).obj
        (line l c (ProjectiveLine Y))) ⟦(2 : ℤ)⟧) := by
    have hcmp : secondLineComparison l c k p hpl Y =
        shiftedLineComparison l c (secondProjection Y) := by
      unfold secondLineComparison
      congr 1 <;> exact Subsingleton.elim _ _
    rw [hcmp]
    exact shiftedLineComparison_section l c Y (secondProjection Y) _
  have h₂ : G.map e₂.hom ≫ (d (F₂.obj M)).hom ≫ T.map (s₂.hom.app M) =
      s₂.hom.app (T.obj M) :=
    pullTwist_section Λ Y (secondProjection Y) _ _ _ _ eD he₂ M
  exact pullSectionTransportData_of_hom T U M e₁ e₂
    ((ambientPullbackComparison Λ (square Y)).symm.app K) d h₁ h₂
    (pullTwist_naturality Λ (diagonalImmersion Y)
      (line l c (diagonalSurface Y)) (line l c (ProjectiveLine Y)) eD
      ((ambientPullbackComparison Λ (square Y)).symm.app K).inv)

end AlgebraicGeometry.ProEtale.RationalP1

end NativeTensor

namespace AlgebraicGeometry.ProEtale.RationalP1
open DiagonalCoefficients CondensedRing

attribute [local irreducible] coefficient line twist firstProjection secondProjection square
attribute [local irreducible] moduleObjectDerivedPullback moduleObjectDerivedPushforward

set_option linter.unusedVariables false in
/-- The native tensor and shift comparisons commute with restriction to the diagonal.
The fields are exactly the two section naturality equations and the square comparison
naturality equation needed by `pull_section_transport`. -/
theorem second_pull_section_transport_data
    (l : ℕ) [Fact l.Prime] (c : Option (PadicAlgCl.FiniteIntermediateField l))
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (hpl : p ≠ l)
    (Y : Scheme.{u}) [Y.Over (Spec (.of k))]
    [hproj : ∀ x : ProjectiveLine Y, Invertible (l : (ProjectiveLine Y).residueField x)]
    [hdiag : ∀ x : diagonalSurface Y, Invertible (l : (diagonalSurface Y).residueField x)]
    (K : DerivedCategory (Modules (coefficient l c).X Y)) :
    ∃ data : PullSectionTransportData
      (F₁ := moduleObjectDerivedPullback (coefficient l c).X (firstProjection Y))
      (F₂ := moduleObjectDerivedPullback (coefficient l c).X (secondProjection Y))
      (G := moduleObjectDerivedPullback (coefficient l c).X (diagonalImmersion Y))
      (s₁ := pullSectionIso (coefficient l c).X Y (firstProjection Y)
        (by unfold firstProjection; exact pullback.diagonal_fst _))
      (s₂ := pullSectionIso (coefficient l c).X Y (secondProjection Y)
        (by unfold secondProjection; exact pullback.diagonal_snd _))
      (T := twist (coefficient l c).X (ProjectiveLine Y)
        (line l c (ProjectiveLine Y)))
      (U := twist (coefficient l c).X (diagonalSurface Y)
        (line l c (diagonalSurface Y)))
      (M := ((moduleObjectDerivedPullback (coefficient l c).X (ProjectiveLine Y ↘ Y)).obj K))
      (e₁ := pullTwistIso (coefficient l c).X (firstProjection Y) _ _
        (shiftedLineComparison l c (firstProjection Y))
        ((moduleObjectDerivedPullback (coefficient l c).X (ProjectiveLine Y ↘ Y)).obj K))
      (e₂ := pullTwistIso (coefficient l c).X (secondProjection Y) _ _
        (secondLineComparison l c k p hpl Y)
        ((moduleObjectDerivedPullback (coefficient l c).X (ProjectiveLine Y ↘ Y)).obj K))
      (b := (ambientPullbackComparison (coefficient l c).X (square Y)).symm.app K), True :=
  second_pull_section_transport_data_aux l c k p hpl Y K

end AlgebraicGeometry.ProEtale.RationalP1
