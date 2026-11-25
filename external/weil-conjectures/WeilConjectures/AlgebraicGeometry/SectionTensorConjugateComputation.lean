/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.InternalScalarPullbackNormalizationData
import WeilConjectures.AlgebraicGeometry.SectionScalarComputationTransport

/-! # K-flat computation of conjugated scalar tensor comparisons

(auxiliary; not a blueprint node)
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option Elab.async false

universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open CategoryTheory.InternalAbelianSheafModule
open scoped CategoryTheory.Obj TensorProduct ChangeOfRings
attribute [local instance 20000] AlgebraicGeometry.ProEtale.sheafBraidedCategory
attribute [local instance 20000] AlgebraicGeometry.ProEtale.CondensedRing.laxMonoidal_Q

namespace AlgebraicGeometry.ProEtale.QuotientChange
variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
  [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (ModuleRingedComparison.modules Λ T)]
  [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (ModuleRingedComparison.modules Λ' T)]

attribute [local irreducible] CategoryTheory.Functor.leftDerivedFunctor
  CategoryTheory.Functor.mapDerivedCategory
  ModuleRingedComparison.tensor ModuleRingedComparison.derivedEquivalence
  ModuleRingedComparison.qTensor ModuleRingedComparison.tensorComparison
  sectionScalarCoefficient sectionScalarRestriction
  DerivedCategory.monoidalClosed
  DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory

attribute [local irreducible] sectionTensorRightComparison sectionTensorRightLocalization

attribute [local implicit_reducible] sectionScalarTensor
  ModuleRingedComparison.totalTensor
  CategoryTheory.Functor.map₂HomologicalComplex
  ModuleRingedComparison.sectionLocalizationComparison

private theorem mapEquation
    {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D)
    {X Y Z : C} {W : D} {f : X ⟶ Y} {g : Y ⟶ Z} {h : X ⟶ Z}
    (e : f ≫ g = h) (k : F.obj Z ⟶ W) :
    F.map f ≫ F.map g ≫ k = F.map h ≫ k := by
  rw [← F.map_comp_assoc, e]

private theorem mapFixedCoefficient
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    (T : C × D ⥤ E) {X X' : C} {Y Y' : D} (f : X ⟶ X') (g : Y ⟶ Y') :
    T.map (Prod.mkHom f (𝟙 Y)) ≫ T.map (Prod.mkHom (𝟙 X') g) =
      T.map (Prod.mkHom f g) := by
  rw [← T.map_comp]
  simp only [prod_comp, Category.comp_id, Category.id_comp]

private theorem tensorCoefficientPaste
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    (T : C × D ⥤ E) {X X' : C} {Y Y' : D} (f : X ⟶ X') (g : Y ⟶ Y')
    {A V W : E} {θ : A ⟶ T.obj (X, Y)} {q : T.obj (X', Y') ⟶ V}
    {z : V ⟶ W} {l : A ⟶ W}
    (h : θ ≫ T.map (Prod.mkHom f g) ≫ q ≫ z = l) :
    θ ≫ T.map (Prod.mkHom f (𝟙 Y)) ≫
      (T.map (Prod.mkHom (𝟙 X') g) ≫ q ≫ z) = l := by
  calc
    _ = θ ≫ (T.map (Prod.mkHom f (𝟙 Y)) ≫ T.map (Prod.mkHom (𝟙 X') g)) ≫
        q ≫ z := by simp only [Category.assoc]
    _ = l := by rw [mapFixedCoefficient]; exact h

private theorem conjugateComputation
    {C : Type*} [Category* C] {A B B' D D' H G : C}
    (c : A ⟶ B) (u : B ⟶ B') [Epi (c ≫ u)]
    {e : B ⟶ D} {e' : B' ⟶ D'} {v : D ⟶ D'} {w : D' ⟶ H} {r : B' ⟶ H}
    {t : A ⟶ G} {θ : G ⟶ D} {l : G ⟶ H}
    (hn : u ≫ e' = e ≫ v) (hc : c ≫ e = t ≫ θ)
    (hθ : θ ≫ v ≫ w = l) (ht : t ≫ l = c ≫ u ≫ r) :
    e' ≫ w = r := by
  apply (cancel_epi (c ≫ u)).mp
  simp only [Category.assoc]
  rw [reassoc_of% hn, ← Category.assoc c, hc, Category.assoc, hθ, ht]

private theorem conjugateComputationTriple
    {C : Type*} [Category* C] {A A' B B' D D' H G : C}
    (c₀ : A ⟶ A') (c₁ : A' ⟶ B) (u : B ⟶ B') [Epi ((c₀ ≫ c₁) ≫ u)]
    {e : B ⟶ D} {e' : B' ⟶ D'} {v : D ⟶ D'} {w : D' ⟶ H} {r : B' ⟶ H}
    {t : A ⟶ G} {θ : G ⟶ D} {l : G ⟶ H}
    (hn : u ≫ e' = e ≫ v) (hc : (c₀ ≫ c₁) ≫ e = t ≫ θ)
    (hθ : θ ≫ v ≫ w = l) (ht : t ≫ l = c₀ ≫ c₁ ≫ u ≫ r) :
    e' ≫ w = r := by
  apply conjugateComputation (c₀ ≫ c₁) u hn hc hθ
  simpa only [Category.assoc] using ht

private theorem natTrans_eq_app_of_iso
    {C D : Type*} [Category* C] [Category* D] {F G : C ⥤ D}
    (α β : F ⟶ G) {X Y : C} (i : X ≅ Y) (h : α.app X = β.app X) :
    α.app Y = β.app Y := by
  apply (cancel_epi (F.map i.hom)).mp
  rw [α.naturality, β.naturality, h]

private def fixedTensorComputation
    {C D : Type*} [Category* C] [Category* D]
    (Q : C ⥤ D) (R : C ⥤ C ⥤ C) (T : D × D ⥤ D)
    (X : C) (B : D) (b : B ⟶ Q.obj X)
    (q : Q.prod Q ⋙ T ⟶ Functor.uncurry.obj R ⋙ Q)
    (H : C ⥤ C) (τ : R.flip.obj X ⟶ H) :
    Q ⋙ (𝟭 D).prod' ((Functor.const D).obj B) ⋙ T ⟶ H ⋙ Q := by
  let J := (𝟭 C).prod' ((Functor.const C).obj X)
  let c := NatTrans.prod' (𝟙 (𝟭 D)) ((Functor.const D).map b)
  let i : Q ⋙ (𝟭 D).prod' ((Functor.const D).obj (Q.obj X)) ⋙ T ≅
      J ⋙ Q.prod Q ⋙ T := NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
    intro A A' f
    dsimp only [J, Functor.comp_map, Functor.prod'_map, Functor.prod_map,
      Functor.id_map, Functor.const_obj_map, Iso.refl_hom]
    simp only [Category.comp_id, Category.id_comp]
    exact congrArg (fun g ↦ T.map (Prod.mkHom (Q.map f) g)) (Q.map_id X).symm)
  let j : J ⋙ Functor.uncurry.obj R ⋙ Q ≅ R.flip.obj X ⋙ Q :=
    NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
      intro A A' f
      dsimp only [J, Functor.comp_map, Functor.prod'_map, Functor.id_map,
        Functor.const_obj_map, Functor.uncurry_obj_map, Iso.refl_hom,
        Functor.prod'_obj, Functor.id_obj, Functor.const_obj_obj, Functor.flip_obj_map]
      simp only [CategoryTheory.Functor.map_id, Category.comp_id,
        Category.id_comp])
  exact Functor.whiskerLeft Q (Functor.whiskerRight c T) ≫ i.hom ≫
    Functor.whiskerLeft J q ≫ j.hom ≫ Functor.whiskerRight τ Q

private theorem fixedTensorComputation_app
    {C D : Type*} [Category* C] [Category* D]
    (Q : C ⥤ D) (R : C ⥤ C ⥤ C) (T : D × D ⥤ D)
    (X : C) (B : D) (b : B ⟶ Q.obj X)
    (q : Q.prod Q ⋙ T ⟶ Functor.uncurry.obj R ⋙ Q)
    (H : C ⥤ C) (τ : R.flip.obj X ⟶ H) (A : C) :
    (fixedTensorComputation Q R T X B b q H τ).app A =
      T.map (Prod.mkHom (𝟙 _) b) ≫ q.app (A, X) ≫ Q.map (τ.app A) := by
  simp only [fixedTensorComputation, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, NatTrans.prod', NatTrans.id_app, Functor.const_map_app,
    NatIso.ofComponents_hom_app, Iso.refl_hom, Category.id_comp,
    Functor.prod'_obj, Functor.id_obj, Functor.const_obj_obj]

private def tensorComputation (a : Λ ⟶ Λ') [IsMonHom a] (T : Scheme.{u}) :
    DerivedCategory.Q ⋙ sectionScalarTensor a T ⟶
      Functor.mapHomologicalComplex
        (tensorRight ((ModuleRingedComparison.equivalence Λ T).functor.obj (B₀ a T)))
        (.up ℤ) ⋙ DerivedCategory.Q :=
  fixedTensorComputation DerivedCategory.Q
    ((curriedTensor (ModuleRingedComparison.modules Λ T)).map₂CochainComplex)
    (ModuleRingedComparison.tensor Λ T)
    ((CochainComplex.singleFunctor _ 0).obj
      ((ModuleRingedComparison.equivalence Λ T).functor.obj (B₀ a T))) _
    (sectionScalarCoefficient a T).hom (ModuleRingedComparison.qTensor Λ T) _
    (CochainComplex.map₂HomologicalComplexFlipObjSingleIso
      (curriedTensor (ModuleRingedComparison.modules Λ T))
      ((ModuleRingedComparison.equivalence Λ T).functor.obj (B₀ a T))).hom

omit [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (ModuleRingedComparison.modules Λ' T)]
  [IsCommMonObj Λ'] in
private theorem tensorComputation_app (a : Λ ⟶ Λ') [IsMonHom a] (T : Scheme.{u})
    (P : CochainComplex (ModuleRingedComparison.modules Λ T) ℤ) :
    (tensorComputation a T).app P =
      (ModuleRingedComparison.tensor Λ T).map
        (Prod.mkHom (𝟙 _) (sectionScalarCoefficient a T).hom) ≫
      (ModuleRingedComparison.qTensor Λ T).app
        (P, (CochainComplex.singleFunctor _ 0).obj
          ((ModuleRingedComparison.equivalence Λ T).functor.obj (B₀ a T))) ≫
      DerivedCategory.Q.map (CochainComplex.mapBifunctorSingle₂Iso
        (curriedTensor (ModuleRingedComparison.modules Λ T))
        ((ModuleRingedComparison.equivalence Λ T).functor.obj (B₀ a T)) P).hom := by
  simp only [tensorComputation, fixedTensorComputation_app,
    CochainComplex.map₂HomologicalComplexFlipObjSingleIso_hom_app]

attribute [local irreducible] tensorComputation

private def scalarComputation (a : Λ ⟶ Λ') [IsMonHom a] (T : Scheme.{u})
    (s : SectionScalarComparison a T) :
    DerivedCategory.Q ⋙ s.pair.derived ⟶
      SheafOfModules.scalarComplex.{u + 1, u, u + 1} s.pair.extension s.pair.extension_additive ⋙
        DerivedCategory.Q := by
  exact Functor.whiskerRight (DerivedCategory.quotientCompQhIso _).inv s.pair.derived ≫
    Functor.whiskerLeft (HomotopyCategory.quotient _ (.up ℤ)) s.pair.counit ≫
    Functor.whiskerRight (s.pair.extension.mapHomotopyCategoryFactors (.up ℤ)).hom
      DerivedCategory.Qh ≫
    Functor.whiskerLeft
      (SheafOfModules.scalarComplex.{u + 1, u, u + 1} s.pair.extension s.pair.extension_additive)
      (DerivedCategory.quotientCompQhIso _).hom

private theorem mapIdentityBetween
    {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D)
    {X : C} {A B Z : D} (f : A ⟶ B) (g : B ⟶ F.obj X) (h : F.obj X ⟶ Z) :
    f ≫ g ≫ F.map (𝟙 X) ≫ h = f ≫ g ≫ h := by
  rw [F.map_id, Category.id_comp]

private theorem scalarComputation_app (a : Λ ⟶ Λ') [IsMonHom a] (T : Scheme.{u})
    (s : SectionScalarComparison a T)
    (P : CochainComplex (ModuleRingedComparison.modules Λ T) ℤ) :
    (scalarComputation a T s).app P =
      SheafOfModules.scalarPairComplexComparison.{u + 1, u, u + 1, u + 1}
        s.pair.extension s.pair.extension_additive s.pair.derived s.pair.counit P := by
  change s.pair.derived.map ((DerivedCategory.quotientCompQhIso _).inv.app P) ≫
    s.pair.counit.app ((HomotopyCategory.quotient _ (.up ℤ)).obj P) ≫
    DerivedCategory.Qh.map (𝟙 _) ≫ (DerivedCategory.quotientCompQhIso _).hom.app
      ((SheafOfModules.scalarComplex.{u + 1, u, u + 1}
        s.pair.extension s.pair.extension_additive).obj P) = _
  exact mapIdentityBetween DerivedCategory.Qh _ _ _

private def restrictedScalarComputation (a : Λ ⟶ Λ') [IsMonHom a] (T : Scheme.{u})
    (s : SectionScalarComparison a T)
    (o : s.pair.extension ⋙ SheafOfModules.scalarRestriction.{u + 1, u, u + 1}
      (sectionScalarMap.{u + 1, u + 1, u} (Scheme.ProEt.topology T) (coefficientMap a T)) ≅
        tensorRight ((ModuleRingedComparison.equivalence Λ T).functor.obj (B₀ a T))) :
    DerivedCategory.Q ⋙ s.pair.derived ⋙
      SheafOfModules.scalarDerivedRestriction.{u + 1, u, u + 1, u + 1}
      (sectionScalarMap.{u + 1, u + 1, u} (Scheme.ProEt.topology T) (coefficientMap a T)) ⟶
      Functor.mapHomologicalComplex
        (tensorRight ((ModuleRingedComparison.equivalence Λ T).functor.obj (B₀ a T)))
        (.up ℤ) ⋙ DerivedCategory.Q := by
  exact Functor.whiskerRight (scalarComputation a T s) _ ≫
    Functor.whiskerLeft
      (SheafOfModules.scalarComplex.{u + 1, u, u + 1} s.pair.extension s.pair.extension_additive)
      (SheafOfModules.scalarRestrictionComparison.{u + 1, u, u + 1, u + 1}
        (sectionScalarMap.{u + 1, u + 1, u} (Scheme.ProEt.topology T) (coefficientMap a T))).hom ≫
    Functor.whiskerRight
      (Functor.mapHomologicalComplexCompIso o (.up ℤ)).hom DerivedCategory.Q

attribute [local irreducible] scalarComputation restrictedScalarComputation

-- Pasting the two computations elaborates both derived tensor and scalar structures.
/-- Conjugated normalized scalar tensor maps have the section K-flat computation equation.
Source: Stacks Project, Tags 03EK, 06YY, 0G7E and 07A6; blueprint integral proper-base-change
proof paragraph (1); second step of lem-sfb-section-tensor-normalization-transport.
(auxiliary; not a blueprint node).

Proof: first take a section complex which is the termwise image of an internal complex.
Substitute the supplied conjugation equation for e. The scalar normalization identifies
its scalar computation with the internal computation; the normalized section tensor
representative equation identifies its tensor localization with the image of the internal
localization map. TensorNormalized now replaces the latter composite by the restricted
scalar counit followed by the localized ordinary internal comparison. The ordinary scalar
normalization and the given generator equation for o identify the ordinary maps: both
send every sheafified local generator z tensor x to x tensor z, and such generators detect
equality after sheafification. The canonical composition and single-complex comparisons
cancel, yielding the displayed equation. Every section complex is isomorphic to a termwise
image under the exact section equivalence. Naturality of e, of the scalar computation
counit, of the tensor localization and of the single-factor total comparison transports
this equation along that isomorphism. Exactness and the tensor comparison preserve and
reflect K-flatness and flat terms. Thus it holds for the stated P. The calculation uses
no flatness of the coefficient map and no boundedness; it also covers zero coefficients
and the empty scheme. -/
theorem section_tensor_conjugate_computation (a : Λ ⟶ Λ') [IsMonHom a]
    (T : Scheme.{u}) (s : SectionScalarComparison a T)
    (hs : SectionScalarNormalized a T s) (t : TensorNormalization a T)
    (ht : TensorNormalized a T t)
    (o : s.pair.extension ⋙ SheafOfModules.scalarRestriction.{u + 1, u, u + 1}
      (sectionScalarMap.{u + 1, u + 1, u} (Scheme.ProEt.topology T) (coefficientMap a T)) ≅
        tensorRight ((ModuleRingedComparison.equivalence Λ T).functor.obj (B₀ a T)))
    (ho : (∀ (M : ModuleRingedComparison.modules Λ T) (U : T.ProEtᵒᵖ)
      (z : (ModuleRingedComparison.ring Λ' T).obj.obj U) (x : M.val.obj U),
    (o.hom.app M).val.app U
      ((eqToHom (s.pair.extension_obj M).symm).val.app U
        ((toSheafify (Scheme.ProEt.topology T)
          (SheafOfModules.changeOfRingsPresheaf
            (sectionScalarMap.{u + 1, u + 1, u} (Scheme.ProEt.topology T)
              (coefficientMap a T)) M).presheaf).app U
              (z ⊗ₜ[(ModuleRingedComparison.ring Λ T).obj.obj U,((sectionScalarMap
                  (Scheme.ProEt.topology T) (coefficientMap a T)).hom.app U).hom] x))) =
      ModuleRingedComparison.sectionPureTensor Λ T M
        ((ModuleRingedComparison.equivalence Λ T).functor.obj (B₀ a T)) U x z))
    (e : s.pair.derived ⋙ SheafOfModules.scalarDerivedRestriction.{u + 1, u, u + 1, u + 1}
      (sectionScalarMap.{u + 1, u + 1, u} (Scheme.ProEt.topology T) (coefficientMap a T)) ≅
        sectionScalarTensor a T)
    (he : ∀ M : DerivedCategory (Modules Λ T),
    (ModuleRingedComparison.derivedEquivalence Λ T).functor.map (t.derived.hom.app M) ≫
        (ModuleRingedComparison.tensorComparison Λ T).hom.app (M, B a T) =
      (sectionScalarRestriction a T s).hom.app ((D a T).obj M) ≫
        (SheafOfModules.scalarDerivedRestriction.{u + 1, u, u + 1, u + 1}
          (sectionScalarMap.{u + 1, u + 1, u} (Scheme.ProEt.topology T) (coefficientMap a T))).map
            (s.derived.hom.app M) ≫
        e.hom.app ((ModuleRingedComparison.derivedEquivalence Λ T).functor.obj M)) :
    (∀ (P : CochainComplex (ModuleRingedComparison.modules Λ T) ℤ),
    CochainComplex.IsKFlatIndependentCoefficients (R := ModuleRingedComparison.ring Λ T) P →
    (∀ n : ℤ, SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
      (R := ModuleRingedComparison.ring Λ T) (P.X n)) →
    e.hom.app (DerivedCategory.Q.obj P) ≫
        (ModuleRingedComparison.tensor Λ T).map
          (Prod.mkHom (𝟙 _) (sectionScalarCoefficient a T).hom) ≫
        (ModuleRingedComparison.qTensor Λ T).app
          (P, (CochainComplex.singleFunctor _ 0).obj
            ((ModuleRingedComparison.equivalence Λ T).functor.obj (B₀ a T))) ≫
        DerivedCategory.Q.map (CochainComplex.mapBifunctorSingle₂Iso
          (curriedTensor (ModuleRingedComparison.modules Λ T))
          ((ModuleRingedComparison.equivalence Λ T).functor.obj (B₀ a T)) P).hom =
      (SheafOfModules.scalarDerivedRestriction.{u + 1, u, u + 1, u + 1}
        (sectionScalarMap.{u + 1, u + 1, u} (Scheme.ProEt.topology T) (coefficientMap a T))).map
          (SheafOfModules.scalarPairComplexComparison.{u + 1, u, u + 1, u + 1}
          s.pair.extension s.pair.extension_additive
            s.pair.derived s.pair.counit P) ≫
        (SheafOfModules.scalarRestrictionComparison.{u + 1, u, u + 1, u + 1}
          (sectionScalarMap.{u + 1, u + 1, u} (Scheme.ProEt.topology T)
            (coefficientMap a T))).hom.app
            ((SheafOfModules.scalarComplex.{u + 1, u, u + 1}
              s.pair.extension s.pair.extension_additive).obj P) ≫
        DerivedCategory.Q.map ((Functor.mapHomologicalComplexCompIso o (.up ℤ)).hom.app P)) := by
  let U := SheafOfModules.scalarDerivedRestriction.{u + 1, u, u + 1, u + 1}
    (sectionScalarMap.{u + 1, u + 1, u} (Scheme.ProEt.topology T) (coefficientMap a T))
  let F := ModuleRingedComparison.derivedEquivalence Λ T
  let E := (ModuleRingedComparison.equivalence Λ T).functor.mapHomologicalComplex (.up ℤ)
  let lhs := Functor.whiskerLeft DerivedCategory.Q e.hom ≫ tensorComputation a T
  let rhs := restrictedScalarComputation a T s o
  have himage (A : CochainComplex (Modules Λ T) ℤ)
      (hA : CochainComplex.IsKFlatIndependentCoefficients
        (R := ModuleRingedComparison.ring Λ T) (E.obj A))
      (hfA : ∀ n : ℤ, SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
        (R := ModuleRingedComparison.ring Λ T)
        ((ModuleRingedComparison.equivalence Λ T).functor.obj (A.X n))) :
      lhs.app (E.obj A) = rhs.app (E.obj A) := by
    let α := ModuleRingedComparison.sectionLocalizationComparison Λ T A
    let c := (sectionScalarRestriction a T s).hom.app ((D a T).obj
      (DerivedCategory.Q.obj A)) ≫ U.map (s.derived.hom.app (DerivedCategory.Q.obj A))
    have hc : IsIso c := by dsimp only [c, U]; infer_instance
    have hn : U.map (s.pair.derived.map α.hom) ≫
        e.hom.app (DerivedCategory.Q.obj (E.obj A)) =
      e.hom.app (F.functor.obj (DerivedCategory.Q.obj A)) ≫
        (sectionScalarTensor a T).map α.hom := by
      simpa only [Functor.comp_map] using e.hom.naturality α.hom
    change U.map (s.pair.derived.map α.hom) ≫
        e.hom.app (DerivedCategory.Q.obj (E.obj A)) =
      e.hom.app (F.functor.obj (DerivedCategory.Q.obj A)) ≫
        (ModuleRingedComparison.tensor Λ T).map (Prod.mkHom α.hom (𝟙 _)) at hn
    have hconj : c ≫ e.hom.app (F.functor.obj (DerivedCategory.Q.obj A)) =
        F.functor.map (t.derived.hom.app (DerivedCategory.Q.obj A)) ≫
          (ModuleRingedComparison.tensorComparison Λ T).hom.app
            (DerivedCategory.Q.obj A, B a T) := by
      simpa only [c, Category.assoc] using (he (DerivedCategory.Q.obj A)).symm
    have hθ := tensorCoefficientPaste (ModuleRingedComparison.tensor Λ T)
      α.hom (sectionScalarCoefficient a T).hom (section_tensor_right_computation a T A)
    have hscalar := section_scalar_computation_transport a T s hs t o ho A hA hfA
    have hfinish := (mapEquation F.functor (ht A)
      (sectionTensorRightLocalization a T A).hom).trans hscalar
    have h := conjugateComputationTriple
      ((sectionScalarRestriction a T s).hom.app ((D a T).obj (DerivedCategory.Q.obj A)))
      (U.map (s.derived.hom.app (DerivedCategory.Q.obj A)))
      (U.map (s.pair.derived.map α.hom)) hn hconj hθ hfinish
    simpa only [lhs, rhs, tensorComputation_app, restrictedScalarComputation,
      scalarComputation_app, NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.const_obj_obj, Functor.id_obj, Category.assoc] using h
  intro P hP hflat
  suffices h : lhs.app P = rhs.app P by
    simpa only [lhs, rhs, tensorComputation_app, restrictedScalarComputation,
      scalarComputation_app, NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Category.assoc, Functor.id_obj, tensorRight] using h
  let EI := (ModuleRingedComparison.equivalence Λ T).mapHomologicalComplex (.up ℤ)
  let A := EI.inverse.obj P
  let j : E.obj A ≅ P := EI.counitIso.app P
  have hA : CochainComplex.IsKFlatIndependentCoefficients
      (R := ModuleRingedComparison.ring Λ T) (E.obj A) := by
    intro Z hZ n
    exact (hP Z hZ n).of_iso
      (((curriedTensor (ModuleRingedComparison.modules Λ T)).map₂CochainComplex.obj Z).mapIso
        j.symm)
  have hfA (n : ℤ) : SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
      (R := ModuleRingedComparison.ring Λ T)
      ((ModuleRingedComparison.equivalence Λ T).functor.obj (A.X n)) := by
    let i := (HomologicalComplex.eval _ (.up ℤ) n).mapIso j
    exact (exactFunctor _ _).prop_of_iso
      (SheafOfModules.siteSheafTensorRightIso (ModuleRingedComparison.ring Λ T) (P.X n) ≪≫
        (curriedTensor (ModuleRingedComparison.modules Λ T)).flip.mapIso i.symm ≪≫
          (SheafOfModules.siteSheafTensorRightIso (ModuleRingedComparison.ring Λ T)
            ((E.obj A).X n)).symm) (hflat n)
  have h := himage A hA hfA
  exact natTrans_eq_app_of_iso lhs rhs j h

end AlgebraicGeometry.ProEtale.QuotientChange
