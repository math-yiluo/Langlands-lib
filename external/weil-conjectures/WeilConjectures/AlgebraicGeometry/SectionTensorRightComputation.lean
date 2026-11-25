/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.InternalScalarPullbackNormalizationData
import WeilConjectures.Algebra.Homology.BifunctorSingleComparison
import WeilConjectures.AlgebraicGeometry.ModuleRingedToposDerivedComparison

/-! # Section localization of right tensor with a degree-zero coefficient

(auxiliary; not a blueprint node)
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory HomologicalComplex
open CategoryTheory.InternalAbelianSheafModule
open scoped CategoryTheory.Obj TensorProduct ChangeOfRings
attribute [local instance 20000] AlgebraicGeometry.ProEtale.sheafBraidedCategory
attribute [local instance 20000] CategoryTheory.Mod.monoidalCategory
  CategoryTheory.Mod.monoidalCategoryCochainComplex CategoryTheory.Mod.derivedMonoidalCategory
  AlgebraicGeometry.ProEtale.CondensedRing.laxMonoidal_Q

namespace AlgebraicGeometry.ProEtale.QuotientChange
variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
  [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (ModuleRingedComparison.modules Λ T)]
  [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (ModuleRingedComparison.modules Λ' T)]

attribute [local irreducible] upperStarFromPoint upperStarFromPointComp
  monoidal_upperStarFromPoint monoidal_pointUpperStar oplaxMonoidal_pointUpperStar
  CategoryTheory.Localization.Monoidal.tensorBifunctor

attribute [local irreducible] CategoryTheory.Functor.leftDerivedFunctor
  CategoryTheory.Functor.mapHomologicalComplexUpToQuasiIso
  CategoryTheory.Functor.mapHomologicalComplexUpToQuasiIsoFactors
  ModuleRingedComparison.tensor sectionModuleEquivalence
  HomologicalComplex₂.total CategoryTheory.Mod.monoidalClosed
  CochainComplex.mapBifunctorSingle₂Iso HomologicalComplex.singleMapHomologicalComplex
  ModuleRingedComparison.qTensor ModuleRingedComparison.tensorComparison
  Mod.inducingFunctorData SheafOfModules.monoidalCategory
  sectionScalarCoefficient sectionScalarRestriction
  DerivedCategory.monoidalClosed
  DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory

omit [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (ModuleRingedComparison.modules Λ T)] in
/-- Naturality of the specified ordinary section tensor comparison.
Source: the naturality clause of ordinary_monoidal, Stacks 03EK.
(auxiliary; not a blueprint node). -/
theorem section_tensor_comparison_naturality (T : Scheme.{u})
    (M M' N N' : Modules Λ T) (f : M ⟶ M') (g : N ⟶ N') :
    (ModuleRingedComparison.equivalence Λ T).functor.map (f ⊗ₘ g) ≫
        (ModuleRingedComparison.ordinaryTensorComparison Λ T M' N').hom =
      (ModuleRingedComparison.ordinaryTensorComparison Λ T M N).hom ≫
        ((ModuleRingedComparison.equivalence Λ T).functor.map f ⊗ₘ
          (ModuleRingedComparison.equivalence Λ T).functor.map g) :=
  (ModuleRingedComparison.ordinary_monoidal Λ T).1 M M' N N' f g

/-- The ordinary section tensor comparison with a fixed right coefficient.
Source: Stacks 03EK; fixed section equivalence tensor normalization.
(auxiliary; not a blueprint node). -/
def sectionTensorRightComparison (a : Λ ⟶ Λ') [IsMonHom a] (T : Scheme.{u}) :
    tensorRight (B₀ a T) ⋙ (ModuleRingedComparison.equivalence Λ T).functor ≅
      (ModuleRingedComparison.equivalence Λ T).functor ⋙
        tensorRight ((ModuleRingedComparison.equivalence Λ T).functor.obj (B₀ a T)) := by
  refine NatIso.ofComponents
    (fun M ↦ ModuleRingedComparison.ordinaryTensorComparison Λ T M (B₀ a T)) ?_
  intro M N f
  have h := section_tensor_comparison_naturality T
    M N (B₀ a T) (B₀ a T) f (𝟙 _)
  change (ModuleRingedComparison.equivalence Λ T).functor.map (f ⊗ₘ 𝟙 _) ≫ _ =
    _ ≫ ((ModuleRingedComparison.equivalence Λ T).functor.map f ⊗ₘ
      (ModuleRingedComparison.equivalence Λ T).functor.map (𝟙 _)) at h
  rw [CategoryTheory.Functor.map_id, tensorHom_id, tensorHom_id] at h
  exact h

/-- The fixed localization and ordinary right-tensor comparison.
Source: Stacks 06YN, 06YU; localization of the degreewise tensor comparison.
(auxiliary; not a blueprint node). -/
def sectionTensorRightLocalization (a : Λ ⟶ Λ') [IsMonHom a] (T : Scheme.{u})
    (P : CochainComplex (Modules Λ T) ℤ) :
    (ModuleRingedComparison.derivedEquivalence Λ T).functor.obj
      (DerivedCategory.Q.obj (((tensorRight (B₀ a T)).mapHomologicalComplex (.up ℤ)).obj P)) ≅
    DerivedCategory.Q.obj
      ((Functor.mapHomologicalComplex
        (tensorRight ((ModuleRingedComparison.equivalence Λ T).functor.obj (B₀ a T)))
        (.up ℤ)).obj
          (((ModuleRingedComparison.equivalence Λ T).functor.mapHomologicalComplex
            (.up ℤ)).obj P)) :=
  ModuleRingedComparison.sectionLocalizationComparison Λ T _ ≪≫
    DerivedCategory.Q.mapIso
      ((Functor.mapHomologicalComplexCompIso (sectionTensorRightComparison a T)
        (.up ℤ)).app P)

attribute [local irreducible] sectionTensorRightComparison sectionTensorRightLocalization
  ModuleRingedComparison.ordinaryTensorComparison ModuleRingedComparison.totalComparison
  ModuleRingedComparison.localizedTotalComparison

attribute [local implicit_reducible] singleTensor
  CategoryTheory.Functor.mapCochainComplexSingleFunctor
  ModuleRingedComparison.totalTensor
  CategoryTheory.Functor.map₂HomologicalComplex
  ModuleRingedComparison.sectionLocalizationComparison

private theorem mapIsoCancel
    {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D) {X Y : C}
    (i : X ≅ Y) {Z : D} {f : F.obj X ⟶ Z} {g : F.obj Y ⟶ Z}
    (h : F.map i.inv ≫ f = g) : f = F.map i.hom ≫ g := by
  rw [← h, ← F.map_comp_assoc, i.hom_inv_id, F.map_id, Category.id_comp]

private theorem singleSquareOfSummands
    {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
    [HasZeroObject C] [HasZeroObject D] [MonoidalCategory C] [MonoidalCategory D]
    [MonoidalPreadditive C] [MonoidalPreadditive D]
    (F : C ⥤ D) [F.Additive]
    (δ : ∀ M N : C, F.obj (M ⊗ N) ⟶ F.obj M ⊗ F.obj N)
    (hd : ∀ (M N N' : C) (g : N ⟶ N'),
      F.map (((curriedTensor C).obj M).map g) ≫ δ M N' =
        δ M N ≫ ((curriedTensor D).obj (F.obj M)).map (F.map g))
    (P : CochainComplex C ℤ) (X : C)
    (r : tensorRight X ⋙ F ≅ F ⋙ tensorRight (F.obj X))
    (hr : ∀ M : C, r.hom.app M = δ M X)
    (κ : (F.mapHomologicalComplex (.up ℤ)).obj
        (CochainComplex.mapBifunctor P ((single C (.up ℤ) 0).obj X)
          (curriedTensor C)) ⟶
      CochainComplex.mapBifunctor ((F.mapHomologicalComplex (.up ℤ)).obj P)
        ((F.mapHomologicalComplex (.up ℤ)).obj ((single C (.up ℤ) 0).obj X))
          (curriedTensor D))
    (hκ : ∀ (p q n : ℤ) (h : p + q = n),
      F.map (CochainComplex.ιMapBifunctor P ((single C (.up ℤ) 0).obj X)
          (curriedTensor C) p q n h) ≫ κ.f n =
        δ (P.X p) (((single C (.up ℤ) 0).obj X).X q) ≫
          CochainComplex.ιMapBifunctor ((F.mapHomologicalComplex (.up ℤ)).obj P)
            ((F.mapHomologicalComplex (.up ℤ)).obj
              ((single C (.up ℤ) 0).obj X)) (curriedTensor D) p q n h) :
    κ ≫ mapBifunctorMap (𝟙 _)
        ((singleMapHomologicalComplex F (.up ℤ) 0).hom.app X) (curriedTensor D) (.up ℤ) ≫
        (CochainComplex.mapBifunctorSingle₂Iso (curriedTensor D) (F.obj X)
          ((F.mapHomologicalComplex (.up ℤ)).obj P)).hom =
      (F.mapHomologicalComplex (.up ℤ)).map
          (CochainComplex.mapBifunctorSingle₂Iso (curriedTensor C) X P).hom ≫
        (Functor.mapHomologicalComplexCompIso r (.up ℤ)).hom.app P := by
  apply mapIsoCancel (F.mapHomologicalComplex (.up ℤ))
    (CochainComplex.mapBifunctorSingle₂Iso (curriedTensor C) X P)
  rw [← cancel_mono (CochainComplex.mapBifunctorSingle₂Iso (curriedTensor D) (F.obj X)
    ((F.mapHomologicalComplex (.up ℤ)).obj P)).inv]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  ext n : 1
  change F.map _ ≫ κ.f n ≫ _ = r.hom.app (P.X n) ≫ _
  rw [hr, CochainComplex.mapBifunctorSingle₂Iso_inv_f,
    CochainComplex.mapBifunctorSingle₂Iso_inv_f, F.map_comp, Category.assoc,
    reassoc_of% hκ n 0 n (by simp), ι_mapBifunctorMap,
    reassoc_of% hd (P.X n) X _ (singleObjXSelf (.up ℤ) 0 X).inv,
    HomologicalComplex.id_f, CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp,
    singleMapHomologicalComplex_hom_app_self]
  erw [← CategoryTheory.Functor.map_comp_assoc]
  rw [Iso.inv_hom_id_map_assoc]
  rfl

-- Only the single nonzero right degree is needed in the total comparison.
omit [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (ModuleRingedComparison.modules Λ T)]
  [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (ModuleRingedComparison.modules Λ' T)]
  [IsCommMonObj Λ'] in
private theorem sectionTensorRight_total (a : Λ ⟶ Λ') [IsMonHom a] (T : Scheme.{u})
    (P : CochainComplex (Modules Λ T) ℤ) :
    (ModuleRingedComparison.totalComparison Λ T P
        ((CochainComplex.singleFunctor _ 0).obj (B₀ a T))).hom ≫
      HomologicalComplex.mapBifunctorMap (𝟙 _)
        ((singleMapHomologicalComplex (ModuleRingedComparison.equivalence Λ T).functor
          (.up ℤ) 0).hom.app (B₀ a T))
        (curriedTensor (ModuleRingedComparison.modules Λ T)) (.up ℤ) ≫
      (CochainComplex.mapBifunctorSingle₂Iso
        (curriedTensor (ModuleRingedComparison.modules Λ T))
        ((ModuleRingedComparison.equivalence Λ T).functor.obj (B₀ a T))
        (((ModuleRingedComparison.equivalence Λ T).functor.mapHomologicalComplex
          (.up ℤ)).obj P)).hom =
      ((ModuleRingedComparison.equivalence Λ T).functor.mapHomologicalComplex (.up ℤ)).map
          (singleTensor a T P).hom ≫
        (Functor.mapHomologicalComplexCompIso (sectionTensorRightComparison a T)
          (.up ℤ)).hom.app P := by
  refine singleSquareOfSummands (ModuleRingedComparison.equivalence Λ T).functor
    (fun M N ↦ (ModuleRingedComparison.ordinaryTensorComparison Λ T M N).hom)
    ?_ P (B₀ a T) (sectionTensorRightComparison a T) ?_
    (ModuleRingedComparison.totalComparison Λ T P
      ((CochainComplex.singleFunctor _ 0).obj (B₀ a T))).hom ?_
  · intro M N N' g
    have h := section_tensor_comparison_naturality T M M N N' (𝟙 M) g
    rw [CategoryTheory.Functor.map_id, id_tensorHom, id_tensorHom] at h
    simpa only [curriedTensor_obj_map] using h
  · intro M
    unfold sectionTensorRightComparison
    rfl
  · unfold ModuleRingedComparison.totalComparison
    exact (ModuleRingedComparison.totalComparison_existsUnique Λ T P
      ((CochainComplex.singleFunctor _ 0).obj (B₀ a T))).exists.choose_spec

private theorem mapThree_eq
    {C D : Type*} [Category* C] [Category* D] (Q : C ⥤ D)
    {A B C' D' E : C} (f : A ⟶ B) (g : B ⟶ C') (h : C' ⟶ D')
    (i : A ⟶ E) (j : E ⟶ D') (H : f ≫ g ≫ h = i ≫ j) :
    Q.map f ≫ Q.map g ≫ Q.map h = Q.map i ≫ Q.map j := by
  rw [← Q.map_comp, ← Q.map_comp, H, Q.map_comp]

private theorem isoCancelPair
    {C : Type*} [Category* C] {A B D E : C} (θ : A ≅ B) (γ : B ≅ D)
    {q : D ⟶ E} {f : A ⟶ E} (h : q = γ.inv ≫ θ.inv ≫ f) :
    θ.hom ≫ γ.hom ≫ q = f := by
  rw [h, γ.hom_inv_id_assoc, θ.hom_inv_id_assoc]

private theorem mapRightComp
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    (T : C × D ⥤ E) {X X' : C} {Y Y' Y'' : D}
    (a : X ⟶ X') (b : Y ⟶ Y') (c : Y' ⟶ Y'') :
    T.map (Prod.mkHom a (b ≫ c)) =
      T.map (Prod.mkHom a b) ≫ T.map (Prod.mkHom (𝟙 X') c) := by
  rw [← T.map_comp]
  simp only [prod_comp, Category.comp_id]

private theorem computationPaste
    {C : Type*} [Category* C] {A B D E F G H I J K L : C}
    (θ : A ⟶ B) (a : B ⟶ D) (b : D ⟶ E) (c : B ⟶ E)
    (q₀ : D ⟶ F) (q₁ : E ⟶ G) (m : F ⟶ G) (z : G ⟶ H)
    (f : A ⟶ I) (loc : I ⟶ F) (α : I ⟶ J) (τ : J ⟶ F)
    (g : I ⟶ K) (α' : K ⟶ L) (v : J ⟶ L) (k : L ⟶ H)
    (hc : c = a ≫ b) (hn : b ≫ q₁ = q₀ ≫ m)
    (hr : θ ≫ a ≫ q₀ = f ≫ loc) (hl : loc = α ≫ τ)
    (ho : τ ≫ m ≫ z = v ≫ k) (hα : g ≫ α' = α ≫ v) :
    θ ≫ c ≫ q₁ ≫ z = f ≫ g ≫ α' ≫ k := by
  rw [hc, Category.assoc, reassoc_of% hn, reassoc_of% hr, hl]
  simp only [Category.assoc]
  rw [ho, ← reassoc_of% hα]

private theorem computationPasteMapped
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    (F : C ⥤ D) (Q : E ⥤ D) {X₀ X₁ X₂ : C} {L₀ H₀ : E}
    {B D' E' F' G J : D}
    {θ : F.obj X₀ ⟶ B} {a : B ⟶ D'} {b : D' ⟶ E'} {c : B ⟶ E'}
    {q₀ : D' ⟶ F'} {q₁ : E' ⟶ G} {m : F' ⟶ G} {z : G ⟶ Q.obj H₀}
    {f : X₀ ⟶ X₁} {loc : F.obj X₁ ⟶ F'} {α : F.obj X₁ ⟶ J} {τ : J ⟶ F'}
    {g : X₁ ⟶ X₂} (α' : F.obj X₂ ≅ Q.obj L₀) {v : J ⟶ Q.obj L₀} (k : L₀ ≅ H₀)
    (hc : c = a ≫ b) (hn : b ≫ q₁ = q₀ ≫ m)
    (hr : θ ≫ a ≫ q₀ = F.map f ≫ loc) (hl : loc = α ≫ τ)
    (ho : τ ≫ m ≫ z = v ≫ Q.map k.hom) (hα : F.map g ≫ α'.hom = α ≫ v) :
    θ ≫ c ≫ q₁ ≫ z = F.map (f ≫ g) ≫ (α' ≪≫ Q.mapIso k).hom := by
  simp only [F.map_comp, Iso.trans_hom, CategoryTheory.Functor.mapIso_hom, Category.assoc]
  exact computationPaste θ a b c q₀ q₁ m z (F.map f) loc α τ (F.map g) α'.hom v
    (Q.map k.hom) hc hn hr hl ho hα

-- The section equivalence requires substantial tensor and colimit typeclass elaboration.
omit [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (ModuleRingedComparison.modules Λ' T)]
  [IsCommMonObj Λ'] in
/-- The tensor localization comparison commutes with putting the right coefficient
in degree zero. Source: Stacks 06YN and 06YU; representative clause of
lem-pd-section-derived-tensor-normalization.
(auxiliary; not a blueprint node).

Proof: apply the representative equation for qTensor to P and the degree-zero
complex of B₀. Naturality moves the canonical map-complex/single comparison
through qTensor. Cancel the two section localization isomorphisms. The remaining
ordinary square compares the total tensor with a single factor to degreewise
right tensor. Precompose in each degree with each direct-sum summand injection.
All summands outside right degree zero vanish; in degree zero both maps are
exactly the ordinary tensor comparison. The coproduct universal property proves
the square. Localize it and combine the two localization factors. This argument
works for all unbounded complexes, with no flatness assumption. -/
theorem section_tensor_right_computation (a : Λ ⟶ Λ') [IsMonHom a] (T : Scheme.{u})
    (P : CochainComplex (Modules Λ T) ℤ) :
    (ModuleRingedComparison.tensorComparison Λ T).hom.app (DerivedCategory.Q.obj P, B a T) ≫
        (ModuleRingedComparison.tensor Λ T).map
          (Prod.mkHom (ModuleRingedComparison.sectionLocalizationComparison Λ T P).hom
            (sectionScalarCoefficient a T).hom) ≫
        (ModuleRingedComparison.qTensor Λ T).app
          ((((ModuleRingedComparison.equivalence Λ T).functor.mapHomologicalComplex
            (.up ℤ)).obj P),
            (CochainComplex.singleFunctor _ 0).obj
              ((ModuleRingedComparison.equivalence Λ T).functor.obj (B₀ a T))) ≫
        DerivedCategory.Q.map (CochainComplex.mapBifunctorSingle₂Iso
          (curriedTensor (ModuleRingedComparison.modules Λ T))
          ((ModuleRingedComparison.equivalence Λ T).functor.obj (B₀ a T))
          (((ModuleRingedComparison.equivalence Λ T).functor.mapHomologicalComplex
            (.up ℤ)).obj P)).hom =
      (ModuleRingedComparison.derivedEquivalence Λ T).functor.map
        (Functor.LaxMonoidal.μ (DerivedCategory.Q (C := Modules Λ T)) P
          ((CochainComplex.singleFunctor _ 0).obj (B₀ a T)) ≫
            DerivedCategory.Q.map (singleTensor a T P).hom) ≫
        (sectionTensorRightLocalization a T P).hom := by
  let E := (ModuleRingedComparison.equivalence Λ T).functor
  let F := (ModuleRingedComparison.derivedEquivalence Λ T).functor
  let S := (CochainComplex.singleFunctor (Modules Λ T) 0).obj (B₀ a T)
  let α := ModuleRingedComparison.sectionLocalizationComparison Λ T P
  let β := ModuleRingedComparison.sectionLocalizationComparison Λ T S
  let σ := (E.mapCochainComplexSingleFunctor 0).app (B₀ a T)
  let EP := (E.mapHomologicalComplex (.up ℤ)).obj P
  let ES := (E.mapHomologicalComplex (.up ℤ)).obj S
  let K := (CochainComplex.singleFunctor (ModuleRingedComparison.modules Λ T) 0).obj
    (E.obj (B₀ a T))
  have hq : (ModuleRingedComparison.qTensor Λ T).app (EP, ES) =
      (ModuleRingedComparison.tensor Λ T).map (Prod.mkHom α.inv β.inv) ≫
        (ModuleRingedComparison.tensorComparison Λ T).inv.app
          (DerivedCategory.Q.obj P, DerivedCategory.Q.obj S) ≫
        F.map (Functor.LaxMonoidal.μ DerivedCategory.Q P S) ≫
        ModuleRingedComparison.localizedTotalComparison Λ T P S := by
    unfold ModuleRingedComparison.qTensor
    simpa only [ModuleRingedComparison.internalLocalizationTensorMap_app] using
      (ModuleRingedComparison.tensor_representatives Λ T).exists.choose_spec.1 P S
  have hrep := isoCancelPair
    ((ModuleRingedComparison.tensorComparison Λ T).app
      (DerivedCategory.Q.obj P, DerivedCategory.Q.obj S))
    ((ModuleRingedComparison.tensor Λ T).mapIso (Iso.prod α β)) hq
  have hcoeff : (ModuleRingedComparison.tensor Λ T).map
      (Prod.mkHom α.hom (sectionScalarCoefficient a T).hom) =
      (ModuleRingedComparison.tensor Λ T).map (Prod.mkHom α.hom β.hom) ≫
        (ModuleRingedComparison.tensor Λ T).map
          (Prod.mkHom (𝟙 _) (DerivedCategory.Q.map σ.hom)) := by
    unfold sectionScalarCoefficient
    exact mapRightComp (ModuleRingedComparison.tensor Λ T) α.hom β.hom
      (DerivedCategory.Q.map σ.hom)
  have hn := (ModuleRingedComparison.qTensor Λ T).naturality
    (Prod.mkHom (𝟙 EP) σ.hom)
  dsimp only [Functor.comp_map, Functor.prod_map, ModuleRingedComparison.totalTensor,
    ModuleRingedComparison.cochainTotalFunctor, Functor.uncurry_obj_map,
    Functor.map₂HomologicalComplex_obj_map] at hn
  simp only [CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp,
    Functor.map₂HomologicalComplex_obj_map] at hn
  have hord := sectionTensorRight_total a T P
  have hordQ := mapThree_eq DerivedCategory.Q _ _ _ _ _ hord
  have hl : ModuleRingedComparison.localizedTotalComparison Λ T P S =
      (ModuleRingedComparison.sectionLocalizationComparison Λ T _).hom ≫
        DerivedCategory.Q.map (ModuleRingedComparison.totalComparison Λ T P S).hom := by
    unfold ModuleRingedComparison.localizedTotalComparison
    simp only [ModuleRingedComparison.sectionTotalComparison_eq,
      ModuleRingedComparison.internalTotalTensor, ModuleRingedComparison.cochainTotalFunctor]
  have hloc := E.mapDerivedCategoryFactors.hom.naturality (singleTensor a T P).hom
  unfold sectionTensorRightLocalization
  have hcomputed := computationPasteMapped F DerivedCategory.Q
    (ModuleRingedComparison.sectionLocalizationComparison Λ T _)
    ((Functor.mapHomologicalComplexCompIso
      (sectionTensorRightComparison a T) (.up ℤ)).app P)
    hcoeff hn hrep hl hordQ hloc
  -- Check the inferred proof directly, as in ordinary_monoidal: repeated elaborator
  -- conversion otherwise expands the same sheaf and derived tensor instances.
  run_tac Lean.Elab.Tactic.withMainContext do
    let some hd := (← Lean.getLCtx).findFromUserName? `hcomputed
      | Lean.throwError "missing tensor computation proof"
    (← Lean.Elab.Tactic.getMainGoal).assign hd.toExpr
    Lean.Elab.Tactic.replaceMainGoal []

end AlgebraicGeometry.ProEtale.QuotientChange
