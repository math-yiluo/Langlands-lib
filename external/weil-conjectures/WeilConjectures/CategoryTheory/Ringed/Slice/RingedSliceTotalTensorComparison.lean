/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Ringed.Slice.RingedSliceEvaluationModels
import WeilConjectures.Mathlib.Algebra.Homology.Bifunctor
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import all WeilConjectures.Algebra.Homology.SixFunctors.LocalizedSiteTensorRestrictionSupplement
import all WeilConjectures.Algebra.Homology.ScalarHomOrdinary.ScalarHomOrdinaryTensorComparisonSupplement
import WeilConjectures.CategoryTheory.LocalizedModuleExactForSystems
import WeilConjectures.Algebra.Homology.SmoothPurity.LocalizedModuleExactIndependent
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor

/-! # Slice restriction of the total tensor complex

Source: Stacks Project, Tags 03EL, 06YN and 07A4.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false

universe c v u a b x y

open CategoryTheory CategoryTheory.Limits Opposite WeilConjectures MonoidalCategory

namespace CategoryTheory

attribute [local irreducible] SheafOfModules.monoidalCategory
  SheafOfModules.tensorObjIsoSheafification

attribute [local instance 20000] siteAbelianHasSheafify siteAbelianWEqualsLocallyBijective

variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max c v u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v u}]
  (A : Sheaf J CommRingCat.{max c v u})

private abbrev ModuleSheaf := SheafOfModules.{max c v u} ((sheafCompose J
  (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj A)

private abbrev nativeModules :=
  let := SheafOfModules.isMonoidal_W_independentCoefficients A
  SheafOfModules.monoidalCategory A

private def nativeTensorι (P Q : CochainComplex (ModuleSheaf.{c, v, u} J A) ℤ)
    (p q n : ℤ) (h : p + q = n) :
    let := nativeModules.{c, v, u} J A
    P.X p ⊗ Q.X q ⟶ ((coefficientTotalTensor.{u, c, v} J A).obj (P, Q)).X n := by
  let := nativeModules.{c, v, u} J A
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients A
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients A
  exact HomologicalComplex.ιMapBifunctor P Q (curriedTensor _) (.up ℤ) p q n h

private theorem tensorHasMapBifunctor
    {D : Type a} [Category.{x} D] [Preadditive D] [MonoidalCategory D]
    [MonoidalPreadditive D] [HasCoproducts.{0} D]
    (P Q : CochainComplex D ℤ) :
    HomologicalComplex.HasMapBifunctor P Q (curriedTensor D) (.up ℤ) := by
  infer_instance

attribute [local instance 20000] tensorHasMapBifunctor

section GenericTotal
variable {D : Type a} [Category.{x} D] [Preadditive D] [MonoidalCategory D]
  {E : Type b} [Category.{y} E] [Preadditive E] [MonoidalCategory E]
  [MonoidalPreadditive D] [MonoidalPreadditive E]
  [HasCoproducts.{0} D] [HasCoproducts.{0} E]
  (L : D ⥤ E) [L.Additive] [PreservesColimitsOfSize.{0, 0} L]
  (e : ∀ X Y : D, L.obj (X ⊗ Y) ≅ L.obj X ⊗ L.obj Y)
  (he : ∀ {X X' Y Y' : D} (f : X ⟶ X') (g : Y ⟶ Y'),
    L.map (f ⊗ₘ g) ≫ (e X' Y').hom = (e X Y).hom ≫ (L.map f ⊗ₘ L.map g))

private theorem tensorMap_factor
    {P P' Q Q' : CochainComplex D ℤ} (f : P ⟶ P') (g : Q ⟶ Q') :
    HomologicalComplex.mapBifunctorMap f (𝟙 Q) (curriedTensor D) (.up ℤ) ≫
      HomologicalComplex.mapBifunctorMap (𝟙 P') g (curriedTensor D) (.up ℤ) =
      HomologicalComplex.mapBifunctorMap f g (curriedTensor D) (.up ℤ) := by
  simp [HomologicalComplex.mapBifunctorMap, ← HomologicalComplex₂.total.map_comp]

include he in
private def tensorRestrictionNatTrans : (Functor.postcompose₂.obj L).obj (curriedTensor D) ⟶
    (((Functor.whiskeringLeft₂ E).obj L).obj L).obj (curriedTensor E) :=
  { app := fun X ↦
      { app := fun Y ↦ (e X Y).hom
        naturality := by
          intro Y Y' g
          change L.map (X ◁ g) ≫ (e X Y').hom =
            (e X Y).hom ≫ (L.obj X ◁ L.map g)
          simpa only [id_tensorHom, L.map_id] using he (𝟙 X) g }
    naturality := by
      intro X X' f
      ext Y
      change L.map (f ▷ Y) ≫ (e X' Y).hom =
        (e X Y).hom ≫ (L.map f ▷ L.obj Y)
      simpa only [tensorHom_id, L.map_id] using he f (𝟙 Y) }

include he in
omit [Preadditive D] [Preadditive E] [MonoidalPreadditive D] [MonoidalPreadditive E]
  [HasCoproducts.{0} D] [HasCoproducts.{0} E]
  [L.Additive] [PreservesColimitsOfSize.{0, 0} L] in
private theorem tensorRestrictionNatTrans_isIso (X Y : D) :
    IsIso (((tensorRestrictionNatTrans L e he).app X).app Y) :=
  (e X Y).isIso_hom

include he in
private theorem tensorTotalRestriction :
    ∃ γ : Functor.uncurry.obj ((curriedTensor D).map₂HomologicalComplex
        (.up ℤ) (.up ℤ) (.up ℤ)) ⋙ L.mapHomologicalComplex (.up ℤ) ≅
      ((L.mapHomologicalComplex (.up ℤ)).prod (L.mapHomologicalComplex (.up ℤ))) ⋙
        Functor.uncurry.obj ((curriedTensor E).map₂HomologicalComplex
          (.up ℤ) (.up ℤ) (.up ℤ)),
      ∀ (P Q : CochainComplex D ℤ) (p q n : ℤ) (h : p + q = n),
        L.map (CochainComplex.ιMapBifunctor P Q (curriedTensor D) p q n h) ≫
            (γ.hom.app (P, Q)).f n =
          (e (P.X p) (Q.X q)).hom ≫
            CochainComplex.ιMapBifunctor
              ((L.mapHomologicalComplex (.up ℤ)).obj P)
              ((L.mapHomologicalComplex (.up ℤ)).obj Q) (curriedTensor E) p q n h := by
  let τ := tensorRestrictionNatTrans L e he
  let (X Y : D) : IsIso ((τ.app X).app Y) :=
    tensorRestrictionNatTrans_isIso L e he X Y
  have hIso (P Q : CochainComplex D ℤ) :
      IsIso (HomologicalComplex.mapBifunctorComparison
        (c₁ := .up ℤ) (c₂ := .up ℤ) τ (.up ℤ) P Q) := by
    apply HomologicalComplex.instIsIsoMapBifunctorComparisonOfAppFunctor
  let γ : Functor.uncurry.obj ((curriedTensor D).map₂HomologicalComplex
        (.up ℤ) (.up ℤ) (.up ℤ)) ⋙ L.mapHomologicalComplex (.up ℤ) ≅
      ((L.mapHomologicalComplex (.up ℤ)).prod (L.mapHomologicalComplex (.up ℤ))) ⋙
        Functor.uncurry.obj ((curriedTensor E).map₂HomologicalComplex
          (.up ℤ) (.up ℤ) (.up ℤ)) :=
    NatIso.ofComponents
      (fun Z ↦ @asIso _ _ _ _
        (HomologicalComplex.mapBifunctorComparison
          (c₁ := .up ℤ) (c₂ := .up ℤ) τ (.up ℤ) Z.1 Z.2) (hIso Z.1 Z.2)) (by
        intro Z Z' f
        simp only [Functor.comp_map, Functor.prod_map, Functor.uncurry_obj_map,
          Functor.map₂HomologicalComplex, asIso_hom, tensorMap_factor]
        exact HomologicalComplex.mapBifunctorComparison_naturality
          (c₁ := .up ℤ) (c₂ := .up ℤ) τ (.up ℤ) f.1 f.2)
  refine ⟨γ, ?_⟩
  intro P Q p q n h
  dsimp only [Functor.comp_obj, Functor.prod_obj, Functor.uncurry_obj_obj,
    Functor.map₂HomologicalComplex]
  dsimp only [γ, NatIso.ofComponents_hom_app, asIso_hom,
    HomologicalComplex.mapBifunctorComparison_f, CochainComplex.ιMapBifunctor]
  -- The inferred cochain shapes use definitionally equal integer addition instances.
  convert HomologicalComplex.map_ιMapBifunctor_mapBifunctorComparisonX
    (c₁ := .up ℤ) (c₂ := .up ℤ) τ (.up ℤ) P Q p q n h using 1
  rfl

end GenericTotal

section NativeTensorRestriction
variable (U : C)

private def tensorOverMap (F G : ModuleSheaf.{c, v, u} J A) :
    let := nativeModules.{c, v, u} J A
    let : MonoidalCategory (SheafOfModules.{max c v u} (((sheafCompose J
      (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj A).over U)) :=
      nativeModules.{max c v, v, u} (J.over U) (A.over U)
    F.over U ⊗ G.over U ⟶ (F ⊗ G).over U := by
  let := nativeModules.{c, v, u} J A
  let : MonoidalCategory (SheafOfModules.{max c v u} (((sheafCompose J
    (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj A).over U)) :=
      nativeModules.{max c v, v, u} (J.over U) (A.over U)
  exact
    (SheafOfModules.ScalarHomOrdinary.tensorIsoSite (A.over U)
      (F.over U) (G.over U)).hom ≫
    SheafOfModules.tensorOverComparison (A := A) U F G ≫
    ((SheafOfModules.ScalarHomOrdinary.tensorIsoSite A F G).inv).over U

private theorem tensorOverMap_isIso (F G : ModuleSheaf.{c, v, u} J A) :
    IsIso (tensorOverMap.{c, v, u} J A U F G) := by
  let := nativeModules.{c, v, u} J A
  let : MonoidalCategory (SheafOfModules.{max c v u} (((sheafCompose J
    (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj A).over U)) :=
      nativeModules.{max c v, v, u} (J.over U) (A.over U)
  have h := SheafOfModules.tensorOverComparison_isIso (A := A) U F G
  let V : ModuleSheaf.{c, v, u} J A ⥤
      ModuleSheaf.{max c v, v, u} (J.over U) (A.over U) :=
    SheafOfModules.overFunctor
      ((sheafCompose J
        (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj A) U
  have hV : IsIso (V.map (SheafOfModules.ScalarHomOrdinary.tensorIsoSite A F G).inv) :=
    V.map_isIso _
  exact IsIso.comp_isIso'
    (SheafOfModules.ScalarHomOrdinary.tensorIsoSite (A.over U)
      (F.over U) (G.over U)).isIso_hom (IsIso.comp_isIso' h hV)

private def tensorOverIso (F G : ModuleSheaf.{c, v, u} J A) :
    let := nativeModules.{c, v, u} J A
    let : MonoidalCategory (SheafOfModules.{max c v u} (((sheafCompose J
      (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj A).over U)) :=
      nativeModules.{max c v, v, u} (J.over U) (A.over U)
    (F ⊗ G).over U ≅ F.over U ⊗ G.over U := by
  let := nativeModules.{c, v, u} J A
  let : MonoidalCategory (SheafOfModules.{max c v u} (((sheafCompose J
    (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj A).over U)) :=
      nativeModules.{max c v, v, u} (J.over U) (A.over U)
  have := tensorOverMap_isIso.{c, v, u} J A U F G
  exact (asIso (tensorOverMap.{c, v, u} J A U F G)).symm

private def tensorPure (F G : ModuleSheaf.{c, v, u} J A) (X : Cᵒᵖ)
    (x : F.val.obj X) (y : G.val.obj X) :
    let := nativeModules.{c, v, u} J A
    (F ⊗ G).val.obj X := by
  let := nativeModules.{c, v, u} J A
  exact SheafOfModules.ScalarHomOrdinary.pure A F G X x y

private theorem tensorOverMap_pure (F G : ModuleSheaf.{c, v, u} J A)
    (X : Over U) (x : F.val.obj (op X.left)) (y : G.val.obj (op X.left)) :
    (tensorOverMap.{c, v, u} J A U F G).val.app (op X)
        (tensorPure.{max c v, v, u} (J.over U) (A.over U) (F.over U) (G.over U) (op X) x y) =
      tensorPure.{c, v, u} J A F G (op X.left) x y := by
  have h₁ := SheafOfModules.ScalarHomOrdinary.tensorIsoSite_pure
    (A.over U) (F.over U) (G.over U) (op X) x y
  have h₂ := SheafOfModules.tensorOverComparison_pure (A := A) U F G X x y
  have h₃ := SheafOfModules.ScalarHomOrdinary.tensorIsoSite_inv_pure
    A F G (op X.left) x y
  exact (congrArg (fun z ↦
    (SheafOfModules.ScalarHomOrdinary.tensorIsoSite A F G).inv.val.app (op X.left)
      ((SheafOfModules.tensorOverComparison (A := A) U F G).val.app (op X) z)) h₁).trans
    ((congrArg ((SheafOfModules.ScalarHomOrdinary.tensorIsoSite A F G).inv.val.app
      (op X.left)) h₂).trans h₃)

private theorem tensorOverMap_naturality
    {F F' G G' : ModuleSheaf.{c, v, u} J A} (f : F ⟶ F') (g : G ⟶ G') :
    let := nativeModules.{c, v, u} J A
    let : MonoidalCategory (SheafOfModules.{max c v u} (((sheafCompose J
      (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj A).over U)) :=
      nativeModules.{max c v, v, u} (J.over U) (A.over U)
    (f.over U ⊗ₘ g.over U) ≫ tensorOverMap.{c, v, u} J A U F' G' =
      tensorOverMap.{c, v, u} J A U F G ≫ (f ⊗ₘ g).over U := by
  let := nativeModules.{c, v, u} J A
  let : MonoidalCategory (SheafOfModules.{max c v u} (((sheafCompose J
    (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj A).over U)) :=
      nativeModules.{max c v, v, u} (J.over U) (A.over U)
  apply SheafOfModules.ScalarHomOrdinary.pure_hom_ext (A.over U)
    (F.over U) (G.over U) ((F' ⊗ G').over U)
  intro X x y
  have h₁ := SheafOfModules.ScalarHomOrdinary.pure_map (A.over U)
    (f.over U) (g.over U) X x y
  have h₂ := tensorOverMap_pure.{c, v, u} J A U F' G' X.unop
    (f.val.app (op X.unop.left) x) (g.val.app (op X.unop.left) y)
  have h₃ := tensorOverMap_pure.{c, v, u} J A U F G X.unop x y
  have h₄ := SheafOfModules.ScalarHomOrdinary.pure_map A f g (op X.unop.left) x y
  exact (congrArg ((tensorOverMap.{c, v, u} J A U F' G').val.app X) h₁).trans
    (h₂.trans (h₄.symm.trans (congrArg ((f ⊗ₘ g).val.app (op X.unop.left)) h₃.symm)))

private theorem naturality_inv {D : Type*} [Category D] {A B A' B' : D}
    (i : A ≅ B) (j : A' ≅ B') {f : A ⟶ A'} {g : B ⟶ B'}
    (h : f ≫ j.hom = i.hom ≫ g) : g ≫ j.inv = i.inv ≫ f := by
  rw [Iso.eq_inv_comp, ← Category.assoc, ← h, Category.assoc,
    Iso.hom_inv_id, Category.comp_id]

private theorem tensorOverIso_naturality
    {F F' G G' : ModuleSheaf.{c, v, u} J A} (f : F ⟶ F') (g : G ⟶ G') :
    let := nativeModules.{c, v, u} J A
    let : MonoidalCategory (SheafOfModules.{max c v u} (((sheafCompose J
      (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj A).over U)) :=
      nativeModules.{max c v, v, u} (J.over U) (A.over U)
    (f ⊗ₘ g).over U ≫ (tensorOverIso.{c, v, u} J A U F' G').hom =
      (tensorOverIso.{c, v, u} J A U F G).hom ≫ (f.over U ⊗ₘ g.over U) := by
  have := tensorOverMap_isIso.{c, v, u} J A U F G
  have := tensorOverMap_isIso.{c, v, u} J A U F' G'
  exact naturality_inv
    (asIso (tensorOverMap.{c, v, u} J A U F G))
    (asIso (tensorOverMap.{c, v, u} J A U F' G'))
    (tensorOverMap_naturality.{c, v, u} J A U f g)

private theorem tensorOverIso_pure (F G : ModuleSheaf.{c, v, u} J A)
    (X : Over U) (x : F.val.obj (op X.left)) (y : G.val.obj (op X.left)) :
    (tensorOverIso.{c, v, u} J A U F G).hom.val.app (op X)
        (tensorPure.{c, v, u} J A F G (op X.left) x y) =
      tensorPure.{max c v, v, u} (J.over U) (A.over U) (F.over U) (G.over U) (op X) x y := by
  let e := tensorOverIso.{c, v, u} J A U F G
  have h := tensorOverMap_pure.{c, v, u} J A U F G X x y
  have h' := congrArg (fun z ↦ e.hom.val.app (op X) z) h
  have hi := congrArg (fun f ↦ f.val.app (op X)
    (tensorPure.{max c v, v, u} (J.over U) (A.over U) (F.over U) (G.over U) (op X) x y))
    e.inv_hom_id
  exact h'.symm.trans hi

universe z t
private theorem slice_pushforward_colimits
    {C : Type a} [Category.{x} C] {D : Type b} [Category.{y} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    [HasSheafify J AddCommGrpCat.{z}] [J.WEqualsLocallyBijective AddCommGrpCat.{z}]
    [HasSheafify K AddCommGrpCat.{z}] [K.WEqualsLocallyBijective AddCommGrpCat.{z}]
    {G : C ⥤ D} [G.IsContinuous J K] [G.IsCocontinuous J K]
    [∀ (F : Cᵒᵖ ⥤ AddCommGrpCat.{z}), G.op.HasPointwiseRightKanExtension F]
    {S : Sheaf J RingCat.{t}} {R : Sheaf K RingCat.{t}}
    (φ : S ⟶ (G.sheafPushforwardContinuous RingCat.{t} J K).obj R) :
    PreservesColimitsOfSize.{z, z} (SheafOfModules.pushforward.{z} φ) := by
  let H := G.sheafPushforwardContinuous AddCommGrpCat.{z} J K
  have : PreservesColimitsOfSize.{z, z} H :=
    (G.sheafAdjunctionCocontinuous AddCommGrpCat.{z} J K).leftAdjoint_preservesColimits
  have : PreservesColimitsOfSize.{z, z} (SheafOfModules.toSheaf.{z} R) :=
    ⟨fun {I} _ ↦ ((moduleSheaves_colimits_forgetful R).2.2.2.2.2 I).2.1⟩
  let T := SheafOfModules.toSheaf.{z} S
  have : PreservesColimitsOfSize.{z, z} (SheafOfModules.pushforward.{z} φ ⋙ T) := by
    change PreservesColimitsOfSize.{z, z} (SheafOfModules.toSheaf.{z} R ⋙ H)
    infer_instance
  have : ReflectsColimitsOfSize.{z, z} T :=
    ⟨fun {_} _ ↦ reflectsColimitsOfShape_of_reflectsIsomorphisms⟩
  exact preservesColimits_of_reflects_of_preserves (SheafOfModules.pushforward.{z} φ) T

-- Infer the native specialization once, before its representative equation is used.
set_option linter.defProp false in
private def nativeTensorRestrictionComparison := by
  let := nativeModules.{c, v, u} J A
  let : MonoidalCategory (SheafOfModules.{max c v u} (((sheafCompose J
    (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj A).over U)) :=
      nativeModules.{max c v, v, u} (J.over U) (A.over U)
  let V : ModuleSheaf.{c, v, u} J A ⥤
      ModuleSheaf.{max c v, v, u} (J.over U) (A.over U) :=
    SheafOfModules.localizedSystemRestriction.{c, v, u} A U
  let : V.Additive := (ringedOverFunctor_exactGeneral.{c, v, max c v u, max c v u}
    ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj A) U).1
  have : PreservesColimitsOfSize.{max c v u, max c v u} V :=
    slice_pushforward_colimits (𝟙 _)
  have : PreservesColimitsOfSize.{0, 0} V := preservesSmallestColimits_of_preservesColimits V
  let : MonoidalPreadditive (ModuleSheaf.{c, v, u} J A) :=
    SheafOfModules.cochainModulesPreadditive A
  let : MonoidalPreadditive (ModuleSheaf.{max c v, v, u} (J.over U) (A.over U)) :=
    SheafOfModules.cochainModulesPreadditive (A.over U)
  exact (tensorTotalRestriction V
      (tensorOverIso.{c, v, u} J A U)
      (by
        intro M M' N N' f g
        exact tensorOverIso_naturality.{c, v, u} J A U f g))

private theorem nativeTensorGenerator_eq
    (P Q : CochainComplex (ModuleSheaf.{c, v, u} J A) ℤ)
    (p q n : ℤ) (h : p + q = n) (X : Cᵒᵖ)
    (x : (P.X p).val.obj X) (y : (Q.X q).val.obj X) :
    coefficientTensorGenerator.{u, c, v} J A P Q p q n h X x y =
      (nativeTensorι.{c, v, u} J A P Q p q n h).val.app X
        (tensorPure.{c, v, u} J A (P.X p) (Q.X q) X x y) := rfl

private theorem tensorComplexOverComparison (U : C) :
    ∃ γ : coefficientTotalTensor.{u, c, v} J A ⋙
        ringedSliceComplexRestriction.{c, v, u} J A U ≅
      ((ringedSliceComplexRestriction.{c, v, u} J A U).prod
        (ringedSliceComplexRestriction.{c, v, u} J A U)) ⋙
          coefficientTotalTensor.{u, max c v, v} (J.over U) (A.over U),
      ∀ (P Q : CochainComplex (ModuleSheaf.{c, v, u} J A) ℤ)
        (p q k : ℤ) (h : p + q = k) (X : Over U)
        (x : (P.X p).val.obj (op X.left)) (y : (Q.X q).val.obj (op X.left)),
        ((γ.app (P, Q)).hom.f k).val.app (op X)
          (coefficientTensorGenerator.{u, c, v} J A P Q p q k h (op X.left) x y) =
        coefficientTensorGenerator.{u, max c v, v} (J.over U) (A.over U)
          ((ringedSliceComplexRestriction.{c, v, u} J A U).obj P)
          ((ringedSliceComplexRestriction.{c, v, u} J A U).obj Q) p q k h (op X) x y := by
  obtain ⟨γ, hγ⟩ := nativeTensorRestrictionComparison.{c, v, u} J A U
  refine ⟨γ, ?_⟩
  intro P Q p q n h X x y
  have hi := hγ P Q p q n h
  have ht := congrArg (fun f ↦ f.val.app (op X)
    (tensorPure.{c, v, u} J A (P.X p) (Q.X q) (op X.left) x y)) hi
  have hp := tensorOverIso_pure.{c, v, u} J A U (P.X p) (Q.X q) X x y
  have hh := ht.trans (congrArg (fun z ↦
    (nativeTensorι.{max c v, v, u} (J.over U) (A.over U)
      ((ringedSliceComplexRestriction.{c, v, u} J A U).obj P)
      ((ringedSliceComplexRestriction.{c, v, u} J A U).obj Q) p q n h).val.app (op X) z) hp)
  rw [nativeTensorGenerator_eq, nativeTensorGenerator_eq]
  exact hh

end NativeTensorRestriction

/-- Ordinary slice restriction commutes with total tensor by the pure-tensor identity.
Source: Stacks Project, Tags 03EL, 06YN and 07A4
(blueprint: lem-weil-pbc-ringed-slice-total-tensor-comparison).

Proof: use the natural module tensor restriction isomorphism on every (p,q)
summand. Its pure-section formula is x tensor y mapped to x tensor y, including
the sheafification units. Restriction preserves coproducts: the sheafification
adjunction and sectionwise restriction identify sheaf coproducts as restricted
sheafified presheaf coproducts, using the slice-sheafification comparison.
Therefore the direct sum of these summand isomorphisms identifies
the degree-k terms. Naturality on each summand commutes with d_P tensor 1 and
1 tensor d_Q; additivity preserves the coefficient (-1)^p in the second term.
The degreewise maps are consequently a chain isomorphism, with inverse given
by the inverse summand maps. Summand naturality also proves naturality in both
complexes. Composing the pure-section formula with the total summand inclusion
gives the stated formula for the actual coefficientTensorGenerator. No K-flatness,
flat terms or boundedness are needed; zero and unbounded complexes are included. -/
theorem ringedSlice_totalTensorComparison_exists (U : C) :
    ∃ γ : coefficientTotalTensor.{u, c, v} J A ⋙
        ringedSliceComplexRestriction.{c, v, u} J A U ≅
      ((ringedSliceComplexRestriction.{c, v, u} J A U).prod
        (ringedSliceComplexRestriction.{c, v, u} J A U)) ⋙
          coefficientTotalTensor.{u, max c v, v} (J.over U) (A.over U),
      ∀ (P Q : CochainComplex (SheafOfModules.{max c v u} ((sheafCompose J (forget₂
        CommRingCat.{max c v u} RingCat.{max c v u})).obj A)) ℤ)
        (p q k : ℤ) (h : p + q = k) (V : Over U)
        (x : (P.X p).val.obj (op V.left)) (y : (Q.X q).val.obj (op V.left)),
        ((γ.hom.app (P, Q)).f k).val.app (op V)
          (coefficientTensorGenerator.{u, c, v} J A P Q p q k h (op V.left) x y) =
        coefficientTensorGenerator.{u, max c v, v} (J.over U) (A.over U)
          ((ringedSliceComplexRestriction.{c, v, u} J A U).obj P)
          ((ringedSliceComplexRestriction.{c, v, u} J A U).obj Q) p q k h (op V) x y := by
  obtain ⟨γ, hγ⟩ := tensorComplexOverComparison.{c, v, u} J A U
  exact ⟨γ, hγ⟩

end CategoryTheory
