/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.Native.Weil.NativeWeilClosedModels
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedCategory
public import Mathlib.CategoryTheory.Monoidal.Transport
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import Mathlib.CategoryTheory.Monoidal.Braided.Transport
import Mathlib.CategoryTheory.Adjunction.Unique
import WeilConjectures.WeilSheaf.Native.Weil.NativeWeilRingedTensorModel
import WeilConjectures.WeilSheaf.Native.NativeHomRepresentativeUniqueness

/-! # Lifting individual tensor constraints from the Frobenius action site

This file separates lifting structural isomorphisms from checking their coherence laws.
Source: Stacks 06YS and 0FPT
(blueprint: lem-sf-native-weil-tensor-constraint-lifts).
-/

@[expose] public section
set_option autoImplicit false
universe u v w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  CategoryTheory.Functor Opposite
  WeilConjectures
attribute [local instance] uliftCategory

namespace CategoryTheory

/-- Individual associator, unitors and swap for a fixed tensor functor and unit.
No naturality, pentagon, triangle, hexagon or involutivity is assumed here.
Source: Stacks 0FPT, descent of the structural isomorphisms
(blueprint: lem-sf-native-weil-tensor-constraint-lifts). -/
structure TensorConstraintCandidate {C : Type v} [Category.{w} C]
    (T : C × C ⥤ C) (U : C) where
  associator : ∀ A B D : C, T.obj (T.obj (A, B), D) ≅ T.obj (A, T.obj (B, D))
  leftUnitor : ∀ A : C, T.obj (U, A) ≅ A
  rightUnitor : ∀ A : C, T.obj (A, U) ≅ A
  braiding : ∀ A B : C, T.obj (A, B) ≅ T.obj (B, A)

/-- Raw monoidal operations, using precisely the given bifunctor on arrows.
Source: Stacks 0FPT (blueprint: lem-sf-native-weil-tensor-constraint-lifts). -/
@[instance_reducible]
def TensorConstraintCandidate.operations {C : Type v} [Category.{w} C]
    {T : C × C ⥤ C} {U : C} (q : TensorConstraintCandidate T U) :
    MonoidalCategoryStruct C where
  tensorObj A B := T.obj (A, B)
  whiskerLeft A _ _ f := T.map (𝟙 A, f)
  whiskerRight f B := T.map (f, 𝟙 B)
  tensorHom f g := T.map (f, g)
  tensorUnit := U
  associator := q.associator
  leftUnitor := q.leftUnitor
  rightUnitor := q.rightUnitor

/-- A faithful model for raw constraints and their prescribed forgotten images.
`modelData` compares the raw operations with a symmetric monoidal model; it does
not assert any coherence law for the raw operations. `forgetData` specifies the
images of the individual constraints for the very tensor comparison supplied
by the caller. Faithfulness is required only of `model`, never of forgetting.
Source: Stacks 0FPT and the native tensor lift, constraint-descent step
(blueprint: lem-sf-native-weil-tensor-constraint-lifts). -/
structure TensorConstraintLifts {C : Type v} [Category.{w} C]
    {D : Type v} [Category.{w} D]
    (F : C ⥤ D) (T : C × C ⥤ C) (U : C) (V : D) (ζ : F.obj U ≅ V)
    (n : MonoidalCategory D) (β : @SymmetricCategory D _ n)
    (τ : T ⋙ F ≅ F.prod F ⋙ @MonoidalCategory.tensor D _ n) where
  candidate : TensorConstraintCandidate T U
  modelMonoidal : MonoidalCategory (ULift.{0} C)
  modelSymmetry : @SymmetricCategory (ULift.{0} C) _ modelMonoidal
  model : C ⥤ ULift.{0} C
  faithful : model.Faithful
  modelData : @Monoidal.InducingFunctorData (ULift.{0} C) _ modelMonoidal C _
    candidate.operations model
  model_braiding (A B : C) :
    letI := candidate.operations
    (modelData.μIso A B).hom ≫ model.map (candidate.braiding A B).hom =
      (modelSymmetry.toBraidedCategory.braiding (model.obj A) (model.obj B)).hom ≫
        (modelData.μIso B A).hom
  ordinaryUnit : n.tensorUnit ≅ V
  forgetData : @Monoidal.InducingFunctorData D _ n C _ candidate.operations F
  forget_tensor (A B : C) :
    letI := candidate.operations
    (forgetData.μIso A B).symm = τ.app (A, B)
  forget_unit :
    letI := candidate.operations
    forgetData.εIso.symm = ζ ≪≫ ordinaryUnit.symm
  forget_braiding (A B : C) :
    F.map (candidate.braiding A B).hom ≫ τ.hom.app (B, A) =
      τ.hom.app (A, B) ≫ (β.toBraidedCategory.braiding (F.obj A) (F.obj B)).hom

end CategoryTheory

set_option backward.defeqAttrib.useBackward true

attribute [local implicit_reducible] CategoryTheory.uniformProd CategoryTheory.prod'
  CategoryTheory.Prod.sectL CategoryTheory.Prod.sectR
  CategoryTheory.ULift.equivalence CategoryTheory.Monoidal.Transported
  CategoryTheory.Monoidal.induced TensorConstraintCandidate.operations
  CoefficientClosedStructure.tensor

private def parameterMap {C : Type v} [Category.{w} C]
    (T : C × C ⥤ C) {K K' : C} (f : K ⟶ K') :
    Prod.sectL C K ⋙ T ⟶ Prod.sectL C K' ⋙ T where
  app A := T.map (X := (A, K)) (Y := (A, K')) (𝟙 A, f)
  naturality {A B} g := by
    change T.map (X := (A, K)) (Y := (B, K)) (g, 𝟙 K) ≫
        T.map (X := (B, K)) (Y := (B, K')) (𝟙 B, f) =
      T.map (X := (A, K)) (Y := (A, K')) (𝟙 A, f) ≫
        T.map (X := (A, K')) (Y := (B, K')) (g, 𝟙 K')
    rw [← T.map_comp, ← T.map_comp]
    congr 1
    exact Prod.ext ((Category.comp_id _).trans (Category.id_comp _).symm)
      ((Category.id_comp _).trans (Category.comp_id _).symm)

private theorem counit_test {C : Type v} [Category.{w} C]
    {L L' R : C ⥤ C} (b : L' ⊣ R) (x y : L ⟶ L')
    (h : ∀ N, x.app (R.obj N) ≫ b.counit.app N =
      y.app (R.obj N) ≫ b.counit.app N) : x = y := by
  ext A
  have hx : L.map (b.unit.app A) ≫ x.app (R.obj (L'.obj A)) ≫
      b.counit.app (L'.obj A) = x.app A := by
    have hn := x.naturality (b.unit.app A)
    dsimp only [CategoryTheory.Functor.comp_obj, CategoryTheory.Functor.id_obj] at hn
    rw [← Category.assoc, hn, Category.assoc, b.left_triangle_components,
      Category.comp_id]
  have hy : L.map (b.unit.app A) ≫ y.app (R.obj (L'.obj A)) ≫
      b.counit.app (L'.obj A) = y.app A := by
    have hn := y.naturality (b.unit.app A)
    dsimp only [CategoryTheory.Functor.comp_obj, CategoryTheory.Functor.id_obj] at hn
    rw [← Category.assoc, hn, Category.assoc, b.left_triangle_components,
      Category.comp_id]
  rw [← hx, ← hy, h]

private def adjointTensorIso {C : Type v} [Category.{w} C]
    (H : Cᵒᵖ × C ⥤ C) (T R : C × C ⥤ C)
    (a : ∀ K, Prod.sectL C K ⋙ T ⊣ Prod.sectR (op K) C ⋙ H)
    (b : ∀ K, Prod.sectL C K ⋙ R ⊣ Prod.sectR (op K) C ⋙ H)
    (ha : ∀ (K K' L : C) (f : K' ⟶ K),
      T.map (X := (H.obj (op K, L), K')) (Y := (H.obj (op K', L), K'))
        (H.map (X := (op K, L)) (Y := (op K', L)) (f.op, 𝟙 L), 𝟙 K') ≫
        (a K').counit.app L =
      T.map (X := (H.obj (op K, L), K')) (Y := (H.obj (op K, L), K))
        (𝟙 _, f) ≫ (a K).counit.app L)
    (hb : ∀ (K K' L : C) (f : K' ⟶ K),
      R.map (X := (H.obj (op K, L), K')) (Y := (H.obj (op K', L), K'))
        (H.map (X := (op K, L)) (Y := (op K', L)) (f.op, 𝟙 L), 𝟙 K') ≫
        (b K').counit.app L =
      R.map (X := (H.obj (op K, L), K')) (Y := (H.obj (op K, L), K))
        (𝟙 _, f) ≫ (b K).counit.app L) : T ≅ R := by
  let e (K : C) := (a K).leftAdjointUniq (b K)
  have ecounit (K N : C) : (e K).hom.app (H.obj (op K, N)) ≫
      (b K).counit.app N = (a K).counit.app N := by
    simpa only [CategoryTheory.Functor.comp_obj, Prod.sectR_obj] using
      Adjunction.leftAdjointUniq_hom_app_counit (a K) (b K) N
  have he {K K' : C} (f : K ⟶ K') :
      parameterMap T f ≫ (e K').hom = (e K).hom ≫ parameterMap R f := by
    apply counit_test (b K')
    intro N
    dsimp only [NatTrans.comp_app, parameterMap, CategoryTheory.Functor.comp_obj, Prod.sectR_obj]
    simp only [Category.assoc]
    change T.map (X := (H.obj (op K', N), K)) (Y := (H.obj (op K', N), K'))
          (𝟙 _, f) ≫ (e K').hom.app _ ≫ (b K').counit.app N =
      (e K).hom.app _ ≫ R.map (X := (H.obj (op K', N), K))
          (Y := (H.obj (op K', N), K')) (𝟙 _, f) ≫ (b K').counit.app N
    rw [ecounit]
    rw [← hb K' K N f, ← Category.assoc]
    have hn := (e K).hom.naturality
      (H.map (X := (op K', N)) (Y := (op K, N)) (f.op, 𝟙 N))
    dsimp only [CategoryTheory.Functor.comp_map, Prod.sectL_map] at hn
    rw [← hn]
    rw [Category.assoc, ecounit]
    exact (ha K' K N f).symm
  refine NatIso.ofComponents (fun P ↦ (e P.2).app P.1) ?_
  intro P Q f
  have ht : T.map f = T.map (X := P) (Y := (Q.1, P.2)) (f.1, 𝟙 _) ≫
      T.map (X := (Q.1, P.2)) (Y := Q) (𝟙 _, f.2) := by
    rw [← T.map_comp]
    congr 1
    exact Prod.ext (Category.comp_id _).symm (Category.id_comp _).symm
  have hr : R.map f = R.map (X := P) (Y := (Q.1, P.2)) (f.1, 𝟙 _) ≫
      R.map (X := (Q.1, P.2)) (Y := Q) (𝟙 _, f.2) := by
    rw [← R.map_comp]
    congr 1
    exact Prod.ext (Category.comp_id _).symm (Category.id_comp _).symm
  rw [ht, hr, Category.assoc]
  have hh := NatTrans.congr_app (he f.2) Q.1
  dsimp only [NatTrans.comp_app, parameterMap] at hh
  change T.map _ ≫ (T.map _ ≫ (e Q.2).hom.app Q.1) = _
  rw [hh, ← Category.assoc]
  have hn := (e P.2).hom.naturality f.1
  dsimp only [CategoryTheory.Functor.comp_map, Prod.sectL_map] at hn
  simpa only [Category.assoc, Iso.app_hom] using
    congrArg (fun z ↦ z ≫ R.map (X := (Q.1, P.2)) (Y := Q) (𝟙 _, f.2)) hn

private def inducingOfMonoidal {C D : Type v} [Category.{w} C] [Category.{w} D]
    [MonoidalCategory C] [MonoidalCategory D] (F : C ⥤ D) [F.Monoidal] :
    Monoidal.InducingFunctorData F where
  μIso := CategoryTheory.Functor.Monoidal.μIso F
  εIso := CategoryTheory.Functor.Monoidal.εIso F
  whiskerLeft_eq := CategoryTheory.Functor.Monoidal.map_whiskerLeft F
  whiskerRight_eq := CategoryTheory.Functor.Monoidal.map_whiskerRight F
  tensorHom_eq := CategoryTheory.Functor.Monoidal.map_tensor F
  associator_eq := by
    intro A B D
    simpa only [Iso.trans_hom, Iso.symm_hom, MonoidalCategory.tensorIso_hom,
      Iso.refl_hom, MonoidalCategory.tensorHom_id, MonoidalCategory.id_tensorHom,
      CategoryTheory.Functor.Monoidal.μIso_hom, CategoryTheory.Functor.Monoidal.μIso_inv,
        Category.assoc] using
      CategoryTheory.Functor.Monoidal.map_associator F A B D
  leftUnitor_eq := by
    intro A
    simpa only [Iso.trans_hom, Iso.symm_hom, MonoidalCategory.tensorIso_hom,
      Iso.refl_hom, MonoidalCategory.tensorHom_id, CategoryTheory.Functor.Monoidal.μIso_inv,
      CategoryTheory.Functor.Monoidal.εIso_inv, Category.assoc] using
      CategoryTheory.Functor.Monoidal.map_leftUnitor F A
  rightUnitor_eq := by
    intro A
    simpa only [Iso.trans_hom, Iso.symm_hom, MonoidalCategory.tensorIso_hom,
      Iso.refl_hom, MonoidalCategory.id_tensorHom, CategoryTheory.Functor.Monoidal.μIso_inv,
      CategoryTheory.Functor.Monoidal.εIso_inv, Category.assoc] using
      CategoryTheory.Functor.Monoidal.map_rightUnitor F A

@[instance_reducible]
private noncomputable def transportedBraided
    {C D : Type v} [Category.{w} C] [Category.{w} D]
    [m : MonoidalCategory C] [γ : SymmetricCategory C] (e : C ≌ D) :
    @CategoryTheory.Functor.Braided C _ m γ.toBraidedCategory D _
      (CategoryTheory.Monoidal.transport e)
      (Monoidal.Transported.instSymmetricCategory e).toBraidedCategory e.functor := by
  let h : (Monoidal.equivalenceTransported e).functor.Braided := inferInstance
  dsimp only [Monoidal.equivalenceTransported, Monoidal.Transported,
    Monoidal.Transported.instMonoidalCategory,
    Monoidal.Transported.instMonoidalCategoryStruct] at h
  exact h

attribute [local implicit_reducible] inducingOfMonoidal

private theorem constraintsFromModel
    {C D : Type v} [Category.{w} C] [Category.{w} D]
    (m : MonoidalCategory C) (γ : @SymmetricCategory C _ m)
    (n : MonoidalCategory D) (β : @SymmetricCategory D _ n)
    (F : C ⥤ D) (U : C) (V : D) (ζ : F.obj U ≅ V)
    (δ : m.tensorUnit ≅ U) (ε : n.tensorUnit ≅ V)
    (t : @MonoidalCategory.tensor C _ m ⋙ F ≅
      F.prod F ⋙ @MonoidalCategory.tensor D _ n)
    (c : RingedForgetTensorTransposition.TensorCoherence m n γ β F t)
    (hc : c.unit = F.mapIso δ ≪≫ ζ ≪≫ ε.symm)
    (T : C × C ⥤ C) (e : T ≅ @MonoidalCategory.tensor C _ m)
    (τ : T ⋙ F ≅ F.prod F ⋙ @MonoidalCategory.tensor D _ n)
    (hτ : τ = isoWhiskerRight e F ≪≫ t) :
    Nonempty (TensorConstraintLifts F T U V ζ n β τ) := by
  let := m
  let := γ
  let := n
  let := β
  let q : TensorConstraintCandidate T U :=
    { associator := fun A B D ↦
        e.app (T.obj (A, B), D) ≪≫
          (MonoidalCategory.tensor C).mapIso ((e.app (A, B)).prod (Iso.refl D)) ≪≫
          (α_ A B D) ≪≫
          (MonoidalCategory.tensor C).mapIso ((Iso.refl A).prod (e.app (B, D)).symm) ≪≫
          (e.app (A, T.obj (B, D))).symm
      leftUnitor := fun A ↦ e.app (U, A) ≪≫
        (MonoidalCategory.tensor C).mapIso (δ.symm.prod (Iso.refl A)) ≪≫ λ_ A
      rightUnitor := fun A ↦ e.app (A, U) ≪≫
        (MonoidalCategory.tensor C).mapIso ((Iso.refl A).prod δ.symm) ≪≫ ρ_ A
      braiding := fun A B ↦ e.app (A, B) ≪≫ β_ A B ≪≫ (e.app (B, A)).symm }
  have hm {P Q : C × C} (f : P ⟶ Q) :
      T.map f = e.hom.app P ≫ (MonoidalCategory.tensor C).map f ≫ e.inv.app Q := by
    rw [← Category.assoc, ← e.hom.naturality]
    simp only [Category.assoc, Iso.hom_inv_id_app, Category.comp_id]
  let i : @Monoidal.InducingFunctorData C _ m C _ q.operations (𝟭 C) := by
    refine @Monoidal.InducingFunctorData.mk C _ m C _ q.operations (𝟭 C)
      (fun A B ↦ (e.app (A, B)).symm) ?_ ?_ ?_ δ ?_ ?_ ?_
    · intro A B D f
      dsimp +instances only [TensorConstraintCandidate.operations,
        CategoryTheory.Functor.id_map, CategoryTheory.Functor.id_obj]
      simpa only [CategoryTheory.Functor.id_map, TensorConstraintCandidate.operations,
        Iso.symm_inv, Iso.symm_hom, Iso.app_hom, Iso.app_inv, Prod.mkHom,
        MonoidalCategory.tensor_map,
        id_tensorHom] using hm (P := (A, B)) (Q := (A, D)) (Prod.mkHom (𝟙 A) f)
    · intro A B f D
      dsimp +instances only [TensorConstraintCandidate.operations,
        CategoryTheory.Functor.id_map, CategoryTheory.Functor.id_obj]
      simpa only [CategoryTheory.Functor.id_map, TensorConstraintCandidate.operations,
        Iso.symm_inv, Iso.symm_hom, Iso.app_hom, Iso.app_inv, Prod.mkHom,
        MonoidalCategory.tensor_map,
        tensorHom_id] using hm (P := (A, D)) (Q := (B, D)) (Prod.mkHom f (𝟙 D))
    · intro A B D E f g
      dsimp +instances only [TensorConstraintCandidate.operations,
        CategoryTheory.Functor.id_map, CategoryTheory.Functor.id_obj]
      simpa only [CategoryTheory.Functor.id_map, TensorConstraintCandidate.operations,
        Iso.symm_inv, Iso.symm_hom, Iso.app_hom, Iso.app_inv, Prod.mkHom,
        MonoidalCategory.tensor_map]
        using hm (P := (A, D)) (Q := (B, E)) (Prod.mkHom f g)
    · intro A B D
      dsimp +instances only [TensorConstraintCandidate.operations,
        CategoryTheory.Functor.id_map, CategoryTheory.Functor.id_obj]
      simp only [q, Iso.trans_hom, CategoryTheory.Functor.mapIso_hom, Iso.symm_hom,
        MonoidalCategory.tensor_map, Iso.prod_hom, Iso.refl_hom,
        MonoidalCategory.tensorIso_hom, Iso.symm_inv, Category.assoc]
    · intro A
      dsimp +instances [CategoryTheory.Functor.id_map, q, TensorConstraintCandidate.operations,
        MonoidalCategory.tensor, MonoidalCategory.tensorIso]
      simp only [Category.assoc]
    · intro A
      dsimp +instances [CategoryTheory.Functor.id_map, q, TensorConstraintCandidate.operations,
        MonoidalCategory.tensor, MonoidalCategory.tensorIso]
      simp only [Category.assoc]
  -- Realize the faithful model on the required universe-lift category.
  let up : C ≌ ULift.{0} C := ULift.equivalence
  let mU : MonoidalCategory (ULift.{0} C) := CategoryTheory.Monoidal.transport up
  let γU : @SymmetricCategory (ULift.{0} C) _ mU :=
    Monoidal.Transported.instSymmetricCategory up
  let := mU
  let umon : @CategoryTheory.Functor.Monoidal C _ m (ULift.{0} C) _ mU up.functor :=
    (@transportedBraided C (ULift.{0} C) _ _ m γ up).toMonoidal
  let fcore : F.CoreMonoidal := CategoryTheory.Functor.CoreMonoidal.mk'
    c.unit.symm (fun A B ↦ (t.app (A, B)).symm)
    (by
      intro A B f D
      have hn := t.hom.naturality (X := (A, D)) (Y := (B, D)) (Prod.mkHom f (𝟙 D))
      dsimp only [CategoryTheory.Functor.comp_map, CategoryTheory.Functor.prod_map,
        MonoidalCategory.tensor_map] at hn
      simp only [CategoryTheory.Functor.map_id] at hn
      rw [@MonoidalCategory.tensorHom_id _ _ n _ _ (F.map f) (F.obj D)] at hn
      simpa only [Iso.symm_inv, tensorHom_id, Iso.app_hom] using hn.symm)
    (by
      intro A B D f
      have hn := t.hom.naturality (X := (D, A)) (Y := (D, B)) (Prod.mkHom (𝟙 D) f)
      dsimp only [CategoryTheory.Functor.comp_map, CategoryTheory.Functor.prod_map,
        MonoidalCategory.tensor_map] at hn
      simp only [CategoryTheory.Functor.map_id] at hn
      rw [@MonoidalCategory.id_tensorHom _ _ n (F.obj D) _ _ (F.map f)] at hn
      simpa only [Iso.symm_inv, id_tensorHom, Iso.app_hom] using hn.symm)
    (by
      intro A B D
      simpa only [Iso.symm_inv, MonoidalCategory.tensor_map,
        MonoidalCategory.tensorHom_id, MonoidalCategory.id_tensorHom, Iso.app_hom,
        MonoidalCategory.tensor_obj] using
        (c.associativity A B D).symm)
    (by
      intro A
      apply (cancel_mono (λ_ (F.obj A)).hom).1
      simp only [Iso.inv_hom_id, Iso.symm_inv, Category.assoc]
      have hl := c.left_unit A
      simp only [MonoidalCategory.tensor_map, tensorHom_id] at hl
      simp only [Iso.app_hom]
      rw [hl]
      rw [← F.map_comp, Iso.inv_hom_id, F.map_id])
    (by
      intro A
      apply (cancel_mono (ρ_ (F.obj A)).hom).1
      simp only [Iso.inv_hom_id, Iso.symm_inv, Category.assoc]
      have hr := c.right_unit A
      simp only [MonoidalCategory.tensor_map, id_tensorHom] at hr
      simp only [Iso.app_hom]
      rw [hr]
      rw [← F.map_comp, Iso.inv_hom_id, F.map_id])
  let fmon : F.Monoidal := fcore.toMonoidal
  let : F.Monoidal := fmon
  let : up.functor.Monoidal := umon
  let := γU
  let μup := CategoryTheory.Functor.LaxMonoidal.μ up.functor
  have hbraid (A B : C) :
      μup A B ≫ up.functor.map (β_ A B).hom =
        (β_ (up.functor.obj A) (up.functor.obj B)).hom ≫ μup B A := by
    let : up.functor.Braided :=
      @transportedBraided C (ULift.{0} C) _ _ m γ up
    exact CategoryTheory.Functor.Braided.braided (F := up.functor) A B
  let mi : MonoidalCategory C := @Monoidal.induced C _ m C _ q.operations
    (𝟭 C) (inferInstance : (𝟭 C).Faithful) i
  let im : @CategoryTheory.Functor.Monoidal C _ mi C _ m (𝟭 C) :=
    @Monoidal.fromInducedMonoidal C _ m C _ q.operations (𝟭 C) inferInstance i
  let liftMon : @CategoryTheory.Functor.Monoidal C _ mi (ULift.{0} C) _ mU up.functor :=
    @CategoryTheory.Functor.Monoidal.instComp C _ mi C _ m (ULift.{0} C) _ mU
      (𝟭 C) up.functor im umon
  let := mi
  let := mU
  let : up.functor.Monoidal := liftMon
  let rawMon : F.Monoidal :=
    @CategoryTheory.Functor.Monoidal.instComp C _ mi C _ m D _ n (𝟭 C) F im fmon
  let modelData : @Monoidal.InducingFunctorData (ULift.{0} C) _ mU C _
      q.operations up.functor := by
    change @Monoidal.InducingFunctorData (ULift.{0} C) _ mU C _
      mi.toMonoidalCategoryStruct up.functor
    exact @inducingOfMonoidal C (ULift.{0} C) _ _ mi mU up.functor liftMon
  let : F.Monoidal := rawMon
  let fd : @Monoidal.InducingFunctorData D _ n C _ q.operations F := by
    change @Monoidal.InducingFunctorData D _ n C _ mi.toMonoidalCategoryStruct F
    exact @inducingOfMonoidal C D _ _ mi n F rawMon
  refine ⟨{ candidate := q
            modelMonoidal := mU
            modelSymmetry := γU
            model := up.functor
            faithful := inferInstance
            modelData := modelData
            model_braiding := ?_
            ordinaryUnit := ε
            forgetData := fd
            forget_tensor := ?_
            forget_unit := ?_
            forget_braiding := ?_ }⟩
  · intro A B
    dsimp +instances only [modelData, inducingOfMonoidal, CategoryTheory.Functor.Monoidal.μIso,
      liftMon, CategoryTheory.Functor.Monoidal.instComp, CategoryTheory.Functor.LaxMonoidal.comp,
      im, Monoidal.fromInducedMonoidal, Monoidal.fromInducedCoreMonoidal,
      CategoryTheory.Functor.CoreMonoidal.toMonoidal,
        CategoryTheory.Functor.CoreMonoidal.toLaxMonoidal, i]
    change (μup A B ≫ up.functor.map (e.app (A, B)).inv) ≫
        up.functor.map (q.braiding A B).hom =
      (γU.toBraidedCategory.braiding (up.functor.obj A) (up.functor.obj B)).hom ≫
        (μup B A ≫ up.functor.map (e.app (B, A)).inv)
    dsimp only [q, Iso.trans_hom, Iso.symm_hom]
    simp only [CategoryTheory.Functor.map_comp, Category.assoc,
      Iso.inv_hom_id_map_assoc]
    rw [← Category.assoc, hbraid]
    simp only [Category.assoc]
  · intro A B
    subst τ
    apply Iso.ext
    dsimp +instances only [fd, inducingOfMonoidal, CategoryTheory.Functor.Monoidal.μIso,
      rawMon, CategoryTheory.Functor.Monoidal.instComp, CategoryTheory.Functor.OplaxMonoidal.comp,
      im, Monoidal.fromInducedMonoidal, Monoidal.fromInducedCoreMonoidal,
      CategoryTheory.Functor.CoreMonoidal.toMonoidal,
        CategoryTheory.Functor.CoreMonoidal.toOplaxMonoidal,
      i, fmon, fcore, CategoryTheory.Functor.CoreMonoidal.mk']
    change F.map (e.app (A, B)).hom ≫ (t.app (A, B)).hom = _
    rfl
  · apply Iso.ext
    dsimp +instances only [fd, inducingOfMonoidal, CategoryTheory.Functor.Monoidal.εIso,
      rawMon, CategoryTheory.Functor.Monoidal.instComp, CategoryTheory.Functor.OplaxMonoidal.comp,
      im, Monoidal.fromInducedMonoidal, Monoidal.fromInducedCoreMonoidal,
      CategoryTheory.Functor.CoreMonoidal.toMonoidal,
        CategoryTheory.Functor.CoreMonoidal.toOplaxMonoidal,
      i, fmon, fcore, CategoryTheory.Functor.CoreMonoidal.mk']
    change F.map δ.inv ≫ c.unit.hom = ζ.hom ≫ ε.inv
    rw [hc]
    simp only [Iso.trans_hom, CategoryTheory.Functor.mapIso_hom, Iso.symm_hom,
      Iso.inv_hom_id_map_assoc]
  · intro A B
    subst τ
    simp +instances only [q, Iso.trans_hom, Iso.symm_hom, CategoryTheory.Functor.map_comp,
      Iso.trans_hom, isoWhiskerRight_hom, NatTrans.comp_app, whiskerRight_app,
      Iso.app_hom, Category.assoc]
    simp only [Iso.app_inv]
    have hcan : F.map (e.inv.app (B, A)) ≫ F.map (e.hom.app (B, A)) = 𝟙 _ := by
      rw [← F.map_comp, Iso.inv_hom_id_app, F.map_id]
    rw [reassoc_of% hcan, c.symmetry]

private def tensorSliceIso {C : Type v} [Category.{w} C]
    (m : MonoidalCategory C) (K : C) :
    Prod.sectL C K ⋙ @MonoidalCategory.tensor C _ m ≅
      @MonoidalCategory.tensorRight C _ m K := by
  let := m
  exact NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
    intro A B f
    change (f ⊗ₘ 𝟙 K) ≫ 𝟙 _ = 𝟙 _ ≫ (f ▷ K)
    simp only [tensorHom_id, Category.comp_id, Category.id_comp])

private theorem uncurry_postcomp
    {D : Type v} [Category.{w} D] {H : Dᵒᵖ × D ⥤ D}
    (S : CoefficientClosedStructure H) {A K N N' : D}
    (g : A ⟶ H.obj (op K, N)) (f : N ⟶ N') :
    (S.transpose A K N').symm (g ≫ H.map (Prod.mkHom (𝟙 (op K)) f)) =
      (S.transpose A K N).symm g ≫ f :=
  (S.adjunction K).homEquiv_naturality_right_symm g f

private theorem constraintsFromClosedModel
    {C D : Type v} [Category.{w} C] [Category.{w} D]
    (H : Cᵒᵖ × C ⥤ C) (H' : Dᵒᵖ × D ⥤ D) (F : C ⥤ D)
    (W : CoefficientClosedStructure H) (S : CoefficientClosedStructure H')
    (η : H ⋙ F ≅ F.op.prod F ⋙ H')
    (T : C × C ⥤ C)
    (a : ∀ K, Prod.sectL C K ⋙ T ⊣ Prod.sectR (op K) C ⋙ H)
    (ha : ∀ (K K' L : C) (f : K' ⟶ K),
      T.map (X := (H.obj (op K, L), K')) (Y := (H.obj (op K', L), K'))
        (H.map (X := (op K, L)) (Y := (op K', L)) (f.op, 𝟙 L), 𝟙 K') ≫
          (a K').counit.app L =
      T.map (X := (H.obj (op K, L), K')) (Y := (H.obj (op K, L), K))
        (𝟙 _, f) ≫ (a K).counit.app L)
    (τ : T ⋙ F ≅ F.prod F ⋙ S.tensor)
    (hτ : ∀ A K, τ.inv.app (A, K) =
      (S.transpose (F.obj A) (F.obj K) (F.obj (T.obj (A, K)))).symm
        (F.map ((a K).unit.app A) ≫ η.hom.app (op K, T.obj (A, K))))
    (γ : @SymmetricCategory C _ W.monoidal)
    (β : @SymmetricCategory D _ S.monoidal)
    (U : C) (V : D) (ζ : F.obj U ≅ V)
    (δ : W.monoidal.tensorUnit ≅ U) (ε : S.monoidal.tensorUnit ≅ V)
    (t : W.tensor ⋙ F ≅ F.prod F ⋙ S.tensor)
    (c : RingedForgetTensorTransposition.TensorCoherence W.monoidal S.monoidal γ β F t)
    (hc : c.unit = F.mapIso δ ≪≫ ζ ≪≫ ε.symm)
    (ht : ∀ A K, t.inv.app (A, K) =
      (S.transpose (F.obj A) (F.obj K) (F.obj (W.tensor.obj (A, K)))).symm
        (F.map ((W.adjunction K).unit.app A) ≫ η.hom.app (op K, W.tensor.obj (A, K)))) :
    Nonempty (TensorConstraintLifts F T U V ζ S.monoidal β τ) := by
  let b (K : C) :=
    (W.adjunction K).ofNatIsoLeft (tensorSliceIso W.monoidal K).symm
  have hbunit (A K : C) :
      (b K).unit.app A = (W.adjunction K).unit.app A := by
    change (W.adjunction K).unit.app A ≫
      (Prod.sectR (op K) C ⋙ H).map (𝟙 _) = _
    rw [CategoryTheory.Functor.map_id]
    dsimp +instances only [CategoryTheory.Functor.comp_obj, CategoryTheory.Functor.id_obj]
    exact Category.comp_id _
  have hbcounit (K L : C) :
      (b K).counit.app L = (W.adjunction K).counit.app L := by
    change 𝟙 _ ≫ _ = _
    exact Category.id_comp _
  have hb (K K' L : C) (f : K' ⟶ K) :
      W.tensor.map
          (H.map (X := (op K, L)) (Y := (op K', L)) (f.op, 𝟙 L), 𝟙 K') ≫
        (b K').counit.app L =
      W.tensor.map (X := (H.obj (op K, L), K'))
          (Y := (H.obj (op K, L), K)) (𝟙 _, f) ≫ (b K).counit.app L := by
    rw [hbcounit, hbcounit]
    let := W.monoidal
    have hn := W.evaluation_naturality K K' L f
    dsimp only [tensorRight, tensorLeft, MonoidalCategory.curriedTensor,
      CategoryTheory.Functor.flip] at hn
    simpa only [CoefficientClosedStructure.tensor, MonoidalCategory.tensor_map,
      MonoidalCategory.tensor_obj, tensorHom_id, id_tensorHom] using hn
  let e := adjointTensorIso H T W.tensor a b ha hb
  have hu (A K : C) :
      (a K).unit.app A ≫ H.map
        (X := (op K, T.obj (A, K))) (Y := (op K, W.tensor.obj (A, K)))
        (Prod.mkHom (𝟙 (op K)) (e.hom.app (A, K))) = (W.adjunction K).unit.app A := by
    change (a K).unit.app A ≫ (Prod.sectR (op K) _ ⋙ H).map
      (((a K).leftAdjointUniq (b K)).hom.app A) = _
    rw [Adjunction.unit_leftAdjointUniq_hom_app, hbunit]
  have he (A K : C) :
      τ.inv.app (A, K) ≫ (F).map (e.hom.app (A, K)) =
        t.inv.app (A, K) := by
    rw [hτ, ht]
    rw [← uncurry_postcomp S (A := F.obj A) (K := F.obj K)
      (N := F.obj (T.obj (A, K))) (N' := F.obj (W.tensor.obj (A, K)))
      (F.map ((a K).unit.app A) ≫ η.hom.app (op K, T.obj (A, K)))
      (F.map (e.hom.app (A, K))) ]
    congr 1
    have hn := η.hom.naturality
      (Prod.mkHom (𝟙 (op K)) (e.hom.app (A, K)))
    dsimp only [CategoryTheory.Functor.comp_map, CategoryTheory.Functor.prod_map,
      CategoryTheory.Functor.op_map] at hn
    dsimp +instances only [CategoryTheory.Functor.comp_obj,
      CategoryTheory.Functor.prod_obj, CategoryTheory.Functor.op_obj,
      CategoryTheory.Functor.id_obj, Prod.sectR_obj, MonoidalCategory.tensorRight,
      MonoidalCategory.curriedTensor, CategoryTheory.Functor.flip,
      CoefficientClosedStructure.tensor, MonoidalCategory.tensor_obj]
    simp only [Prod.mkHom, unop_id, CategoryTheory.Functor.map_id, op_id] at hn
    simp only [Category.assoc]
    change (F).map ((a K).unit.app A) ≫
          (η.hom.app (op K, T.obj (A, K)) ≫ _ ) = _
    rw [← hn, ← Category.assoc, ← (F).map_comp, hu]
    rfl
  have hcomp : τ = isoWhiskerRight e (F) ≪≫ t := by
    apply Iso.ext_inv
    apply NatTrans.ext
    funext P
    rcases P with ⟨A, K⟩
    change τ.inv.app (A, K) = t.inv.app (A, K) ≫ (F).map (e.inv.app (A, K))
    rw [← he A K]
    simp only [Category.assoc, ← (F).map_comp,
      Iso.hom_inv_id_app]
    rw [CategoryTheory.Functor.map_id]
    dsimp +instances only [CategoryTheory.Functor.comp_obj]
    exact (Category.comp_id _).symm
  exact constraintsFromModel W.monoidal γ S.monoidal β F
    U V ζ δ ε t c hc T e τ hcomp

namespace AlgebraicGeometry.ProEtaleWeilSheaf
variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)] (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]

/-- Lift the individual structural isomorphisms, with their images in a faithful
ringed model and under forgetting. This theorem supplies no monoidal structure
on the specified tensor T, and no pentagon, triangle or braiding axioms for it.

Source: Stacks 06YS and 0FPT; native tensor coherence steps 1--3, restricted to
lifting individual constraints and identifying their images
(blueprint: lem-sf-native-weil-tensor-constraint-lifts).

Proof: present native Weil sheaves as modules on the small Frobenius action
site using frobenius_action_resolutions. If Φ is the ordinary restriction
model, inverse-image composition and the coefficient identification give a
natural isomorphism c: Φ composed with the site action to native pullback
composed with Φ. It fixes the same finite-subextension-valued functions.
Send (N,θ) to (ΦN,c_N followed by Φθ). Naturality gives the intertwining
condition, and the inverse of Φ gives the inverse equivalence of fixed pairs.
This equivalence commutes with forgetting. Localize the additive equivalence.
Transport the ringed closed symmetric monoidal structure
back along this equivalence; this gives modelMonoidal and modelSymmetry.
The tensor right-adjoint functors on this model identify with M.weilHom by
the product-total representative models on K-injectives. Compare their left
adjoints with a using Adjunction.leftAdjointUniq. Its counit identity and ha
make these slice comparisons natural in the tensor parameter, hence an
isomorphism of bifunctors. Conjugate the model associator and swap by this
isomorphism; conjugate the model unitors also by the canonical identification
of its unit with single_0(adicConstant). Take precisely T.map for all raw
tensor and whiskering maps. The inverse bifunctor comparison gives modelData
for the universe-lift realization into the transported ringed model, which is
faithful. These assertions concern individual isomorphisms and their images;
no coherence law for the new operations is used here.

For forgetData, use the ringed forgetful tensor descent on flat-term K-flat
models, which forgetting preserves. The unit-mate formula hτ identifies its
tensorator with τ inverse: evaluate the two Hom representatives componentwise
and use hη and the ordinary adjunction normalization in hS. The signed swap
normalization in hS identifies the ordinary symmetry with the ringed one.
Since hmonoidal fixes the ordinary associator and unitors, the ringed descent
squares give exactly the three displayed inducing-constraint equations and
the swap equation. The whiskering and tensor-map equations follow directly
from naturality of τ. Transport the ringed coefficient-unit identification to
ordinaryUnit; the single-functor factorization of exact forgetting turns the
ringed unit-normalization equation into forget_unit. All comparisons are
natural on the localization, not just on cohomology. The same construction
works for zero complexes and the empty site, and all Koszul signs are retained.
-/
theorem native_weil_tensor_constraint_lifts
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
    [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
    (M : NativeClosedHomModels k₀ l X)
    (η : M.weilHom ⋙ nativeForget k₀ l X ≅
      (nativeForget k₀ l X).op.prod (nativeForget k₀ l X) ⋙ M.ordinaryHom)
    (hη : NativeHomRepresentativeCompatibility (ihomBifunctor k₀ l X)
      (ordinaryIhomBifunctor l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
      M.weilHom M.ordinaryHom M.weilRepresentatives M.ordinaryRepresentatives
      (Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X)) η)
    (S : CoefficientClosedStructure M.ordinaryHom)
    (β : @SymmetricCategory _ _ S.monoidal)
    (hmonoidal : S.monoidal = (inferInstance : MonoidalCategory
      (DerivedCategory (ProEtale.AdicSheaf l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber))))
    (hS : NativeOrdinaryTensorModels l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber
      M.ordinaryHom M.ordinaryRepresentatives S β)
    (T : (DerivedCategory (ProEtaleWeilSheaf k₀ l X)) ×
      DerivedCategory (ProEtaleWeilSheaf k₀ l X) ⥤
        DerivedCategory (ProEtaleWeilSheaf k₀ l X))
    (a : ∀ K : DerivedCategory (ProEtaleWeilSheaf k₀ l X),
      Prod.sectL _ K ⋙ T ⊣ Prod.sectR (op K) _ ⋙ M.weilHom)
    (ha : ∀ (K K' L : DerivedCategory (ProEtaleWeilSheaf k₀ l X)) (f : K' ⟶ K),
        T.map (X := (M.weilHom.obj (op K, L), K'))
            (Y := (M.weilHom.obj (op K', L), K'))
            (M.weilHom.map (X := (op K, L)) (Y := (op K', L)) (f.op, 𝟙 L), 𝟙 K') ≫
              (a K').counit.app L =
          T.map (X := (M.weilHom.obj (op K, L), K'))
            (Y := (M.weilHom.obj (op K, L), K))
            (𝟙 (M.weilHom.obj (op K, L)), f) ≫ (a K).counit.app L)
    (τ : T ⋙ nativeForget k₀ l X ≅
        (nativeForget k₀ l X).prod (nativeForget k₀ l X) ⋙ S.tensor)
    (hτ : ∀ A K : DerivedCategory (ProEtaleWeilSheaf k₀ l X),
        τ.inv.app (A, K) =
          (S.transpose ((nativeForget k₀ l X).obj A) ((nativeForget k₀ l X).obj K)
            ((nativeForget k₀ l X).obj (T.obj (A, K)))).symm
              ((nativeForget k₀ l X).map ((a K).unit.app A) ≫
                η.hom.app (op K, T.obj (A, K)))) :
    Nonempty (TensorConstraintLifts (nativeForget k₀ l X) T
      ((DerivedCategory.singleFunctor _ 0).obj (adicConstant k₀ l X))
      ((DerivedCategory.singleFunctor _ 0).obj
        (ProEtale.AdicSheaf.unit l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber))
      ((Functor.mapDerivedCategorySingleFunctor
        (Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X)) 0).app
          (adicConstant k₀ l X)) S.monoidal β τ) := by
  obtain ⟨W, γ, δ, ε, t, χ, c, hc, hχ, ht⟩ :=
    native_weil_ringed_tensor_model k₀ l X M S β hmonoidal hS
  have hχη : χ = η := native_hom_representative_unique k₀ l X M χ hχ η hη
  subst χ
  exact constraintsFromClosedModel M.weilHom M.ordinaryHom (nativeForget k₀ l X)
    W S η T a ha τ hτ γ β _ _ _ δ ε t c hc ht

end AlgebraicGeometry.ProEtaleWeilSheaf
