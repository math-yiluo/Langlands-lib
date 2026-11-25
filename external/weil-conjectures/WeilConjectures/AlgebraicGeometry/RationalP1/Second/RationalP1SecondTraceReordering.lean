/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RationalP1.Second.RationalP1SecondTraceEquation
public import WeilConjectures.CategoryTheory.SixFunctors.LocalizingClosure
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientReference

import WeilConjectures.AlgebraicGeometry.RationalP1.Second.RationalP1SecondScalarTrace

/-! # The diagonal-free second trace rearrangement
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor
universe u₁ v₁ u₂ v₂
section GenericStrength
open Functor.LaxMonoidal Functor.OplaxMonoidal
open CategoryTheory MonoidalCategory
variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
  {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D] [BraidedCategory D]
  (F : C ⥤ D) [F.Monoidal] (K : C) (T : D)

private def str (V : C) : (F.obj K ⊗ T) ⊗ F.obj V ≅ F.obj (K ⊗ V) ⊗ T :=
  (α_ (F.obj K) T (F.obj V)) ≪≫
    tensorIso (Iso.refl _) (β_ T (F.obj V)) ≪≫
    (α_ (F.obj K) (F.obj V) T).symm ≪≫
    tensorIso (Functor.Monoidal.μIso F K V) (Iso.refl T)

private theorem str_nat {V V' : C} (f : V ⟶ V') :
    ((F.obj K ⊗ T) ◁ F.map f) ≫ (str F K T V').hom =
      (str F K T V).hom ≫ (F.map (K ◁ f) ▷ T) := by
  simp only [str, Iso.trans_hom, Iso.symm_hom, tensorIso, Iso.refl_hom,
    Functor.Monoidal.μIso]
  simp only [tensorHom_id, id_tensorHom, Category.assoc]
  rw [associator_naturality_right_assoc]
  rw [← whiskerLeft_comp_assoc, BraidedCategory.braiding_naturality_right,
    whiskerLeft_comp_assoc]
  rw [associator_inv_naturality_middle_assoc]
  rw [← comp_whiskerRight, Functor.LaxMonoidal.μ_natural_right]
  simp only [comp_whiskerRight]

private theorem str_unit :
    (str F K T (𝟙_ C)).hom ≫ (F.map (ρ_ K).hom ▷ T) =
      ((F.obj K ⊗ T) ◁ η F) ≫ (ρ_ (F.obj K ⊗ T)).hom := by
  simp only [str, Iso.trans_hom, Iso.symm_hom, tensorIso, Iso.refl_hom,
    Functor.Monoidal.μIso]
  simp only [tensorHom_id, id_tensorHom, Category.assoc]
  have hu : μ F K (𝟙_ C) ≫ F.map (ρ_ K).hom =
      (F.obj K ◁ η F) ≫ (ρ_ (F.obj K)).hom := by
    apply (cancel_epi (F.obj K ◁ ε F)).1
    rw [← Functor.LaxMonoidal.right_unitality,
      Functor.Monoidal.whiskerLeft_ε_η_assoc]
  rw [← comp_whiskerRight, hu, comp_whiskerRight]
  rw [← associator_inv_naturality_middle_assoc]
  rw [← whiskerLeft_comp_assoc, ← BraidedCategory.braiding_naturality_right,
    whiskerLeft_comp_assoc]
  rw [← associator_naturality_right_assoc]
  congr 1
  simp only [braiding_tensorUnit_right, whiskerLeft_comp,
    Category.assoc]
  monoidal

private theorem str_eval (V : C) (t : V ⟶ 𝟙_ C) :
    (str F K T V).hom ≫ (F.map ((K ◁ t) ≫ (ρ_ K).hom) ▷ T) =
      ((F.obj K ⊗ T) ◁ (F.map t ≫ η F)) ≫ (ρ_ (F.obj K ⊗ T)).hom := by
  rw [F.map_comp, comp_whiskerRight, ← Category.assoc, ← str_nat,
    Category.assoc, str_unit, ← whiskerLeft_comp_assoc]
private theorem conjugated_strength_evaluation
    (V : C) (t : V ⟶ 𝟙_ C) (H : D ⥤ D)
    (a : F.obj K ⊗ T ≅ H.obj (F.obj K))
    (b : F.obj (K ⊗ V) ⊗ T ≅ H.obj (F.obj (K ⊗ V)))
    (hn : b.hom ≫ H.map (F.map ((K ◁ t) ≫ (ρ_ K).hom)) =
      (F.map ((K ◁ t) ≫ (ρ_ K).hom) ▷ T) ≫ a.hom) :
    (a.inv ▷ F.obj V) ≫ (str F K T V).hom ≫ b.hom ≫
        H.map (F.map ((K ◁ t) ≫ (ρ_ K).hom)) =
      (H.obj (F.obj K) ◁ (F.map t ≫ η F)) ≫ (ρ_ (H.obj (F.obj K))).hom := by
  rw [hn, reassoc_of% (str_eval F K T V t)]
  rw [← whisker_exchange_assoc, rightUnitor_naturality_assoc]
  simp only [Iso.inv_hom_id, Category.comp_id]

end GenericStrength

namespace AlgebraicGeometry.ProEtale.RationalP1
open DiagonalCoefficients CondensedRing

attribute [local irreducible] unitComponent counitComponent twistProjectionMap
attribute [local irreducible] coefficient line diagram secondLineComparison
attribute [local irreducible] moduleObjectDerivedPushforward moduleObjectDerivedPullback
attribute [local irreducible] twist projectionMap singleUnitIso
attribute [local irreducible] firstProjection secondProjection square
attribute [local irreducible] condensedAmbientExchange

private theorem tensorShift_naturality
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u}) (L : Modules Λ X)
    {A B : DerivedCategory (Modules Λ X)} (f : A ⟶ B) :
    (f ▷ (((DerivedCategory.singleFunctor (Modules Λ X) 0).obj L) ⟦(2 : ℤ)⟧)) ≫
        (tensorShiftIso Λ X L B).hom =
      (tensorShiftIso Λ X L A).hom ≫ (twist Λ X L).map f := by
  have hn := (NatTrans.shift_app_comm
    ((curriedTensor (DerivedCategory (Modules Λ X))).map f) (2 : ℤ)
      ((DerivedCategory.singleFunctor (Modules Λ X) 0).obj L)).symm
  have ha := (tensorShift_existsUnique Λ X L A).exists.choose_spec
  have hb := (tensorShift_existsUnique Λ X L B).exists.choose_spec
  unfold tensorShiftIso
  unfold twist rationalTwistFunctor CondensedRing.derivedTensor at *
  unfold internalTensorCommShift internalMonoidal internalTensorBundle nativeTensorBundle at *
  rw [eq_of_heq ha, eq_of_heq hb]
  simp only [Functor.comp_obj, Functor.comp_map, Functor.flip_obj_obj, Functor.flip_obj_map,
    curriedTensor_obj_obj, curriedTensor_map_app, Iso.app_hom] at hn ⊢
  convert hn using 1; rfl

private theorem secondTraceStrength_evaluation
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (Y : Scheme.{u})
    (L : Modules Λ (ProjectiveLine Y)) (K V : DerivedCategory (Modules Λ Y))
    (t : V ⟶ 𝟙_ (DerivedCategory (Modules Λ Y))) :
    (secondTraceStrength Λ Y L K V).hom ≫
        (twist Λ (ProjectiveLine Y) L).map
          ((moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y)).map
            ((K ◁ t) ≫ (ρ_ K).hom)) =
      ((twist Λ (ProjectiveLine Y) L).obj
          ((moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y)).obj K) ◁
        ((moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y)).map t ≫
          (secondTraceUnitIso Λ Y).hom)) ≫
        (ρ_ ((twist Λ (ProjectiveLine Y) L).obj
          ((moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y)).obj K))).hom := by
  have hn := tensorShift_naturality Λ (ProjectiveLine Y) L
    ((moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y)).map
      ((K ◁ t) ≫ (ρ_ K).hom))
  let := secondTracePullMonoidal Λ Y
  let := secondTraceBraided Λ Y
  unfold secondTraceStrength secondTraceTensorIso secondTraceSwap secondTraceUnitIso
  simpa only [str, Iso.trans_hom, Iso.symm_hom, tensorIso, Iso.refl_hom,
    Functor.Monoidal.μIso, Functor.Monoidal.εIso, tensorHom_id, id_tensorHom,
    Category.assoc] using
    conjugated_strength_evaluation
      (moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y)) K
      (((DerivedCategory.singleFunctor (Modules Λ (ProjectiveLine Y)) 0).obj L)
        ⟦(2 : ℤ)⟧) V t (twist Λ (ProjectiveLine Y) L)
      (tensorShiftIso Λ (ProjectiveLine Y) L _)
      (tensorShiftIso Λ (ProjectiveLine Y) L _) hn.symm

private theorem counitComponent_factor
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (Y : Scheme.{u})
    (L : ∀ X : Scheme.{u}, Modules Λ X) (d : Diagram Λ Y L)
    (K : DerivedCategory (Modules Λ Y))
    (hq : IsIso (projectionMap Λ (ProjectiveLine Y ↘ Y) K
      (((DerivedCategory.singleFunctor (Modules Λ (ProjectiveLine Y)) 0).obj
        (L (ProjectiveLine Y))) ⟦(2 : ℤ)⟧))) :
    counitComponent Λ Y L d K hq =
      counitProjectionPart Λ Y (L (ProjectiveLine Y)) K hq ≫
        (K ◁ (trace Λ Y L d ≫ (singleUnitIso Λ Y).hom)) ≫ (ρ_ K).hom := by
  unfold counitComponent counitProjectionPart
  simp only [whiskerLeft_comp, Category.assoc]

-- The statement compares several fixed derived pullback and tensor interfaces.
/-- The forward p2 projection cancels the exchange/projection tail against the
pulled counit. This equation has no unit insertion, diagonal tensor comparison,
diagonal class, supported-source map, or integral. -/
theorem second_trace_reordering
    (l : ℕ) [Fact l.Prime] (c : Option (PadicAlgCl.FiniteIntermediateField l))
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (hpl : p ≠ l)
    (Y : Scheme.{u}) [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    [IsNoetherian Y] [IsNoetherian (ProjectiveLine Y)] [IsNoetherian (diagonalSurface Y)]
    [DiagonalTraceLocalizations l Y]
    [DiagonalTraceLocalizations l (ProjectiveLine Y)]
    [DiagonalTraceLocalizations l (diagonalSurface Y)]
    (δ : diagonalCompletedDomain l Y ⟶ diagonalCompletedCodomain l Y)
    (family : Family l Y) (_reference : Reference l Y δ family)
    (K : DerivedCategory (Modules (coefficient l c).X Y))
    (_hK : CategoryTheory.localizingClosure
      (constantModelBoundedConstructible (coefficient l c).X Y) K)
    (ε : (moduleObjectDerivedPushforward (coefficient l c).X (ProjectiveLine Y ↘ Y)).obj
      ((twist (coefficient l c).X (ProjectiveLine Y) (line l c (ProjectiveLine Y))).obj
        ((moduleObjectDerivedPullback (coefficient l c).X (ProjectiveLine Y ↘ Y)).obj K)) ⟶ K)
    (_hε : CounitComponentNormalized (coefficient l c).X Y (line l c)
      (diagram l c Y family) K ε) :
    SecondTraceEquation (coefficient l c).X Y (line l c) (diagram l c Y family)
      (secondLineComparison l c k p hpl Y)
      ((twist (coefficient l c).X (ProjectiveLine Y) (line l c (ProjectiveLine Y))).obj
        ((moduleObjectDerivedPullback (coefficient l c).X (ProjectiveLine Y ↘ Y)).obj K))
      ((twist (coefficient l c).X (ProjectiveLine Y) (line l c (ProjectiveLine Y))).map
        ((moduleObjectDerivedPullback (coefficient l c).X (ProjectiveLine Y ↘ Y)).map ε))
      (secondForwardProjection l c k p hpl Y K) := by
  obtain ⟨hq, hε⟩ := _hε
  have he : ε = counitComponent (coefficient l c).X Y (line l c)
      (diagram l c Y family) K hq := eq_of_heq hε
  subst ε
  obtain ⟨hx, ht⟩ := second_scalar_trace l c k p hpl Y δ family _reference
  let := hx
  constructor
  intro hb hp
  have hpre := (second_pretrace l c k p hpl Y K hq hx).equation hb hp
  have heval := secondTraceStrength_evaluation (coefficient l c).X Y
    (line l c (ProjectiveLine Y)) K
    ((moduleObjectDerivedPushforward (coefficient l c).X (ProjectiveLine Y ↘ Y)).obj
      (((DerivedCategory.singleFunctor (Modules (coefficient l c).X (ProjectiveLine Y))
        0).obj (line l c (ProjectiveLine Y))) ⟦(2 : ℤ)⟧))
    (trace (coefficient l c).X Y (line l c) (diagram l c Y family) ≫
      (singleUnitIso (coefficient l c).X Y).hom)
  have hscalar := congrArg (fun a ↦ inv (secondTraceExchange l c k p hpl Y) ≫ a) ht
  simp only [Functor.map_comp, Category.assoc, IsIso.inv_hom_id_assoc] at hscalar
  rw [counitComponent_factor]
  simp only [Functor.map_comp, Category.assoc] at heval ⊢
  rw [reassoc_of% hpre, heval]
  simp only [← whiskerLeft_comp_assoc]
  rw [hscalar]

end AlgebraicGeometry.ProEtale.RationalP1
