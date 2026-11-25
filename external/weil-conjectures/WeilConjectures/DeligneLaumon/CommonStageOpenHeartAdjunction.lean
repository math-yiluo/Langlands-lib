/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.DeligneLaumon.ConstructiblePullbackTExact

import WeilConjectures.SmoothPurity.Qcqs.QcqsCompactSupportRealization
import WeilConjectures.SmoothPurity.IntegralSupportNormalization.IntegralSupportFunctorNormalization
import WeilConjectures.DeligneLaumon.CompactSupportNormalizedScalarIsomorphisms
import Mathlib.CategoryTheory.Adjunction.Restrict
import WeilConjectures.SmoothPurity.Sf.SfIntegralPullbackLinearAdjunction
import Mathlib.LinearAlgebra.TensorProduct.Map
import all WeilConjectures.SmoothPurity.PurCompactSupport.IntegralCompactSupportCoefficientData
import WeilConjectures.SmoothPurity.Sf.SfRationalDirectImageCoefficientCompatibility
import all WeilConjectures.SmoothPurity.GeneralAlgebraicallyClosedCoefficients.GeneralAlgebraicallyClosedCoefficients
import WeilConjectures.SmoothPurity.Automorphism.AutomorphismConstructibleStageEquivalence
import Mathlib.CategoryTheory.Triangulated.Adjunction
import WeilConjectures.CategoryTheory.Triangulated.TStructure.ShortExact
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor

/-! # Exact extension by zero on the common-stage constructible heart

Source: SGA 4, XVII, §5; Bhatt--Scholze, Proposition 6.8.14 and Remark 6.8.15.
(blueprint: lem-zl-common-stage-open-heart-adjunction).
-/

@[expose] public noncomputable section

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false
set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

-- Keep residue fields abstract during instance matching on different schemes.
attribute [local irreducible] Scheme.residueField

attribute [local irreducible] CategoryTheory.ScalarLocalization.composition

open TensorProduct

namespace Rationalization
open CategoryTheory.ScalarLocalization
variable (R : Type*) [CommRing R] (p : R)
  {C : Type*} [Category C] [Preadditive C] [Linear R C]
  {D : Type*} [Category D] [Preadditive D] [Linear R D]

attribute [-instance] WeilConjectures.CompletedCoefficientPushforward.modAbelian
  WeilConjectures.CompletedCoefficientPushforward.hasDerived
  SheafOfModules.localizedSystemExtensionAdditive
  SheafOfModules.localizedSystemExtensionLimits
  SheafOfModules.localizedSystemExtensionColimits
  SheafOfModules.localizedSystemRestrictionAdditive
  SheafOfModules.localizedSystemRestrictionLimits
  SheafOfModules.localizedSystemRestrictionColimits in
private def liftLinear (F : C ⥤ D) [F.Additive] [F.Linear R] :
    ScalarLocalization R C p ⥤ ScalarLocalization R D p where
  obj X := ⟨F.obj X.obj⟩
  map {X Y} := (F.mapLinearMap R).baseChange (Localization.Away p)
  map_id X := by
    change (F.mapLinearMap R).baseChange (Localization.Away p) (1 ⊗ₜ[R] 𝟙 X.obj) = _
    rw [LinearMap.baseChange_tmul]
    change (1 : Localization.Away p) ⊗ₜ[R] F.map (𝟙 X.obj) =
      (1 : Localization.Away p) ⊗ₜ[R] 𝟙 (F.obj X.obj)
    rw [F.map_id]
  map_comp {X Y Z} f g := by
    change (F.mapLinearMap R).baseChange (Localization.Away p)
      (composition R C p X.obj Y.obj Z.obj g f) =
      composition R D p _ _ _
        ((F.mapLinearMap R).baseChange (Localization.Away p) g)
        ((F.mapLinearMap R).baseChange (Localization.Away p) f)
    induction g using TensorProduct.inductionOn with
    | tmul b g =>
      induction f using TensorProduct.inductionOn with
      | tmul a f =>
        simp only [composition_tmul, LinearMap.baseChange_tmul,
          CategoryTheory.Functor.coe_mapLinearMap]
        change (b * a) ⊗ₜ[R] F.map (f ≫ g) =
          (b * a) ⊗ₜ[R] (F.map f ≫ F.map g)
        rw [F.map_comp]
      | add f g hf hg => simp only [_root_.map_add, hf, hg]
    | add f g hf hg => simp only [_root_.map_add, LinearMap.add_apply, hf, hg]

attribute [-instance] WeilConjectures.CompletedCoefficientPushforward.modAbelian
  WeilConjectures.CompletedCoefficientPushforward.hasDerived
  SheafOfModules.localizedSystemExtensionAdditive
  SheafOfModules.localizedSystemExtensionLimits
  SheafOfModules.localizedSystemExtensionColimits
  SheafOfModules.localizedSystemRestrictionAdditive
  SheafOfModules.localizedSystemRestrictionLimits
  SheafOfModules.localizedSystemRestrictionColimits in
@[simp] private theorem liftLinear_tmul (F : C ⥤ D) [F.Additive] [F.Linear R]
    {X Y : ScalarLocalization R C p} (a : Localization.Away p) (f : X.obj ⟶ Y.obj) :
    (liftLinear R p F).map (a ⊗ₜ[R] f) = a ⊗ₜ[R] F.map f := by
  change (F.mapLinearMap R).baseChange (Localization.Away p) (a ⊗ₜ[R] f) = _
  simpa only [CategoryTheory.Functor.coe_mapLinearMap] using
    (LinearMap.baseChange_tmul (F.mapLinearMap R) a f)

attribute [-instance] WeilConjectures.CompletedCoefficientPushforward.modAbelian
  WeilConjectures.CompletedCoefficientPushforward.hasDerived
  SheafOfModules.localizedSystemExtensionAdditive
  SheafOfModules.localizedSystemExtensionLimits
  SheafOfModules.localizedSystemExtensionColimits
  SheafOfModules.localizedSystemRestrictionAdditive
  SheafOfModules.localizedSystemRestrictionLimits
  SheafOfModules.localizedSystemRestrictionColimits in
private instance liftLinear_additive (F : C ⥤ D) [F.Additive] [F.Linear R] :
    (liftLinear R p F).Additive where
  map_add {X Y f g} := by
    change (F.mapLinearMap R).baseChange (Localization.Away p) (f + g) = _
    exact _root_.map_add _ f g

attribute [-instance] WeilConjectures.CompletedCoefficientPushforward.modAbelian
  WeilConjectures.CompletedCoefficientPushforward.hasDerived
  SheafOfModules.localizedSystemExtensionAdditive
  SheafOfModules.localizedSystemExtensionLimits
  SheafOfModules.localizedSystemExtensionColimits
  SheafOfModules.localizedSystemRestrictionAdditive
  SheafOfModules.localizedSystemRestrictionLimits
  SheafOfModules.localizedSystemRestrictionColimits in
private def liftAdjunction (F : C ⥤ D) [F.Additive] [F.Linear R]
    (G : D ⥤ C) [G.Additive] [G.Linear R] (adj : F ⊣ G) :
    liftLinear R p F ⊣ liftLinear R p G where
  unit :=
    { app X := 1 ⊗ₜ[R] adj.unit.app X.obj
      naturality {X Y} f := by
        dsimp only [liftLinear, CategoryTheory.Functor.id_obj, CategoryTheory.Functor.comp_obj]
        change composition R C p _ _ _
          (1 ⊗ₜ[R] adj.unit.app Y.obj) f =
          composition R C p _ _ _
            ((G.mapLinearMap R).baseChange (Localization.Away p)
              ((F.mapLinearMap R).baseChange (Localization.Away p) f))
            (1 ⊗ₜ[R] adj.unit.app X.obj)
        induction f using TensorProduct.inductionOn with
        | tmul a f =>
          simp only [LinearMap.baseChange_tmul, CategoryTheory.Functor.coe_mapLinearMap,
            composition_tmul, one_mul, mul_one]
          exact congrArg (fun k ↦ a ⊗ₜ[R] k) (adj.unit.naturality f)
        | add f g hf hg => simp only [_root_.map_add, LinearMap.add_apply, hf, hg] }
  counit :=
    { app X := 1 ⊗ₜ[R] adj.counit.app X.obj
      naturality {X Y} f := by
        dsimp only [liftLinear, CategoryTheory.Functor.id_obj, CategoryTheory.Functor.comp_obj]
        change composition R D p _ _ _
          (1 ⊗ₜ[R] adj.counit.app Y.obj)
            ((F.mapLinearMap R).baseChange (Localization.Away p)
              ((G.mapLinearMap R).baseChange (Localization.Away p) f)) =
          composition R D p _ _ _ f (1 ⊗ₜ[R] adj.counit.app X.obj)
        induction f using TensorProduct.inductionOn with
        | tmul a f =>
          simp only [LinearMap.baseChange_tmul, CategoryTheory.Functor.coe_mapLinearMap,
            composition_tmul, one_mul, mul_one]
          exact congrArg (fun k ↦ a ⊗ₜ[R] k) (adj.counit.naturality f)
        | add f g hf hg => simp only [_root_.map_add, LinearMap.add_apply, hf, hg] }
  left_triangle_components X := by
    change composition R D p _ _ _ (1 ⊗ₜ[R] adj.counit.app (F.obj X.obj))
      ((liftLinear R p F).map (1 ⊗ₜ[R] adj.unit.app X.obj)) = _
    rw [liftLinear_tmul, composition_tmul, one_mul]
    exact congrArg (fun k ↦ (1 : Localization.Away p) ⊗ₜ[R] k)
      (adj.left_triangle_components X.obj)
  right_triangle_components X := by
    change composition R C p _ _ _
      ((liftLinear R p G).map (1 ⊗ₜ[R] adj.counit.app X.obj))
      (1 ⊗ₜ[R] adj.unit.app (G.obj X.obj)) = _
    rw [liftLinear_tmul, composition_tmul, one_mul]
    exact congrArg (fun k ↦ (1 : Localization.Away p) ⊗ₜ[R] k)
      (adj.right_triangle_components X.obj)
end Rationalization

namespace CommonOpenHeartProof
open IntegralSupportNormalization FrobeniusExchange CategoryTheory.Functor

section LinearLeft
variable {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
  {F : C ⥤ D} {G : D ⥤ C}
attribute [-instance] WeilConjectures.CompletedCoefficientPushforward.modAbelian
  WeilConjectures.CompletedCoefficientPushforward.hasDerived
  SheafOfModules.localizedSystemExtensionAdditive
  SheafOfModules.localizedSystemExtensionLimits
  SheafOfModules.localizedSystemExtensionColimits
  SheafOfModules.localizedSystemRestrictionAdditive
  SheafOfModules.localizedSystemRestrictionLimits
  SheafOfModules.localizedSystemRestrictionColimits in
private theorem linearLeftOfLinearRight (R : Type*) [CommRing R] [Linear R C] [Linear R D]
    [G.Linear R] (a : F ⊣ G) : F.Linear R where
  map_smul {X Y} f r := by
    apply (a.homEquiv _ _).injective
    have hh (v : X ⟶ Y) : a.homEquiv _ _ (F.map v) = v ≫ a.unit.app Y := by
      rw [a.homEquiv_unit]
      exact (a.unit.naturality v).symm
    rw [hh, a.homEquiv_unit, G.map_smul, Linear.comp_smul, ← a.homEquiv_unit,
      hh, Linear.smul_comp]

end LinearLeft

attribute [-instance] WeilConjectures.CompletedCoefficientPushforward.modAbelian
  WeilConjectures.CompletedCoefficientPushforward.hasDerived
  SheafOfModules.localizedSystemExtensionAdditive
  SheafOfModules.localizedSystemExtensionLimits
  SheafOfModules.localizedSystemExtensionColimits
  SheafOfModules.localizedSystemRestrictionAdditive
  SheafOfModules.localizedSystemRestrictionLimits
  SheafOfModules.localizedSystemRestrictionColimits in
private noncomputable def faithfulIntegralReduction
    {C : Type*} [Category C] {D : Type*} [Category D]
    {Q : Type*} [Category Q]
    (i : C ⥤ D) (hi : i.FullyFaithful)
    {S : D ⥤ Q} {T : Q ⥤ D} (a : S ⊣ T)
    (h : ∀ Y, IsIso (a.unit.app (i.obj Y))) : (i ⋙ S).FullyFaithful where
  preimage {X Y} f := hi.preimage (a.homEquiv _ _ f ≫ inv (a.unit.app (i.obj Y)))
  map_preimage {X Y} f := by
    let := h Y
    change S.map (i.map _) = _
    rw [hi.map_preimage]
    apply (a.homEquiv _ _).injective
    have hh : ∀ g : i.obj X ⟶ i.obj Y,
        a.homEquiv _ _ (S.map g) = g ≫ a.unit.app (i.obj Y) := fun g ↦ by
      rw [a.homEquiv_unit]
      exact (a.unit.naturality g).symm
    rw [hh]
    simp
  preimage_map {X Y} f := by
    let := h Y
    change hi.preimage (a.homEquiv _ _ (S.map (i.map f)) ≫ _) = _
    rw [a.homEquiv_unit]
    have hh := (a.unit.naturality (i.map f)).symm
    change a.unit.app (i.obj X) ≫ T.map (S.map (i.map f)) = _ at hh
    rw [hh]
    simp

section HeartExact
open CategoryTheory.Triangulated
universe uA vA uB vB
variable {A : Type uA} [Category.{vA} A] [Preadditive A] [HasZeroObject A]
  [HasShift A ℤ] [∀ n : ℤ, (shiftFunctor A n).Additive] [Pretriangulated A]
  [IsTriangulated A]
  {B : Type uB} [Category.{vB} B] [Preadditive B] [HasZeroObject B]
  [HasShift B ℤ] [∀ n : ℤ, (shiftFunctor B n).Additive] [Pretriangulated B]
  [IsTriangulated B] (t : TStructure A) (s : TStructure B)
  (G : A ⥤ B) [G.CommShift ℤ] [G.IsTriangulated] [G.Additive]

end HeartExact

namespace StageLeftAdjunction
universe w u₁ v₁ u₂ v₂
variable {I : Type w} [Preorder I]
  {C : I → Type u₁} [∀ i, Category.{v₁} (C i)]
  {B : I → Type u₂} [∀ i, Category.{v₂} (B i)]
  {S : StageSystem C} {T : StageSystem B}

attribute [-instance] WeilConjectures.CompletedCoefficientPushforward.modAbelian
  WeilConjectures.CompletedCoefficientPushforward.hasDerived
  SheafOfModules.localizedSystemExtensionAdditive
  SheafOfModules.localizedSystemExtensionLimits
  SheafOfModules.localizedSystemExtensionColimits
  SheafOfModules.localizedSystemRestrictionAdditive
  SheafOfModules.localizedSystemRestrictionLimits
  SheafOfModules.localizedSystemRestrictionColimits in
private theorem coherenceInv
    (R : StageSystem.Morphism T S)
  (L : ∀ i, C i ⥤ B i) (a : ∀ i, L i ⊣ R.Φ i)
  (b : ∀ {i j : I} (h : i ≤ j), L i ⋙ T.T h ≅ S.T h ⋙ L j)
  (hb : ∀ {i j : I} (h : i ≤ j) (K : C i),
    (S.T h).map ((a i).unit.app K) ≫ (R.β h).hom.app ((L i).obj K) =
      (a j).unit.app ((S.T h).obj K) ≫ (R.Φ j).map ((b h).inv.app K))
    {i j k : I} (h : i ≤ j) (h' : j ≤ k) (K : C i) :
    (L k).map ((S.assoc h h').inv.app K) ≫ (b h').inv.app ((S.T h).obj K) ≫
      (T.T h').map ((b h).inv.app K) =
    (b (h.trans h')).inv.app K ≫ (T.assoc h h').inv.app ((L i).obj K) := by
  apply ((a k).homEquiv _ _).injective
  change (a k).unit.app _ ≫ (R.Φ k).map _ =
    (a k).unit.app _ ≫ (R.Φ k).map _
  simp only [CategoryTheory.Functor.map_comp]
  have hunit := (a k).unit.naturality ((S.assoc h h').inv.app K)
  dsimp only [CategoryTheory.Functor.id_map, CategoryTheory.Functor.comp_map] at hunit
  rw [← reassoc_of% hunit]
  rw [← reassoc_of% (hb h' ((S.T h).obj K))]
  have hn := (R.β h').hom.naturality ((b h).inv.app K)
  dsimp only [CategoryTheory.Functor.comp_map, CategoryTheory.Functor.comp_obj] at hn
  rw [← hn, ← (S.T h').map_comp_assoc, ← hb, (S.T h').map_comp]
  have ht := (S.assoc h h').inv.naturality ((a i).unit.app K)
  dsimp only [CategoryTheory.Functor.comp_map, CategoryTheory.Functor.comp_obj,
    CategoryTheory.Functor.id_obj] at ht
  simp only [Category.assoc]
  rw [← reassoc_of% ht]
  have hc := R.coh h h' ((L i).obj K)
  have hc' : (S.T h').map ((R.β h).hom.app ((L i).obj K)) ≫
      (R.β h').hom.app ((T.T h).obj ((L i).obj K)) =
    (S.assoc h h').hom.app ((R.Φ i).obj ((L i).obj K)) ≫
      (R.β (h.trans h')).hom.app ((L i).obj K) ≫
      (R.Φ k).map ((T.assoc h h').inv.app ((L i).obj K)) := by
    rw [← reassoc_of% hc]
    simp only [← CategoryTheory.Functor.map_comp, Iso.hom_inv_id_app,
      CategoryTheory.Functor.comp_obj, CategoryTheory.Functor.map_id, Category.comp_id]
  rw [hc']
  simp only [Iso.inv_hom_id_app_assoc]
  rw [reassoc_of% (hb (h.trans h') K)]

attribute [-instance] WeilConjectures.CompletedCoefficientPushforward.modAbelian
  WeilConjectures.CompletedCoefficientPushforward.hasDerived
  SheafOfModules.localizedSystemExtensionAdditive
  SheafOfModules.localizedSystemExtensionLimits
  SheafOfModules.localizedSystemExtensionColimits
  SheafOfModules.localizedSystemRestrictionAdditive
  SheafOfModules.localizedSystemRestrictionLimits
  SheafOfModules.localizedSystemRestrictionColimits in
private def family
    (R : StageSystem.Morphism T S)
  (L : ∀ i, C i ⥤ B i) (a : ∀ i, L i ⊣ R.Φ i)
  (b : ∀ {i j : I} (h : i ≤ j), L i ⋙ T.T h ≅ S.T h ⋙ L j)
  (hb : ∀ {i j : I} (h : i ≤ j) (K : C i),
    (S.T h).map ((a i).unit.app K) ≫ (R.β h).hom.app ((L i).obj K) =
      (a j).unit.app ((S.T h).obj K) ≫ (R.Φ j).map ((b h).inv.app K)) : S.Morphism T where
  Φ := L
  β := b
  coh {i j k} h h' K := by
    apply (cancel_epi ((L k).map ((S.assoc h h').inv.app K) ≫
      (b h').inv.app ((S.T h).obj K) ≫ (T.T h').map ((b h).inv.app K))).1
    rw [Category.assoc, Category.assoc, ← (T.T h').map_comp_assoc,
      Iso.inv_hom_id_app]
    change (L k).map ((S.assoc h h').inv.app K) ≫
      (b h').inv.app ((S.T h).obj K) ≫
      (T.T h').map (𝟙 ((L j).obj ((S.T h).obj K))) ≫
      (b h').hom.app ((S.T h).obj K) ≫ (L k).map ((S.assoc h h').hom.app K) = _
    simp only [(T.T h').map_id]
    rw [coherenceInv R L a b hb]
    simp

end StageLeftAdjunction

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
attribute [-instance] WeilConjectures.CompletedCoefficientPushforward.modAbelian
  WeilConjectures.CompletedCoefficientPushforward.hasDerived
  SheafOfModules.localizedSystemExtensionAdditive
  SheafOfModules.localizedSystemExtensionLimits
  SheafOfModules.localizedSystemExtensionColimits
  SheafOfModules.localizedSystemRestrictionAdditive
  SheafOfModules.localizedSystemRestrictionLimits
  SheafOfModules.localizedSystemRestrictionColimits in
private def descendStageAdjunction
    {I : Type*} [Preorder I] [IsDirectedOrder I]
    {C : I → Type*} [∀ i, Category (C i)]
    {C' : I → Type*} [∀ i, Category (C' i)]
    {S : StageSystem C} {T : StageSystem C'}
    (L : S.Morphism T) (R : StageSystem.Morphism T S) (a : ∀ i, L.Φ i ⊣ R.Φ i)
    (η :
    StageSystem.Morphism.Hom (StageSystem.Morphism.id S) (L.comp R))
    (ε : StageSystem.Morphism.Hom (R.comp L) (StageSystem.Morphism.id T))
    (hη : ∀ i, η.τ i = (a i).unit) (hε : ∀ i, ε.τ i = (a i).counit) :
    L.functor ⊣ R.functor where
  unit := StageSystem.Morphism.functorIdIso.inv ≫
    StageSystem.Morphism.descNatTrans η ≫ (L.functorCompIso R).hom
  counit := (R.functorCompIso L).inv ≫
    StageSystem.Morphism.descNatTrans ε ≫ StageSystem.Morphism.functorIdIso.hom
  left_triangle_components X := by
    simp only [NatTrans.comp_app, StageSystem.Morphism.functorIdIso_inv_app,
      StageSystem.Morphism.functorIdIso_hom_app,
      StageSystem.Morphism.functorCompIso_hom_app,
      StageSystem.Morphism.functorCompIso_inv_app,
      Category.id_comp, Category.comp_id, StageSystem.Morphism.descNatTrans_app,
      hη, hε, StageSystem.Morphism.functor_map_ι]
    change (T.ι X.stage).map ((L.Φ X.stage).map ((a X.stage).unit.app X.obj)) ≫
      (T.ι X.stage).map ((a X.stage).counit.app ((L.Φ X.stage).obj X.obj)) = _
    rw [← CategoryTheory.Functor.map_comp]
    change (T.ι X.stage).map _ =
      𝟙 ((T.ι X.stage).obj ((L.Φ X.stage).obj X.obj))
    calc
      _ = (T.ι X.stage).map (𝟙 ((L.Φ X.stage).obj X.obj)) :=
        congrArg ((T.ι X.stage).map) ((a X.stage).left_triangle_components X.obj)
      _ = _ := (T.ι X.stage).map_id _
  right_triangle_components X := by
    simp only [NatTrans.comp_app, StageSystem.Morphism.functorIdIso_inv_app,
      StageSystem.Morphism.functorIdIso_hom_app,
      StageSystem.Morphism.functorCompIso_hom_app,
      StageSystem.Morphism.functorCompIso_inv_app,
      Category.id_comp, Category.comp_id, StageSystem.Morphism.descNatTrans_app,
      hη, hε, StageSystem.Morphism.functor_map_ι]
    change (S.ι X.stage).map ((a X.stage).unit.app ((R.Φ X.stage).obj X.obj)) ≫
      (S.ι X.stage).map ((R.Φ X.stage).map ((a X.stage).counit.app X.obj)) = _
    rw [← CategoryTheory.Functor.map_comp]
    change (S.ι X.stage).map _ =
      𝟙 ((S.ι X.stage).obj ((R.Φ X.stage).obj X.obj))
    calc
      _ = (S.ι X.stage).map (𝟙 ((R.Φ X.stage).obj X.obj)) :=
        congrArg ((S.ι X.stage).map) ((a X.stage).right_triangle_components X.obj)
      _ = _ := (S.ι X.stage).map_id _

section LeftMate
variable {A B C D' : Type*} [Category A] [Category B] [Category C] [Category D']
  {L : A ⥤ B} {P : B ⥤ A} {L' : C ⥤ D'} {P' : D' ⥤ C}
  (a : L ⊣ P) (a' : L' ⊣ P') [IsIso a.unit] [IsIso a'.unit]
  (S : A ⥤ C) (T' : B ⥤ D') (g : P ⋙ S ≅ T' ⋙ P')
  (e : L ⋙ T' ≅ S ⋙ L')

end LeftMate

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  {U T : Scheme.{u}} [baseU : U.Over (Spec (.of D.k))] [baseT : T.Over (Spec (.of D.k))]
  [ftU : LocallyOfFiniteType (U ↘ Spec (.of D.k))]
  [qcU : QuasiCompact (U ↘ Spec (.of D.k))]
  [ftT : LocallyOfFiniteType (T ↘ Spec (.of D.k))]
  [qcT : QuasiCompact (T ↘ Spec (.of D.k))]
  (j : U ⟶ T) [oj : IsOpenImmersion j] [overj : j.IsOver (Spec (.of D.k))]

variable [qj : QuasiCompact j]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

private abbrev integral :=
  sfCompactSupportFiniteIntegralFunctor l D.k
    (PurCompactSupport.coefficientPrimeUnit l D hl)
    (Compactification.ofIsOpenImmersion j) E

attribute [-instance] WeilConjectures.CompletedCoefficientPushforward.modAbelian
  WeilConjectures.CompletedCoefficientPushforward.hasDerived
  SheafOfModules.localizedSystemExtensionAdditive
  SheafOfModules.localizedSystemExtensionLimits
  SheafOfModules.localizedSystemExtensionColimits
  SheafOfModules.localizedSystemRestrictionAdditive
  SheafOfModules.localizedSystemRestrictionLimits
  SheafOfModules.localizedSystemRestrictionColimits in
private def realization :
    integral D l hl j E ⋙ (sfIntegralConstructible l E T).ι ≅
      (sfIntegralConstructible l E U).ι ⋙ ordinaryOpen l E j :=
  (sfQcqsCompactSupportRealization l E D.k
      (PurCompactSupport.coefficientPrimeUnit l D hl)
      (Compactification.ofIsOpenImmersion j)).symm ≪≫
    CategoryTheory.Functor.isoWhiskerLeft (sfIntegralConstructible l E U).ι (openIdentity l E j)

attribute [-instance] WeilConjectures.CompletedCoefficientPushforward.modAbelian
  WeilConjectures.CompletedCoefficientPushforward.hasDerived
  SheafOfModules.localizedSystemExtensionAdditive
  SheafOfModules.localizedSystemExtensionLimits
  SheafOfModules.localizedSystemExtensionColimits
  SheafOfModules.localizedSystemRestrictionAdditive
  SheafOfModules.localizedSystemRestrictionLimits
  SheafOfModules.localizedSystemRestrictionColimits in
private theorem reduction_isIso
    [∀ x : U, Invertible (l : U.residueField x)]
    [∀ y : T, Invertible (l : T.residueField y)] (K : sfIntegralConstructibleCategory l E U) :
    IsIso ((compactOperationReduction l E D.k
      (PurCompactSupport.coefficientPrimeUnit l D hl) j
      (Compactification.ofIsOpenImmersion j)).app K) := by
  let c := Compactification.ofIsOpenImmersion j
  let a := compactOperationReduction l E D.k
    (PurCompactSupport.coefficientPrimeUnit l D hl) j c
  let S := (models l E).system T
  apply (S.isIso_iff_evaluations _).2
  intro n
  have hh := (compactRealization_exists l E D.k
    (PurCompactSupport.coefficientPrimeUnit l D hl) j c).choose_spec K n
  let V := coefficientSequenceDerivedEvaluation l E T n
  let q := (scalarReductionDerivedExtension l E T n).map
    ((compactRealization l E D.k
      (PurCompactSupport.coefficientPrimeUnit l D hl) j c).hom.app K)
  let e := (S.reductionEvaluation n).inv.app ((compactImage l E j c).obj K.obj)
  let r := V.map ((operationReduction l E
    (systemDerivedOpen l E c.i ⋙ systemDirect l E c.g)).app K.obj)
  let d := (compactFiniteEvaluation l E c n).hom.app K.obj
  have : IsIso (q ≫ e ≫ r ≫ d) := by
    have hh' : q ≫ e ≫ r ≫ d = (sfCompactSupportFiniteReductionIso l D.k
        (PurCompactSupport.coefficientPrimeUnit l D hl) c E K n).hom := hh
    rw [hh']
    infer_instance
  have : IsIso (e ≫ r ≫ d) := IsIso.of_isIso_comp_left q _
  have : IsIso (r ≫ d) := IsIso.of_isIso_comp_left e _
  have : IsIso r := IsIso.of_isIso_comp_right r d
  change IsIso (V.map
    (S.reduction.map ((compactRealization l E D.k
      (PurCompactSupport.coefficientPrimeUnit l D hl) j c).hom.app K) ≫
      (operationReduction l E
        (systemDerivedOpen l E c.i ⋙ systemDirect l E c.g)).app K.obj))
  rw [V.map_comp]
  infer_instance

variable (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
  [∀ x : U, Invertible (l : U.residueField x)]
  [∀ y : T, Invertible (l : T.residueField y)]
open GeneralAlgebraicallyClosedCoefficients
open AlgebraicallyClosedCoefficients (Index Coefficient)
attribute [local instance] stageCategory
attribute [local implicit_reducible] catToReflQuiver StageHom
set_option allowUnsafeReducibility true in
attribute [local reducible] Stage stageCategory
set_option linter.auxLemma false in
set_option allowUnsafeReducibility true in
attribute [local reducible] stageCategory._aux_1 stageCategory._aux_3 stageCategory._aux_5
set_option allowUnsafeReducibility true in
attribute [local irreducible] stageSystem commonStageDerivedPullback
  sfCompactSupportFiniteFunctor rationalDerivedPullback

end CommonOpenHeartProof

end WeilConjectures
