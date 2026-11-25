/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.CoefficientAffineConstructibleProEtaleModules
public import WeilConjectures.AlgebraicGeometry.PointModelRestrictionModule
import WeilConjectures.AlgebraicGeometry.CoefficientSliceFixedModuleEquivalence
import WeilConjectures.AlgebraicGeometry.ConstantCoefficientPullbackCoordinates
import WeilConjectures.AlgebraicGeometry.ConstantModuleGlobalEncoding
import Mathlib.CategoryTheory.Adjunction.Mates

/-! # Internal module coordinates on a coefficient-sized slice

Source: Stacks Project, Tags 00YV, 03CY and 04IX.
(auxiliary; not a blueprint node).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
attribute [local instance 2000] AlgebraicGeometry.ProEtale.sheafMonoidalCategory
  AlgebraicGeometry.ProEtale.sheafMonoidalClosed
namespace AlgebraicGeometry.ProEtale.IntegralModelsStacks

-- Uniqueness fixes this choice even though the coefficient-cartesianness proof is postponed.
@[irreducible] private noncomputable def chosenCoordinates
    {X Y : Scheme.{u}} (f : Y ⟶ X)
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (k : Type (u + 1)) [CommRing k]
    (c : ConstantCompletion.constant (Scheme.coefficientProEtaleModelTopology.{u, u} X) k ≅
      smallRing X (condensedRingObj Λ X)) :
    ConstantCompletion.constant (Scheme.coefficientProEtaleModelTopology.{u, u} Y) k ≅
        smallRing Y (condensedRingObj Λ Y) :=
  (constant_coefficient_pullback_coordinates f Λ k c).exists.choose

private theorem chosenCoordinates_spec
    {X Y : Scheme.{u}} (f : Y ⟶ X)
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (k : Type (u + 1)) [CommRing k]
    (c : ConstantCompletion.constant (Scheme.coefficientProEtaleModelTopology.{u, u} X) k ≅
      smallRing X (condensedRingObj Λ X)) :
    let d := chosenCoordinates f Λ k c
    ∀ (V : (Scheme.coefficientProEtaleSiteModel.{u, u} X)ᵒᵖ) (a : k),
        ((InternalModuleOperations.coefficientMap Λ f).hom.app
          (AsSmall.down.op.obj V)).hom
            (c.hom.hom.app V
              ((toSheafify (Scheme.coefficientProEtaleModelTopology.{u, u} X)
                ((Functor.const _).obj (CommRingCat.of k))).app V a)) =
          d.hom.hom.app ((Scheme.coefficientProEtaleModelBaseChange.{u, u} f).op.obj V)
            ((toSheafify (Scheme.coefficientProEtaleModelTopology.{u, u} Y)
              ((Functor.const _).obj (CommRingCat.of k))).app
                ((Scheme.coefficientProEtaleModelBaseChange.{u, u} f).op.obj V) a) := by
  unfold chosenCoordinates
  exact (constant_coefficient_pullback_coordinates f Λ k c).exists.choose_spec

@[irreducible] private noncomputable def chosenEncoding
    (X : Scheme.{u})
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (k : Type (u + 1)) [CommRing k]
    (c : ConstantCompletion.constant (Scheme.coefficientProEtaleModelTopology.{u, u} X) k ≅
      smallRing X (condensedRingObj Λ X)) :
    Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X) ≌
        Sheaf (Scheme.coefficientProEtaleModelTopology.{u, u} X) (ModuleCat.{u + 1} k) :=
  (constant_module_global_encoding X Λ k c).choose

private theorem chosenEncoding_spec
    (X : Scheme.{u})
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (k : Type (u + 1)) [CommRing k]
    (c : ConstantCompletion.constant (Scheme.coefficientProEtaleModelTopology.{u, u} X) k ≅
      smallRing X (condensedRingObj Λ X)) :
    let E := chosenEncoding X Λ k c
    E.functor = smallModules X (condensedRingObj Λ X) ⋙ ConstantCompletion.res c.hom ⋙
        coefficientModelFixedScalars _ k ∧
      Nonempty (E.functor.obj (Mod.regular (condensedRingObj Λ X)) ≅
        (constantSheaf (Scheme.coefficientProEtaleModelTopology.{u, u} X)
          (ModuleCat.{u + 1} k)).obj (ModuleCat.of k k)) ∧
      ∀ {Y : Scheme.{u}} (f : Y ⟶ X)
        (d : ConstantCompletion.constant (Scheme.coefficientProEtaleModelTopology.{u, u} Y) k ≅
          smallRing Y (condensedRingObj Λ Y)),
        (∀ (V : (Scheme.coefficientProEtaleSiteModel.{u, u} X)ᵒᵖ) (a : k),
          ((InternalModuleOperations.coefficientMap Λ f).hom.app
            (AsSmall.down.op.obj V)).hom
              (c.hom.hom.app V
                ((toSheafify (Scheme.coefficientProEtaleModelTopology.{u, u} X)
                  ((Functor.const _).obj (CommRingCat.of k))).app V a)) =
            d.hom.hom.app ((Scheme.coefficientProEtaleModelBaseChange.{u, u} f).op.obj V)
              ((toSheafify (Scheme.coefficientProEtaleModelTopology.{u, u} Y)
                ((Functor.const _).obj (CommRingCat.of k))).app
                  ((Scheme.coefficientProEtaleModelBaseChange.{u, u} f).op.obj V) a)) →
        Nonempty (CondensedRing.upperStar Λ f ⋙
          (smallModules Y (condensedRingObj Λ Y) ⋙ ConstantCompletion.res d.hom ⋙
            coefficientModelFixedScalars _ k) ≅
          E.functor ⋙ Scheme.coefficientProEtaleFixedModulePullback.{u, u} f k) := by
  unfold chosenEncoding
  exact (constant_module_global_encoding X Λ k c).choose_spec

namespace SliceChoice
open Scheme

@[irreducible] private noncomputable def chosenSlice
    (Y : Scheme.{u}) (U : coefficientProEtaleSiteModel.{u, u} Y)
    (k : Type (u + 1)) [CommRing k] :
    Sheaf (coefficientProEtaleModelTopology.{u, u} (AsSmall.down.obj U).left)
          (ModuleCat.{u + 1} k) ≌
        Sheaf ((coefficientProEtaleModelTopology.{u, u} Y).over U) (ModuleCat.{u + 1} k) :=
  (coefficient_slice_fixed_module_equivalence Y U k).choose

private theorem chosenSlice_spec
    (Y : Scheme.{u}) (U : coefficientProEtaleSiteModel.{u, u} Y)
    (k : Type (u + 1)) [CommRing k] :
    let S := chosenSlice Y U k
    Nonempty (coefficientProEtaleFixedModulePullback.{u, u} (AsSmall.down.obj U).hom k ⋙
        S.functor ≅ (coefficientProEtaleModelTopology.{u, u} Y).overPullback
          (ModuleCat.{u + 1} k) U) ∧
      ∀ M : ModuleCat.{u + 1} k,
        Nonempty (S.functor.obj
          ((constantSheaf
            (coefficientProEtaleModelTopology.{u, u} (AsSmall.down.obj U).left)
            (ModuleCat.{u + 1} k)).obj M) ≅
          (constantSheaf ((coefficientProEtaleModelTopology.{u, u} Y).over U)
            (ModuleCat.{u + 1} k)).obj M) := by
  unfold chosenSlice
  exact (coefficient_slice_fixed_module_equivalence Y U k).choose_spec

end SliceChoice

private noncomputable def fixedModelBaseChangeComp
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    Scheme.coefficientProEtaleModelBaseChange.{u, u} g ⋙
      Scheme.coefficientProEtaleModelBaseChange.{u, u} f ≅
      Scheme.coefficientProEtaleModelBaseChange.{u, u} (f ≫ g) :=
  NatIso.ofComponents
    (fun (V : Scheme.coefficientProEtaleSiteModel.{u, u} Z) ↦ AsSmall.up.mapIso
      ((MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤) f g).symm.app
        (AsSmall.down.obj V)))
    (by
      intro V W a
      apply ULift.ext
      exact (MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤) f g).inv.naturality
        (AsSmall.down.map a))

private noncomputable def fixedPullbackComp
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (R : Type (u + 1)) [CommRing R] :
    Scheme.coefficientProEtaleFixedModulePullback.{u, u} (f ≫ g) R ≅
      Scheme.coefficientProEtaleFixedModulePullback.{u, u} g R ⋙
        Scheme.coefficientProEtaleFixedModulePullback.{u, u} f R := by
  let adj₁ := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (Scheme.coefficientProEtaleModelBaseChange.{u, u} (f ≫ g)) (ModuleCat.{u + 1} R)
      (Scheme.coefficientProEtaleModelTopology.{u, u} Z)
      (Scheme.coefficientProEtaleModelTopology.{u, u} X)
  let adj₂ :=
    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
      (Scheme.coefficientProEtaleModelBaseChange.{u, u} g) (ModuleCat.{u + 1} R)
        (Scheme.coefficientProEtaleModelTopology.{u, u} Z)
        (Scheme.coefficientProEtaleModelTopology.{u, u} Y)).comp
    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
      (Scheme.coefficientProEtaleModelBaseChange.{u, u} f) (ModuleCat.{u + 1} R)
        (Scheme.coefficientProEtaleModelTopology.{u, u} Y)
        (Scheme.coefficientProEtaleModelTopology.{u, u} X))
  let i := Functor.sheafPushforwardContinuousComp' (eFG := fixedModelBaseChangeComp f g)
    (ModuleCat.{u + 1} R) (Scheme.coefficientProEtaleModelTopology.{u, u} Z)
    (Scheme.coefficientProEtaleModelTopology.{u, u} Y)
    (Scheme.coefficientProEtaleModelTopology.{u, u} X)
  exact ((conjugateIsoEquiv adj₁ adj₂).symm i.symm).symm

private theorem threeFunctorObj
    {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
    (F : A ⥤ B) (G : B ⥤ C) (H : C ⥤ D) (N : A) :
    (F ⋙ G ⋙ H).obj N = H.obj ((F ⋙ G).obj N) := rfl

private theorem transObj
    {A B C : Type*} [Category* A] [Category* B] [Category* C]
    (E : A ≌ B) (S : B ≌ C) (N : A) :
    (E.trans S).functor.obj N = S.functor.obj (E.functor.obj N) := rfl

private theorem restrictionObj
    {X Y Z : Scheme.{u}} (f : Y ⟶ X) (g : Z ⟶ Y)
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    pointModelRestriction Λ f N g = (CondensedRing.upperStar Λ (g ≫ f)).obj N := rfl

private theorem overObj
    {C D : Type*} [Category* C] [Category* D]
    (J : GrothendieckTopology C) (U : C) (M : Sheaf J D) :
    (J.overPullback D U).obj M = M.over U := rfl

/-- Encoding comparison for all modules, before choosing any presentation.

Source: Stacks Project, Sites, Tag 00YV, functoriality of algebraic structures;
Modules on Sites, Tags 03CY and 04IX, sheafification and localization of modules.
(auxiliary; not a blueprint node).

Proof: reconstruct internal modules by the section-module equivalence, transport
through AsSmall, restrict scalars along c and use the constant-ring/fixed-scalar
equivalence. Pull c directly along U.hom ≫ f using the actual condensed coefficient
map to obtain coordinates dZ on Z = U.left. The global encoding comparison along
this composite sends its internal inverse image to the fixed-scalar inverse image
along the composite. Composition of fixed-scalar direct images and uniqueness of
left adjoints identify that inverse image with inverse image along f followed by
U.hom. The weakly-etale slice equivalence then identifies the latter with slice
restriction. This avoids an intermediate encoding on Y and the internal-module
pullback compositor. The global encoding sends the regular module to the constant
regular k-module, and the slice equivalence preserves that constant sheaf. All
coordinate choices are uniquely determined. The empty scheme and zero ring use
the same constructions. -/
theorem constant_slice_module_encoding
    {X Y : Scheme.{u}} (f : Y ⟶ X)
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (k : Type (u + 1)) [CommRing k]
    (c : ConstantCompletion.constant (Scheme.coefficientProEtaleModelTopology.{u, u} X) k ≅
      smallRing X (condensedRingObj Λ X))
    (U : Scheme.coefficientProEtaleSiteModel.{u, u} Y) :
    ∃ E : Mod (Sheaf (Scheme.ProEt.topology (AsSmall.down.obj U).left) Ab.{u + 1})
        (condensedRingObj Λ (AsSmall.down.obj U).left) ≌
      Sheaf ((Scheme.coefficientProEtaleModelTopology.{u, u} Y).over U)
        (ModuleCat.{u + 1} k),
      (∀ N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X),
        Nonempty (E.functor.obj (pointModelRestriction Λ f N (AsSmall.down.obj U).hom) ≅
          (((Scheme.coefficientProEtaleFixedModulePullback.{u, u} f k).obj
            ((coefficientModelFixedScalars _ k).obj
              ((smallModules X (condensedRingObj Λ X) ⋙
                ConstantCompletion.res c.hom).obj N))).over U))) ∧
      Nonempty (E.functor.obj (Mod.regular (condensedRingObj Λ (AsSmall.down.obj U).left)) ≅
        (constantSheaf ((Scheme.coefficientProEtaleModelTopology.{u, u} Y).over U)
          (ModuleCat.{u + 1} k)).obj (ModuleCat.of k k)) := by
  let Z : Scheme.{u} := (AsSmall.down.obj U).left
  let g : Z ⟶ Y := (AsSmall.down.obj U).hom
  let dZ := chosenCoordinates (g ≫ f) Λ k c
  have hdZ := chosenCoordinates_spec (g ≫ f) Λ k c
  let EX := chosenEncoding X Λ k c
  let EZ := chosenEncoding Z Λ k dZ
  have hEX := (chosenEncoding_spec X Λ k c).1
  have hEZ := (chosenEncoding_spec Z Λ k dZ).1
  let p := ((chosenEncoding_spec X Λ k c).2.2 (g ≫ f) dZ hdZ).some
  let hreg := (chosenEncoding_spec Z Λ k dZ).2.1.some
  let S := SliceChoice.chosenSlice Y U k
  let hS := (SliceChoice.chosenSlice_spec Y U k).1.some
  let a := ((SliceChoice.chosenSlice_spec Y U k).2 (ModuleCat.of k k)).some
  let E := EZ.trans S
  let P := Scheme.coefficientProEtaleFixedModulePullback.{u, u} f k
  let T := (Scheme.coefficientProEtaleModelTopology.{u, u} Y).overPullback
    (ModuleCat.{u + 1} k) U
  refine ⟨E, ?_, ⟨S.functor.mapIso hreg ≪≫ a⟩⟩
  intro N
  let Nz := (CondensedRing.upperStar Λ (g ≫ f)).obj N
  let eZ := eqToIso (congrArg (fun F ↦ F.obj Nz) hEZ)
  let eX := P.mapIso (eqToIso (congrArg (fun F ↦ F.obj N) hEX))
  let hObj := threeFunctorObj (smallModules X (condensedRingObj Λ X))
    (ConstantCompletion.res c.hom) (coefficientModelFixedScalars _ k) N
  let M := (coefficientModelFixedScalars _ k).obj
    ((smallModules X (condensedRingObj Λ X) ⋙ ConstantCompletion.res c.hom).obj N)
  exact ⟨E.functor.mapIso (eqToIso (restrictionObj f g Λ N)) ≪≫
    eqToIso (transObj EZ S Nz) ≪≫
    S.functor.mapIso (eZ ≪≫ p.app N ≪≫ (fixedPullbackComp g f k).app (EX.functor.obj N)) ≪≫
    hS.app (P.obj (EX.functor.obj N)) ≪≫
    T.mapIso (eX ≪≫ P.mapIso (eqToIso hObj)) ≪≫
    eqToIso (overObj (Scheme.coefficientProEtaleModelTopology.{u, u} Y) U (P.obj M))⟩

end AlgebraicGeometry.ProEtale.IntegralModelsStacks
