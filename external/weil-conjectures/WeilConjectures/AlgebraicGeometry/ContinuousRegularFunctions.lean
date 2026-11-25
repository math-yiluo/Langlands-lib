/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingObjects.ContinuousMap
public import WeilConjectures.CategoryTheory.Sites.MonObj
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod

import all WeilConjectures.AlgebraicGeometry.IntegralScalarContractive

/-! # Multiplication and coefficient functions of continuous regular modules

The coefficient of an endomorphism is its value on the global unit section. Naturality
and regular-module linearity determine its action everywhere from this function.
(auxiliary; not a blueprint node)
-/

@[expose] public section

universe u
open CategoryTheory Limits MonoidalCategory MonObj Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- Multiply each section by the restriction of a fixed global continuous function. -/
noncomputable def continuousMultiplier (X : Scheme.{u})
    (O : Type) [CommRing O] [TopologicalSpace O] [IsTopologicalRing O] (b : C(X, O)) :
    let R := (sheafCompose (Scheme.ProEt.topology X)
      (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj (continuousMapRingSheaf X O)
    Mod.regular R ⟶ Mod.regular R := by
  let R := (sheafCompose (Scheme.ProEt.topology X)
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj (continuousMapRingSheaf X O)
  let h : R ⟶ R := ⟨{
    app := fun U ↦ AddCommGrpCat.ofHom {
      toFun a := ULift.up (⟨fun x ↦ a.down x * b (U.unop.hom x),
        a.down.continuous.mul (b.continuous.comp U.unop.hom.continuous)⟩ :
          C(U.unop.left, O))
      map_zero' := by apply ULift.ext; ext x; exact zero_mul _
      map_add' a a' := by apply ULift.ext; ext x; exact add_mul _ _ _ }
    naturality := by
      intro U V g
      apply ConcreteCategory.hom_ext
      intro a
      apply ULift.ext
      ext x
      change a.down (g.unop.left x) * b (V.unop.hom x) =
        a.down (g.unop.left x) * b (U.unop.hom (g.unop.left x))
      congr 2
      exact congrArg (fun f : V.unop.left ⟶ X ↦ f x)
        (MorphismProperty.Over.w g.unop).symm }⟩
  refine Mod.homMk h ?_
  let F := sheafToPresheaf (Scheme.ProEt.topology X) Ab.{u + 1}
  let : MonObj R.obj := (continuousMapRingSheaf X O).obj.monObjCompForget₂
  have hp : μ[R.obj] ≫ h.hom = R.obj ◁ h.hom ≫ μ[R.obj] := by
    ext U : 2
    apply AddCommGrpCat.hom_ext_toIntLinearMap
    apply TensorProduct.ext'
    intro a c
    apply ULift.ext
    ext x
    change (a.down x * c.down x) * b (U.unop.hom x) =
      a.down x * (c.down x * b (U.unop.hom x))
    exact mul_assoc _ _ _
  apply Sheaf.tensor_hom_ext
  change Functor.LaxMonoidal.μ F R R ≫ F.map (μ[R] ≫ h) =
    Functor.LaxMonoidal.μ F R R ≫ F.map (R ◁ h ≫ μ[R])
  rw [F.map_comp, F.map_comp, ← Category.assoc, Sheaf.μ_comp_map_mul]
  rw [← Category.assoc, ← Functor.LaxMonoidal.μ_natural_right,
    Category.assoc, Sheaf.μ_comp_map_mul]
  exact hp

/-- The actual abelian sheaf underlying the sheaf of continuous ring-valued functions. -/
noncomputable abbrev continuousAbRing (X : Scheme.{u})
    (O : Type) [CommRing O] [TopologicalSpace O] [IsTopologicalRing O] :=
  (sheafCompose (Scheme.ProEt.topology X) (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
    (continuousMapRingSheaf X O)

/-- Evaluate a regular-module endomorphism on the unit over the terminal site object. -/
noncomputable def regularCoefficient (X : Scheme.{u})
    (O : Type) [CommRing O] [TopologicalSpace O] [IsTopologicalRing O]
    (g : Mod.regular (continuousAbRing X O) ⟶ Mod.regular (continuousAbRing X O)) :
    C(X, O) :=
  (g.hom.hom.app (op (Scheme.ProEt.mk (𝟙 X))) (ULift.up 1)).down

lemma continuousRegular_apply (X : Scheme.{u})
    (O : Type) [CommRing O] [TopologicalSpace O] [IsTopologicalRing O]
    (g : Mod.regular (continuousAbRing X O) ⟶ Mod.regular (continuousAbRing X O))
    (U : X.ProEtᵒᵖ) (a : ULift.{u + 1} C(U.unop.left, O)) (x : U.unop.left) :
    (g.hom.hom.app U a).down x = a.down x * regularCoefficient X O g (U.unop.hom x) := by
  let v : U.unop ⟶ Scheme.ProEt.mk (𝟙 X) := MorphismProperty.Over.homMk U.unop.hom
  have hn := ConcreteCategory.congr_hom (g.hom.hom.naturality v.op)
    (ULift.up (1 : C(X, O)))
  have hone : g.hom.hom.app U (ULift.up 1) =
      ULift.up ((regularCoefficient X O g).comp
        ⟨(U.unop.hom : U.unop.left ⟶ X).base.hom, U.unop.hom.continuous⟩) := hn
  have hmul := continuousRegular_map_mul X O g U a (ULift.up 1)
  have ha : a * ULift.up (1 : C(U.unop.left, O)) = a := by
    apply ULift.ext
    exact mul_one _
  rw [ha, hone] at hmul
  exact congrArg (fun f : ULift.{u + 1} C(U.unop.left, O) ↦ f.down x) hmul

lemma regularCoefficient_injective (X : Scheme.{u})
    (O : Type) [CommRing O] [TopologicalSpace O] [IsTopologicalRing O] :
    Function.Injective (regularCoefficient X O) := by
  intro g h hgh
  apply Mod.hom_ext
  ext U a
  apply ULift.ext
  ext x
  rw [continuousRegular_apply, continuousRegular_apply, hgh]

lemma regularCoefficient_multiplier (X : Scheme.{u})
    (O : Type) [CommRing O] [TopologicalSpace O] [IsTopologicalRing O] (b : C(X, O)) :
    regularCoefficient X O (continuousMultiplier X O b) = b := by
  ext x
  change 1 * b ((𝟙 X) x) = b x
  simp

lemma continuousRegular_mono (X : Scheme.{u})
    (O : Type) [CommRing O] [IsDomain O] [TopologicalSpace O] [IsTopologicalRing O]
    (g : Mod.regular (continuousAbRing X O) ⟶ Mod.regular (continuousAbRing X O))
    (hg : ∀ x, regularCoefficient X O g x ≠ 0) : Mono g := by
  have happ (U : X.ProEtᵒᵖ) : Mono (g.hom.hom.app U) := by
    apply (AddCommGrpCat.mono_iff_injective _).2
    intro a b hab
    apply ULift.ext
    ext x
    have hh := congrArg (fun f : ULift.{u + 1} C(U.unop.left, O) ↦ f.down x) hab
    rw [continuousRegular_apply, continuousRegular_apply] at hh
    exact mul_right_cancel₀ (hg (U.unop.hom x)) hh
  let _ := happ
  have : Mono g.hom.hom := NatTrans.mono_of_mono_app _
  have : Mono ((sheafToPresheaf (Scheme.ProEt.topology X) Ab.{u + 1}).map g.hom) :=
    inferInstanceAs (Mono g.hom.hom)
  have : Mono g.hom := (sheafToPresheaf (Scheme.ProEt.topology X) Ab.{u + 1}).mono_of_mono_map
    (inferInstanceAs (Mono g.hom.hom))
  exact (Mod.forget (continuousAbRing X O)).mono_of_mono_map ‹Mono g.hom›

lemma regularCoefficient_comp (X : Scheme.{u})
    (O : Type) [CommRing O] [TopologicalSpace O] [IsTopologicalRing O]
    (g h : Mod.regular (continuousAbRing X O) ⟶ Mod.regular (continuousAbRing X O)) :
    regularCoefficient X O (g ≫ h) =
      regularCoefficient X O g * regularCoefficient X O h := by
  ext x
  exact continuousRegular_apply X O h (op (Scheme.ProEt.mk (𝟙 X)))
    (g.hom.hom.app (op (Scheme.ProEt.mk (𝟙 X))) (ULift.up 1)) x

/-- The identity regular endomorphism has constant coefficient one.
Source: evaluation of the identity on the unit section.
(auxiliary; not a blueprint node) -/
lemma regularCoefficient_id (X : Scheme.{u})
    (O : Type) [CommRing O] [TopologicalSpace O] [IsTopologicalRing O] :
    regularCoefficient X O (𝟙 (Mod.regular (continuousAbRing X O))) = 1 := rfl

/-- A continuous nowhere-zero field multiplier has a continuous inverse.
Source: continuous reciprocal and the universal property of the regular module.
(auxiliary; not a blueprint node) -/
lemma continuousRegular_field_isIso (X : Scheme.{u})
    (K : Type) [Field K] [TopologicalSpace K] [IsTopologicalRing K] [ContinuousInv₀ K]
    (g : Mod.regular (continuousAbRing X K) ⟶ Mod.regular (continuousAbRing X K))
    (hg : ∀ x, regularCoefficient X K g x ≠ 0) : IsIso g := by
  let b : C(X, K) := ⟨fun x ↦ (regularCoefficient X K g x)⁻¹,
    (regularCoefficient X K g).continuous.inv₀ hg⟩
  let h := continuousMultiplier X K b
  have hgh : g ≫ h = 𝟙 _ := by
    apply regularCoefficient_injective X K
    rw [regularCoefficient_comp, regularCoefficient_multiplier, regularCoefficient_id]
    ext x
    exact mul_inv_cancel₀ (hg x)
  have hhg : h ≫ g = 𝟙 _ := by
    apply regularCoefficient_injective X K
    rw [regularCoefficient_comp, regularCoefficient_multiplier, regularCoefficient_id]
    ext x
    exact inv_mul_cancel₀ (hg x)
  exact ⟨⟨h, hgh, hhg⟩⟩

end AlgebraicGeometry.ProEtale.CondensedRing
