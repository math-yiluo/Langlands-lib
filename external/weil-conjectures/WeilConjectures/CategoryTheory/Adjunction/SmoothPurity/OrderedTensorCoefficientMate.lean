/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.NatIso

/-! # Coefficient transport of ordered tensor counit transposes

The argument uses only the projection square and the scalar right-unit equation.
-/

@[expose] public section
set_option autoImplicit false
universe u₁ u₂ u₃ u₄ v₁ v₂ v₃ v₄
open CategoryTheory
namespace CategoryTheory.Adjunction

/-- The projection and evaluation square at the objects used by the tensor transpose.
Source: blueprint smooth-purity reduction compatibility (3).
(blueprint: lem-pur-ordered-tensor-coefficient-mate).
Proof: precompose by the scalar projection isomorphism and compact-support
comparison. The projection square, projection naturality and evaluation square
reduce both sides to tensor naturality followed by the scalar right-unit law. -/
theorem orderedTensor_coefficient_arrow_square
    {C : Type u₁} {D : Type u₂} {C' : Type u₃} {D' : Type u₄}
    [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} C'] [Category.{v₄} D']
    (P : C ⥤ D) (P' : C' ⥤ D') (S : C ⥤ C') (T : D ⥤ D')
    (RY : D ⥤ D) (RY' : D' ⥤ D')
    (b : P ⋙ T ≅ S ⋙ P')
    (W L : C) (W' L' E : C') (I K : D) (I' : D')
    (ρ : RY.obj I ⟶ K) (ρ' : RY'.obj I' ⟶ T.obj K)
    (π : RY.obj (P.obj W) ≅ P.obj L)
    (πs : RY'.obj (P'.obj (S.obj W)) ⟶ P'.obj E)
    (π' : RY'.obj (P'.obj W') ≅ P'.obj L')
    (ε : P.obj W ⟶ I) (ε' : P'.obj W' ⟶ I') (cw : S.obj W ⟶ W')
    (d : S.obj L ⟶ E) (v : E ⟶ L')
    (δW : T.obj (RY.obj (P.obj W)) ⟶ RY'.obj (T.obj (P.obj W)))
    (δI : T.obj (RY.obj I) ⟶ RY'.obj (T.obj I)) (e : T.obj I ⟶ I')
    (hπ : RY'.map (P'.map cw) ≫ π'.hom = πs ≫ P'.map v)
    (hδ : T.map (RY.map ε) ≫ δI = δW ≫ RY'.map (T.map ε))
    (hproj : T.map π.hom ≫ b.hom.app L ≫ P'.map d =
      δW ≫ RY'.map (b.hom.app W) ≫ πs)
    (he : δI ≫ RY'.map e ≫ ρ' = T.map ρ)
    (hunit : b.hom.app W ≫ P'.map cw ≫ ε' = T.map ε ≫ e)
    (domain : S.obj L ⟶ L')
    (hdomain : domain = d ≫ v) :
    b.inv.app L ≫ T.map (π.inv ≫ RY.map ε ≫ ρ) =
      P'.map domain ≫ π'.inv ≫ RY'.map ε' ≫ ρ' := by
  rw [hdomain]
  simp only [P'.map_comp, Category.assoc]
  apply (cancel_epi (T.map π.hom ≫ b.hom.app L)).1
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
  rw [← T.map_comp, Iso.hom_inv_id_assoc]
  rw [reassoc_of% hproj]
  rw [← reassoc_of% hπ]
  simp only [Iso.hom_inv_id_assoc]
  simp only [← Functor.map_comp_assoc]
  rw [hunit]
  simp only [Functor.map_comp, Category.assoc]
  rw [← reassoc_of% hδ, he]

end CategoryTheory.Adjunction
