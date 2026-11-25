/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.CategoryTheory.Adjunction.FullyFaithful
public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.Algebra.Homology.ExactSequence
/-! # Transport of localization across equivalent coefficient presentations -/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false

@[expose] public noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits
universe u v
namespace AlgebraicGeometry.ProEtale
private theorem exact_localization_transport
    {C : Type*} [Category C] [HasZeroMorphisms C]
    {A B D A' D' : C} (f : A ⟶ B) (g : B ⟶ D)
    [Mono f] [Epi g] (h : (ComposableArrows.mk₂ f g).Exact)
    (a : A' ≅ A) (d : D' ≅ D) :
    Mono (a.hom ≫ f) ∧ Epi (g ≫ d.inv) ∧
      (ComposableArrows.mk₂ (a.hom ≫ f) (g ≫ d.inv)).Exact := by
  refine ⟨inferInstance, inferInstance, ?_⟩
  let e : ComposableArrows.mk₂ (a.hom ≫ f) (g ≫ d.inv) ≅
      ComposableArrows.mk₂ f g :=
    ComposableArrows.isoMk₂ a (Iso.refl B) d
      (by change (a.hom ≫ f) ≫ 𝟙 B = a.hom ≫ f; rw [Category.comp_id])
      (by
        change (g ≫ d.inv) ≫ d.hom = 𝟙 B ≫ g
        rw [Category.assoc, d.inv_hom_id, Category.comp_id, Category.id_comp])
  exact ComposableArrows.exact_of_iso e.symm h

private def openAdjunctionTransport
    {C O S : Type u} [Category.{v} C] [Category.{v} O] [Category.{v} S]
    (Q : O ≌ S) (F : C ⥤ O) (A : S ⥤ C) (R : C ⥤ S)
    (a : A ⊣ R) (e : F ⋙ Q.functor ≅ R) : Q.functor ⋙ A ⊣ F := by
  let b := Q.toAdjunction.comp (a.ofNatIsoRight e.symm)
  let d : (F ⋙ Q.functor) ⋙ Q.inverse ≅ F :=
    Functor.associator _ _ _ ≪≫ isoWhiskerLeft F Q.unitIso.symm ≪≫ Functor.rightUnitor F
  exact b.ofNatIsoRight d

end AlgebraicGeometry.ProEtale
