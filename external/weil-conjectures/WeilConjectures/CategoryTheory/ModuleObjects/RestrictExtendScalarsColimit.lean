/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PushPadicAlgClColimit

/-!
# Restriction of scalars of an extension of scalars to a colimit of algebras

Let `C` be a braided monoidal category whose tensor product preserves colimits, `R` a commutative
algebra object and `M` an `R`-module object. For a morphism of algebras `s : S ⟶ S'` under `R`,
the map `S ⊗_R M ⟶ S' ⊗_R M` is `R`-linear (`CategoryTheory.Mod.restrictExtendChange`).

If `T = colim_j S_j` is a colimit of `R`-algebras, then `Res_R(T ⊗_R M) = colim_j Res_R(S_j ⊗_R M)`
as `R`-module objects (`CategoryTheory.Mod.isColimitRestrictExtendScalarsColimitCocone`), the
forgetful functor from `R`-module objects reflecting colimits.
-/

@[expose] public section

universe v₁ u₁

open CategoryTheory Limits MonoidalCategory MonObj

namespace CategoryTheory.Mod

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
  [HasCoequalizers C] [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)] [BraidedCategory C]
  {R : C} [MonObj R] [IsCommMonObj R]

section Change

variable {S S' : C} [MonObj S] [MonObj S'] {φ : R ⟶ S} {φ' : R ⟶ S'} [IsMonHom φ]
  [IsMonHom φ'] (s : S ⟶ S') [IsMonHom s] (h : φ ≫ s = φ') (M : Mod C R)

/-- The map `S ⊗_R M ⟶ S' ⊗_R M`, `x ⊗ m ↦ s(x) ⊗ m`, as a morphism of `R`-modules. -/
noncomputable def restrictExtendChange :
    (comap φ).obj (extendScalarsObj φ M) ⟶ (comap φ').obj (extendScalarsObj φ' M) :=
  Hom.mk' (extendChangeHom s h M) (by
    rw [comap_obj_smul φ, comap_obj_smul φ', Category.assoc, smul_extendChangeHom,
      ← whisker_exchange_assoc, ← comp_whiskerRight_assoc, h]
    rfl)

@[simp]
lemma restrictExtendChange_hom : (restrictExtendChange s h M).hom = extendChangeHom s h M := rfl

end Change

section Colimit

variable {J : Type} [SmallCategory J] (S : J ⥤ C) [∀ j, MonObj (S.obj j)]
  [∀ {j k : J} (g : j ⟶ k), IsMonHom (S.map g)] (φ : ∀ j, R ⟶ S.obj j) [∀ j, IsMonHom (φ j)]
  (hφ : ∀ {j k : J} (g : j ⟶ k), φ j ≫ S.map g = φ k) (M : Mod C R)

/-- The diagram `j ↦ Res_R(S_j ⊗_R M)` of `R`-module objects attached to a diagram of
`R`-algebras `j ↦ S_j`. -/
@[simps]
noncomputable def restrictExtendScalarsColimitDiagram : J ⥤ Mod C R where
  obj j := (comap (φ j)).obj (extendScalarsObj (φ j) M)
  map g := restrictExtendChange (S.map g) (hφ g) M
  map_id j := Mod.hom_ext _ _ ((extendScalarsColimitDiagram S φ hφ M).map_id j)
  map_comp g g' := Mod.hom_ext _ _ ((extendScalarsColimitDiagram S φ hφ M).map_comp g g')

variable {T : C} [MonObj T] (ι : ∀ j, S.obj j ⟶ T)
  (hι : ∀ {j k : J} (g : j ⟶ k), S.map g ≫ ι k = ι j)
  [∀ j, IsMonHom (ι j)] (ψ : R ⟶ T) [IsMonHom ψ] (hψ : ∀ j, φ j ≫ ι j = ψ)

/-- The cocone `Res_R(S_j ⊗_R M) ⟶ Res_R(T ⊗_R M)` of `R`-module objects attached to a cocone of
`R`-algebras `S_j ⟶ T`. -/
@[simps]
noncomputable def restrictExtendScalarsColimitCocone :
    Cocone (restrictExtendScalarsColimitDiagram S φ hφ M) where
  pt := (comap ψ).obj (extendScalarsObj ψ M)
  ι :=
    { app j := restrictExtendChange (ι j) (hψ j) M
      naturality _ _ g := Mod.hom_ext _ _
        ((extendScalarsColimitCocone S φ hφ M ι hι ψ hψ).ι.naturality g) }

/-- **Restriction of scalars of an extension of scalars to a colimit of algebras**: if
`T = colim_j S_j` in `C`, then `Res_R(T ⊗_R M) = colim_j Res_R(S_j ⊗_R M)` as `R`-module
objects. -/
noncomputable def isColimitRestrictExtendScalarsColimitCocone
    (hc : IsColimit (algCocone S ι hι)) :
    IsColimit (restrictExtendScalarsColimitCocone S φ hφ M ι hι ψ hψ) := by
  let h := isColimitExtendScalarsColimitCocone S φ hφ M ι hι ψ hψ hc
  let hR := isColimitOfPreserves (tensorLeft R) h
  let c (s : Cocone (restrictExtendScalarsColimitDiagram S φ hφ M)) :
      Cocone (extendScalarsColimitDiagram S φ hφ M) :=
    { pt := s.pt.X
      ι :=
        { app j := (s.ι.app j).hom
          naturality _ _ g := by
            have := congrArg Hom.hom (s.ι.naturality g)
            simpa using this } }
  exact
    { desc s := Hom.mk' (h.desc (c s)) (by
        refine hR.hom_ext fun j ↦ ?_
        have h₁ := IsModHom.smul_hom (A := R)
          (f := ((restrictExtendScalarsColimitCocone S φ hφ M ι hι ψ hψ).ι.app j).hom)
        have h₂ := IsModHom.smul_hom (A := R) (f := (s.ι.app j).hom)
        have h₃ : extendChangeHom (ι j) (hψ j) M ≫ h.desc (c s) = (s.ι.app j).hom :=
          h.fac (c s) j
        dsimp at h₁ h₂ ⊢
        simp only [restrictExtendScalarsColimitCocone_ι_app, restrictExtendChange_hom] at h₁
        rw [extendScalarsColimitCocone_ι_app, ← Category.assoc, ← h₁, Category.assoc, h₃, h₂,
          ← whiskerLeft_comp_assoc, h₃])
      fac s j := Mod.hom_ext _ _ (h.fac (c s) j)
      uniq s m hm := Mod.hom_ext _ _ (h.uniq (c s) m.hom fun j ↦ congrArg Hom.hom (hm j)) }

end Colimit

end CategoryTheory.Mod
