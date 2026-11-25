/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.CoefficientAffineConstructibleProEtaleModules
import WeilConjectures.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.CategoryTheory.Adjunction.Whiskering

/-! # Fixed-scalar coordinates on a coefficient-sized pro-etale slice

Source: Stacks Project, Tags 00XZ and 04IX.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- Weakly-etale localization in fixed-scalar sheaves, with its inverse-image comparison.

Source: Stacks Project, Sites, Tag 00XZ; Modules on Sites, Tag 04IX.
(auxiliary; not a blueprint node).

Proof: conjugate the concrete weakly-etale slice equivalence by AsSmall, and use
its equivalence of covering sieves to obtain S. Composition with the structural
map is left adjoint to scheme base change. Precomposition on sheaves therefore
identifies the fixed-scalar inverse image with restriction along composition.
After the site equivalence this is the over-forgetful functor, giving the first
comparison. The site equivalence is both continuous and cocontinuous, so its
precomposition commutes with sheafification. Applying that comparison to a
constant presheaf proves the last assertion. -/
theorem coefficient_slice_fixed_module_equivalence
    (Y : Scheme.{u}) (U : coefficientProEtaleSiteModel.{u, u} Y)
    (k : Type (u + 1)) [CommRing k] :
    ∃ S : Sheaf (coefficientProEtaleModelTopology.{u, u} (AsSmall.down.obj U).left)
          (ModuleCat.{u + 1} k) ≌
        Sheaf ((coefficientProEtaleModelTopology.{u, u} Y).over U) (ModuleCat.{u + 1} k),
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
  let W : Y.ProEt := AsSmall.down.obj U
  let Z := W.left
  let JY := coefficientProEtaleModelTopology.{u, u} Y
  let JZ := coefficientProEtaleModelTopology.{u, u} Z
  let eY := AsSmall.equiv.{u, u + 1, u + 1} (C := Y.ProEt)
  let eZ := AsSmall.equiv.{u, u + 1, u + 1} (C := Z.ProEt)
  let e₁ : Over U ≌ Over W := Over.postEquiv (X := U) eY.symm
  let e₂ := ProEt.sliceEquiv Y W
  let e := e₁.trans (e₂.trans eZ)
  have : eY.symm.inverse.IsDenseSubsite (ProEt.topology Y) JY :=
    inferInstanceAs (eY.functor.IsDenseSubsite (ProEt.topology Y)
      (eY.inverse.inducedTopology (ProEt.topology Y)))
  have : eY.inverse.IsDenseSubsite JY (ProEt.topology Y) :=
    inferInstanceAs (eY.symm.functor.IsDenseSubsite JY (ProEt.topology Y))
  have h₁ : e₁.functor.IsDenseSubsite (JY.over U) ((ProEt.topology Y).over W) := by
    refine { functorPushforward_mem_iff := ?_ }
    intro V T
    change T.functorPushforward (Over.post AsSmall.down) ∈ _ ↔ _
    rw [GrothendieckTopology.mem_over_iff, GrothendieckTopology.mem_over_iff]
    change (Sieve.overEquiv ((Over.post AsSmall.down).obj V))
        (T.functorPushforward (Over.post AsSmall.down)) ∈ _ ↔ _
    rw [Sieve.overEquiv_functorPushforward_post]
    exact eY.inverse.functorPushforward_mem_iff JY (ProEt.topology Y)
  have : e₁.symm.inverse.IsDenseSubsite (JY.over U) ((ProEt.topology Y).over W) := h₁
  have : e₁.inverse.IsDenseSubsite ((ProEt.topology Y).over W) (JY.over U) :=
    inferInstanceAs (e₁.symm.functor.IsDenseSubsite ((ProEt.topology Y).over W) (JY.over U))
  have : e₂.inverse.IsDenseSubsite (ProEt.topology Z) ((ProEt.topology Y).over W) :=
    ProEt.sliceDense Y W
  have : eZ.inverse.IsDenseSubsite JZ (ProEt.topology Z) := by
    have : eZ.symm.inverse.IsDenseSubsite (ProEt.topology Z) JZ :=
      inferInstanceAs (eZ.functor.IsDenseSubsite (ProEt.topology Z)
        (eZ.inverse.inducedTopology (ProEt.topology Z)))
    exact inferInstanceAs (eZ.symm.functor.IsDenseSubsite JZ (ProEt.topology Z))
  have : e.inverse.IsDenseSubsite JZ (JY.over U) := by
    refine { functorPushforward_mem_iff := ?_ }
    intro V T
    change T.functorPushforward ((eZ.inverse ⋙ e₂.inverse) ⋙ e₁.inverse) ∈ _ ↔ _
    rw [Sieve.functorPushforward_comp, Sieve.functorPushforward_comp]
    exact (e₁.inverse.functorPushforward_mem_iff
      ((ProEt.topology Y).over W) (JY.over U)).trans
      ((e₂.inverse.functorPushforward_mem_iff
        (ProEt.topology Z) ((ProEt.topology Y).over W)).trans
        (eZ.inverse.functorPushforward_mem_iff JZ (ProEt.topology Z)))
  let S := (e.sheafCongr (JY.over U) JZ (ModuleCat.{u + 1} k)).symm
  let G : coefficientProEtaleSiteModel.{u, u} Z ⥤ coefficientProEtaleSiteModel.{u, u} Y :=
    AsSmall.down ⋙ MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale W.hom) ⋙ AsSmall.up
  let F := coefficientProEtaleModelBaseChange.{u, u} W.hom
  have : F.IsContinuous JY JZ :=
    coefficientProEtaleModelBaseChange_isContinuous.{u, u} W.hom
  have : (AsSmall.up : Y.ProEt ⥤ coefficientProEtaleSiteModel.{u, u} Y).IsContinuous
      (ProEt.topology Y) JY := coefficientProEtaleModelUp_isContinuous.{u, u} Y
  have : G.IsContinuous JZ JY := by
    have : (MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale W.hom)).IsContinuous
        (ProEt.topology Z) (ProEt.topology Y) := ProEt.isContinuous_overMap W.prop
    have := Functor.isContinuous_comp
      (MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale W.hom)) AsSmall.up
      (ProEt.topology Z) (ProEt.topology Y) JY
    exact Functor.isContinuous_comp AsSmall.down _ JZ (ProEt.topology Z) JY
  let a : G ⊣ F := eZ.symm.toAdjunction.comp
    ((MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ W.hom
      inferInstance _root_.trivial).comp eY.toAdjunction)
  let b := a.sheafPushforwardContinuous (E := ModuleCat.{u + 1} k) JZ JY
  let h := (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    F (ModuleCat.{u + 1} k) JY JZ).leftAdjointUniq b
  let n : e.functor ⋙ G ≅ Over.forget U := by
    refine NatIso.ofComponents (fun V ↦ AsSmall.up.mapIso
      (MorphismProperty.Over.isoMk (Iso.refl _) ?_)) ?_
    · change 𝟙 _ ≫ (AsSmall.down.obj V.left).hom =
        (AsSmall.down.map V.hom).left ≫ W.hom
      simpa only [Category.id_comp] using
        (MorphismProperty.Over.w (AsSmall.down.map V.hom)).symm
    · intro V V' v
      apply eY.inverse.map_injective
      apply MorphismProperty.Over.Hom.ext
      change (AsSmall.down.map v.left).left ≫ 𝟙 _ = 𝟙 _ ≫ (AsSmall.down.map v.left).left
      simp
  have : (e.functor ⋙ G).IsContinuous (JY.over U) JY :=
    Functor.isContinuous_comp _ _ _ JZ _
  refine ⟨S, ⟨?_⟩, ?_⟩
  · exact Functor.isoWhiskerRight h S.functor ≪≫
      Functor.sheafPushforwardContinuousComp e.functor G (ModuleCat.{u + 1} k)
        (JY.over U) JZ JY ≪≫
      Functor.sheafPushforwardContinuousIso n (ModuleCat.{u + 1} k) (JY.over U) JY
  · intro M
    exact ⟨((e.functor.pushforwardContinuousSheafificationCompatibility
      (ModuleCat.{u + 1} k) (JY.over U) JZ).app ((Functor.const _).obj M)).symm⟩

end AlgebraicGeometry.Scheme
