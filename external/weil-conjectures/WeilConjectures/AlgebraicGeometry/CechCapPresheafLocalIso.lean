/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.AlternatingCechSheafConstruction

/-! # Intersection restriction becomes invertible on its open

Source: Stacks Project, Tag 02FU, restriction to a member of the covering.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits Opposite
namespace AlgebraicGeometry
noncomputable section

/-- Restrict a module presheaf to intersections with W, retaining scalars on the test open.
Source: Stacks Project, Tag 02FU, restriction on intersection sections. -/
def cechCapPresheafFunctor {X : Scheme.{u}} (W : X.Opens) :
    PresheafOfModules.{u} X.ringCatSheaf.obj ⥤
      PresheafOfModules.{u} X.ringCatSheaf.obj :=
  PresheafOfModules.pushforward (cechCapRingMap W)

/-- The natural restriction of a presheaf to intersections with W.
Source: Stacks Project, Tag 02FU, restriction on intersection sections. -/
def cechCapPresheafUnit {X : Scheme.{u}} (W : X.Opens) :
    𝟭 (PresheafOfModules.{u} X.ringCatSheaf.obj) ⟶ cechCapPresheafFunctor W where
  app P :=
    { app V := ModuleCat.ofHom (X := P.obj V)
        (Y := ((cechCapPresheafFunctor W).obj P).obj V)
        { toFun := fun s ↦ P.map (homOfLE (inf_le_left : V.unop ⊓ W ≤ V.unop)).op s
          map_add' := by intros; simp
          map_smul' := by intro a s; exact P.map_smul _ a s }
      naturality := by
        intro V Z h
        ext s
        change P.map (homOfLE (inf_le_left : Z.unop ⊓ W ≤ Z.unop)).op
            (P.map h s) =
          P.map (homOfLE (inf_le_inf_right W (leOfHom h.unop))).op
            (P.map (homOfLE (inf_le_left : V.unop ⊓ W ≤ V.unop)).op s)
        rw [← PresheafOfModules.map_comp_apply, ← PresheafOfModules.map_comp_apply]
        rfl }
  naturality := by
    intro P Q f
    ext V s
    exact ConcreteCategory.congr_hom (f.naturality
      (homOfLE (inf_le_left : V.unop ⊓ W ≤ V.unop)).op).symm s

private theorem cap_unit_cap_isIso {X : Scheme.{u}} (W : X.Opens)
    (P : PresheafOfModules.{u} X.ringCatSheaf.obj) :
    IsIso ((cechCapPresheafFunctor W).map ((cechCapPresheafUnit W).app P)) := by
  apply (isIso_iff_of_reflects_iso _ (PresheafOfModules.toPresheaf _)).mp
  rw [NatTrans.isIso_iff_isIso_app]
  intro V
  change IsIso (P.presheaf.map
    (homOfLE (inf_le_left : (V.unop ⊓ W) ⊓ W ≤ V.unop ⊓ W)).op)
  have he : (V.unop ⊓ W) ⊓ W = V.unop ⊓ W := inf_assoc _ _ _ |>.trans (by simp)
  have hh : homOfLE (inf_le_left : (V.unop ⊓ W) ⊓ W ≤ V.unop ⊓ W) =
      (eqToIso he).hom := Subsingleton.elim _ _
  rw [hh]
  infer_instance

private theorem cap_unit_pushforward_isIso {X : Scheme.{u}} (W : X.Opens)
    (M : W.toScheme.Modules) :
    IsIso ((cechCapPresheafUnit W).app ((Scheme.Modules.pushforward W.ι).obj M).val) := by
  apply (isIso_iff_of_reflects_iso _ (PresheafOfModules.toPresheaf _)).mp
  rw [NatTrans.isIso_iff_isIso_app]
  intro V
  change IsIso (M.presheaf.map
    ((TopologicalSpace.Opens.map W.ι.base).map
      (homOfLE (inf_le_left : V.unop ⊓ W ≤ V.unop))).op)
  have he : W.ι ⁻¹ᵁ (V.unop ⊓ W) = W.ι ⁻¹ᵁ V.unop := by
    ext x
    simp
  have hh : (TopologicalSpace.Opens.map W.ι.base).map
      (homOfLE (inf_le_left : V.unop ⊓ W ≤ V.unop)) =
      (eqToIso he).hom := Subsingleton.elim _ _
  rw [hh]
  infer_instance

private theorem cap_precompose_bijective {X : Scheme.{u}} (W : X.Opens)
    (P H : PresheafOfModules.{u} X.ringCatSheaf.obj)
    [IsIso ((cechCapPresheafUnit W).app H)] :
    Function.Bijective (fun f : (cechCapPresheafFunctor W).obj P ⟶ H ↦
      (cechCapPresheafUnit W).app P ≫ f) := by
  let K := cechCapPresheafFunctor W
  let ν := cechCapPresheafUnit W
  have : IsIso (K.map (ν.app P)) := cap_unit_cap_isIso W P
  constructor
  · intro f g h
    have he := congrArg K.map h
    simp only [Functor.map_comp] at he
    have hk : K.map f = K.map g := (cancel_epi (K.map (ν.app P))).mp he
    apply (cancel_mono (ν.app H)).mp
    calc
      f ≫ ν.app H = ν.app (K.obj P) ≫ K.map f := ν.naturality f
      _ = ν.app (K.obj P) ≫ K.map g := congrArg (ν.app (K.obj P) ≫ ·) hk
      _ = g ≫ ν.app H := (ν.naturality g).symm
  · intro f
    refine ⟨K.map f ≫ inv (ν.app H), ?_⟩
    change ν.app P ≫ (K.map f ≫ inv (ν.app H)) = f
    calc
      ν.app P ≫ (K.map f ≫ inv (ν.app H)) =
          (f ≫ ν.app H) ≫ inv (ν.app H) := by
        rw [← Category.assoc]
        exact congrArg (· ≫ inv (ν.app H)) (ν.naturality f).symm
      _ = f := by simp only [Category.assoc, IsIso.hom_inv_id, Category.comp_id]

/-- Intersecting with W has no effect after sheafification and restriction to W.
Source: Stacks Project, Tag 02FU, local restriction of the Čech resolution.
(blueprint: lem-pc-s3-cech-cap-presheaf-local-iso).

Proof: Intersecting twice with W equals intersecting once, so K maps the unit
on every presheaf to an isomorphism. For a module sheaf M on W, the unit on the
underlying presheaf of its direct image is invertible: the inverse images of V
and V intersect W in W coincide. Thus precomposition with the unit on P bijects
maps K(P) to that direct image with maps P to it. The inverse sends f to K(f)
followed by the inverse target unit. For injectivity, apply K, cancel the image
unit, and use naturality and the invertible target unit. The composite of the
sheafification and open-restriction adjunctions transfers this bijection to maps
out of the displayed morphism. The coyoneda criterion makes it an isomorphism.
This works for empty W and arbitrary presheaves P. -/
theorem cechCapPresheafUnit_local_isIso {X : Scheme.{u}} (W : X.Opens)
    (P : PresheafOfModules.{u} X.ringCatSheaf.obj) :
    IsIso ((Scheme.Modules.restrictFunctor W.ι).map
      ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
        ((cechCapPresheafUnit W).app P))) := by
  let L := PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
  let F := Scheme.Modules.restrictFunctor W.ι
  let adj := (PresheafOfModules.sheafificationAdjunction
    (𝟙 X.ringCatSheaf.obj)).comp (Scheme.Modules.restrictAdjunction W.ι)
  let T := L ⋙ F
  let ν := cechCapPresheafUnit W
  change IsIso (T.map (ν.app P))
  apply isIso_of_coyoneda_map_bijective
  intro M
  have : IsIso (ν.app ((Scheme.Modules.pushforward W.ι).obj M).val) :=
    cap_unit_pushforward_isIso W M
  let e₁ := adj.homEquiv ((cechCapPresheafFunctor W).obj P) M
  let e₀ := adj.homEquiv P M
  have hb := cap_precompose_bijective W P ((Scheme.Modules.pushforward W.ι).obj M).val
  constructor
  · intro f g h
    apply e₁.injective
    apply hb.1
    have he := congrArg e₀ h
    change adj.homEquiv P M (T.map (ν.app P) ≫ f) =
      adj.homEquiv P M (T.map (ν.app P) ≫ g) at he
    exact (adj.homEquiv_naturality_left (ν.app P) f).symm.trans
      (he.trans (adj.homEquiv_naturality_left (ν.app P) g))
  · intro f
    obtain ⟨g, hg⟩ := hb.2 (e₀ f)
    refine ⟨e₁.symm g, ?_⟩
    apply e₀.injective
    change adj.homEquiv P M (T.map (ν.app P) ≫ e₁.symm g) = e₀ f
    rw [adj.homEquiv_naturality_left, e₁.apply_symm_apply]
    exact hg

end
end AlgebraicGeometry
