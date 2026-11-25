/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
public import WeilConjectures.AlgebraicGeometry.ProEtaleRootsOfUnitySheaf

/-! # Inverse-image comparison for pro-etale roots of unity

Source: Stacks Project, Tag 03PK (auxiliary; not a blueprint node).

## Main definitions

- `proEtaleRootsOfUnityDirectImageMap`: pullback of roots along the projection.
- `proEtaleRootsOfUnityInverseImageMap`: its inverse-image adjunct.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

private theorem sections_inclusion (S : Scheme.{u}) (N : ℕ) (U : S.ProEtᵒᵖ)
    (x : (proEtaleRootsOfUnitySheaf S N).obj.obj U) :
    ULift.up (Additive.ofMul (Additive.toMul
      (proEtaleRootsOfUnitySections S N U x)).val) =
      (proEtaleRootsOfUnityInclusion S N).hom.app U x := by
  exact (existsUnique_proEtaleRootsOfUnitySections S N U).exists.choose_spec x

private theorem sections_map (S : Scheme.{u}) (N : ℕ) {U V : S.ProEtᵒᵖ}
    (a : U ⟶ V) (x : (proEtaleRootsOfUnitySheaf S N).obj.obj U) :
    proEtaleRootsOfUnitySections S N V ((proEtaleRootsOfUnitySheaf S N).obj.map a x) =
      Additive.ofMul (restrictRootsOfUnity a.unop.left.appTop.hom N
        (Additive.toMul (proEtaleRootsOfUnitySections S N U x))) := by
  apply Additive.toMul.injective
  apply Subtype.ext
  have h := congrArg (fun b ↦ b x) ((proEtaleRootsOfUnityInclusion S N).hom.naturality a)
  change (proEtaleRootsOfUnityInclusion S N).hom.app V
      ((proEtaleRootsOfUnitySheaf S N).obj.map a x) =
    (proEtaleUnitsSheaf S).obj.map a
      ((proEtaleRootsOfUnityInclusion S N).hom.app U x) at h
  rw [← sections_inclusion, ← sections_inclusion] at h
  exact congrArg (fun y ↦ y.down.toMul) h

/-- Naturality of the sectionwise projection formula.
Source: Stacks Project, Tag 03PK (auxiliary; not a blueprint node).
The pullback projection square commutes, and global sections turn this commutative
square into the equality of ring maps used below. -/
private theorem proEtaleRootsOfUnityDirectImageNaturality {X Y : Scheme.{u}} (f : X ⟶ Y)
    (N : ℕ) :
    ∀ (U V : Y.ProEtᵒᵖ) (a : U ⟶ V),
      ((proEtaleRootsOfUnitySheaf Y N).obj.map a ≫
        AddCommGrpCat.ofHom
          ((proEtaleRootsOfUnitySections X N
              ((proEtaleBaseChange f).op.obj V)).symm.toAddMonoidHom.comp
            ((restrictRootsOfUnity (pullback.fst V.unop.hom f).appTop.hom N).toAdditive.comp
              (proEtaleRootsOfUnitySections Y N V).toAddMonoidHom))) =
      AddCommGrpCat.ofHom
          ((proEtaleRootsOfUnitySections X N
              ((proEtaleBaseChange f).op.obj U)).symm.toAddMonoidHom.comp
            ((restrictRootsOfUnity (pullback.fst U.unop.hom f).appTop.hom N).toAdditive.comp
              (proEtaleRootsOfUnitySections Y N U).toAddMonoidHom)) ≫
        ((proEtaleBaseChange f).op ⋙ (proEtaleRootsOfUnitySheaf X N).obj).map a := by
  intro U V a
  let r (W : Y.ProEtᵒᵖ) :=
    (restrictRootsOfUnity (pullback.fst W.unop.hom f).appTop.hom N).toAdditive
  let eY (W : Y.ProEtᵒᵖ) := proEtaleRootsOfUnitySections Y N W
  let eX (W : Y.ProEtᵒᵖ) :=
    proEtaleRootsOfUnitySections X N ((proEtaleBaseChange f).op.obj W)
  let a' := (proEtaleBaseChange f).op.map a
  have hproj : ((proEtaleBaseChange f).map a.unop).left ≫
      pullback.fst U.unop.hom f =
      pullback.fst V.unop.hom f ≫ a.unop.left := by
    exact pullback.lift_fst _ _ _
  have hr (y : Additive (rootsOfUnity N ((proEtaleStructureSheaf Y).obj.obj U))) :
      r V (Additive.ofMul (restrictRootsOfUnity a.unop.left.appTop.hom N y.toMul)) =
        Additive.ofMul (restrictRootsOfUnity a'.unop.left.appTop.hom N
          ((r U y).toMul)) := by
    apply Additive.toMul.injective
    apply Subtype.ext
    apply Units.ext
    have h := congrArg (fun g ↦ g.appTop) hproj
    simp only [Hom.comp_appTop] at h
    exact congrArg (fun g ↦ g.hom y.toMul.val.val) h.symm
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro x
  change (eX V).symm (r V (eY V ((proEtaleRootsOfUnitySheaf Y N).obj.map a x))) =
    (proEtaleRootsOfUnitySheaf X N).obj.map a' ((eX U).symm (r U (eY U x)))
  apply (eX V).injective
  calc
    _ = r V (eY V ((proEtaleRootsOfUnitySheaf Y N).obj.map a x)) :=
      (eX V).apply_symm_apply _
    _ = r V (Additive.ofMul (restrictRootsOfUnity a.unop.left.appTop.hom N
        (Additive.toMul (eY U x)))) := congrArg (r V) (sections_map Y N a x)
    _ = Additive.ofMul (restrictRootsOfUnity a'.unop.left.appTop.hom N
        (Additive.toMul (r U (eY U x)))) := hr (eY U x)
    _ = _ := by
      have h := sections_map X N a' ((eX U).symm (r U (eY U x)))
      exact ((congrArg (fun y ↦ Additive.ofMul
        (restrictRootsOfUnity a'.unop.left.appTop.hom N (Additive.toMul y)))
        ((eX U).apply_symm_apply (r U (eY U x)))).symm.trans h.symm)

/-- Pullback of roots along the fibre-product projection uniquely determines a sheaf map.
Source: Stacks Project, Tag 03PK (auxiliary; not a blueprint node).
Proof: on `V`, pull units back by the global-sections ring map of `pullback.fst V.hom f`.
Ring homomorphisms preserve multiplication, powers and one, so this is a group homomorphism
on roots. The pullback projection commutes with every arrow `V' → V`; functoriality of
global sections gives naturality. The roots-section equivalences and injectivity of their
inclusions imply uniqueness sectionwise, hence uniqueness as a sheaf map. -/
theorem existsUnique_proEtaleRootsOfUnityDirectImageMap {X Y : Scheme.{u}} (f : X ⟶ Y)
    (N : ℕ) :
    ∃! b : proEtaleRootsOfUnitySheaf Y N ⟶
        (proEtaleSheafDirectImage f AddCommGrpCat.{u + 1}).obj
          (proEtaleRootsOfUnitySheaf X N),
      ∀ (V : Y.ProEtᵒᵖ) (x : (proEtaleRootsOfUnitySheaf Y N).obj.obj V),
        proEtaleRootsOfUnitySections X N ((proEtaleBaseChange f).op.obj V)
            (b.hom.app V x) =
          Additive.ofMul (restrictRootsOfUnity
            (pullback.fst V.unop.hom f).appTop.hom N
              (Additive.toMul (proEtaleRootsOfUnitySections Y N V x))) := by
  let b₀ : (proEtaleRootsOfUnitySheaf Y N).obj ⟶
      (proEtaleBaseChange f).op ⋙ (proEtaleRootsOfUnitySheaf X N).obj := {
    app := fun V ↦ by
      let e := proEtaleRootsOfUnitySections X N ((proEtaleBaseChange f).op.obj V)
      exact AddCommGrpCat.ofHom (e.symm.toAddMonoidHom.comp
        ((restrictRootsOfUnity (pullback.fst V.unop.hom f).appTop.hom N).toAdditive.comp
          (proEtaleRootsOfUnitySections Y N V).toAddMonoidHom)),
    naturality := by
      intro U V a
      exact proEtaleRootsOfUnityDirectImageNaturality f N U V a
  }
  let b : proEtaleRootsOfUnitySheaf Y N ⟶
      (proEtaleSheafDirectImage f AddCommGrpCat.{u + 1}).obj
        (proEtaleRootsOfUnitySheaf X N) := ⟨b₀⟩
  refine ⟨b, ?_, ?_⟩
  · intro V x
    exact (proEtaleRootsOfUnitySections X N
      ((proEtaleBaseChange f).op.obj V)).apply_symm_apply _
  · intro c hc
    apply Sheaf.hom_ext
    ext V x
    apply (proEtaleRootsOfUnitySections X N ((proEtaleBaseChange f).op.obj V)).injective
    exact (hc V x).trans
      ((proEtaleRootsOfUnitySections X N
        ((proEtaleBaseChange f).op.obj V)).apply_symm_apply _).symm

/-- The direct-image root map `β`, fixed uniquely by the fibre-product projection formula.
Source: Stacks Project, Tag 03PK (auxiliary; not a blueprint node). -/
noncomputable def proEtaleRootsOfUnityDirectImageMap {X Y : Scheme.{u}} (f : X ⟶ Y)
    (N : ℕ) :
    proEtaleRootsOfUnitySheaf Y N ⟶
      (proEtaleSheafDirectImage f AddCommGrpCat.{u + 1}).obj
        (proEtaleRootsOfUnitySheaf X N) :=
  (existsUnique_proEtaleRootsOfUnityDirectImageMap f N).exists.choose

end AlgebraicGeometry.Scheme
