/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ScalarGlobalSectionsComparison
import WeilConjectures.AlgebraicGeometry.EtaleTensorSections

/-! # Normalized restriction of a projection pullback

Source: Stacks Project, Tags 0096, 0097 and 01CD.
-/

@[expose] public section

universe w
open CategoryTheory Opposite
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section
set_option autoImplicit false
attribute [local irreducible] tensorPullback tensorPullbackObj
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Restriction of a pullback along an open commutative triangle preserves unit sections.
Source: Stacks Project, Tags 0096, 0097 and 01CD.
(blueprint: lem-sc-tensor-pullback-open-triangle).

Proof: use leftAdjointUniq from the restriction adjunction to the chosen tensor-pullback
adjunction for j, then tensorSectionsComp j b, and transport along h. Evaluate the
leftAdjointUniq unit equation at the top open of B. The normalized composition
unit equation then identifies the two successive units with the unit for d.
All top restrictions are retained, so this includes an empty source.
-/
theorem exists_tensorPullback_openTriangle {A B C : Scheme.{w}}
    (j : A ⟶ B) [IsOpenImmersion j] (b : B ⟶ C) (d : A ⟶ C)
    (h : j ≫ b = d) (F : C.Modules) :
    ∃ e : ((tensorPullback b).obj F).restrict j ≅ (tensorPullback d).obj F,
      ∀ (s : Γ(F, ⊤)),
        e.hom.app ⊤
          (((tensorPullback b).obj F).presheaf.map
            (homOfLE (by simp : j ''ᵁ ⊤ ≤ b ⁻¹ᵁ ⊤)).op
            (((Classical.choose (exists_tensorPullbackAdjunction b)).unit.app F).app ⊤ s)) =
          tensorPullbackTopSection d F s := by
  subst d
  let M := (tensorPullback b).obj F
  let aj := Classical.choose (exists_tensorPullbackAdjunction j)
  let ab := Classical.choose (exists_tensorPullbackAdjunction b)
  let ac := Classical.choose (exists_tensorPullbackAdjunction (j ≫ b))
  let er := (restrictAdjunction j).leftAdjointUniq aj
  let ec := tensorSectionsComp j b
  refine ⟨er.app M ≪≫ ec.app F, ?_⟩
  intro s
  have hr := congrArg (fun φ ↦ φ.app ⊤)
    ((restrictAdjunction j).unit_leftAdjointUniq_hom_app aj M)
  have hc := congrArg (fun φ ↦ φ.app ⊤)
    (unit_conjugateEquiv_symm ac (ab.comp aj) (pushforwardComp j b).inv F)
  simp only [Hom.comp_app, pushforward_map_app, restrictAdjunction_unit_app_app] at hr
  simp only [Hom.comp_app, pushforward_map_app, Adjunction.comp_unit_app,
    Functor.comp_map, pushforwardComp_inv_app_app] at hc
  change M.presheaf.map (homOfLE (j.image_preimage_le ⊤)).op ≫
      (er.hom.app M).app ⊤ = (aj.unit.app M).app ⊤ at hr
  change (ac.unit.app F).app ⊤ ≫ 𝟙 _ =
      (ab.unit.app F).app ⊤ ≫ (aj.unit.app M).app ⊤ ≫ (ec.hom.app F).app ⊤ at hc
  erw [Category.comp_id] at hc
  have ht : tensorPullbackTopSection (j ≫ b) F s = (ac.unit.app F).app ⊤ s := by
    change ((tensorPullback (j ≫ b)).obj F).presheaf.map
      (homOfLE (by simp : ⊤ ≤ (j ≫ b) ⁻¹ᵁ ⊤)).op ((ac.unit.app F).app ⊤ s) = _
    have hi : homOfLE (by simp : ⊤ ≤ (j ≫ b) ⁻¹ᵁ ⊤) = 𝟙 _ := rfl
    erw [hi, op_id, ((tensorPullback (j ≫ b)).obj F).presheaf.map_id]
    rfl
  rw [ht]
  change (ec.hom.app F).app ⊤
    ((er.hom.app M).app ⊤
      (M.presheaf.map (homOfLE (by simp : j ''ᵁ ⊤ ≤ b ⁻¹ᵁ ⊤)).op
        ((ab.unit.app F).app ⊤ s))) = (ac.unit.app F).app ⊤ s
  have hs := congrArg (fun z ↦ z ((ab.unit.app F).app ⊤ s)) hr
  change (er.hom.app M).app ⊤
    (M.presheaf.map (homOfLE (by simp : j ''ᵁ ⊤ ≤ b ⁻¹ᵁ ⊤)).op
      ((ab.unit.app F).app ⊤ s)) = (aj.unit.app M).app ⊤ ((ab.unit.app F).app ⊤ s) at hs
  rw [hs]
  exact (congrArg (fun z ↦ z s) hc).symm

end
end AlgebraicGeometry.Scheme.Modules
