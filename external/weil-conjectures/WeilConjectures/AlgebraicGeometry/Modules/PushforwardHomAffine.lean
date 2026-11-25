/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Modules.PushforwardHom

/-!
# Morphisms out of a pushforward of the structure sheaf over an affine open

Let `f : X ⟶ Y` be a morphism of schemes, `V` an affine open of `Y` with `f⁻¹V` affine, and `N`
an `𝒪_Y`-module. A morphism `(f_* 𝒪_X)|_V ⟶ N|_V` is determined by its value on the sections over
`V`: over a basic open `D(r) ⊆ V` the sections of `f_* 𝒪_X` are the localization of
`Γ(X, f⁻¹V)` at `f^♯ r`, on which the morphism is determined by linearity, as `r` is a unit there;
and the basic opens of `V` cover every open of `V`.
-/

@[expose] public section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}} (f : X ⟶ Y) {N : Y.Modules}

/-- The sections of a pushforward `f_* M` over `V` are a `Γ(Y, V)`-module through `f^♯`. -/
lemma pushforward_smul_def (M : X.Modules) (V : Y.Opens) (r : Γ(Y, V))
    (m : Γ((pushforward f).obj M, V)) :
    r • m = (show Γ(M, f ⁻¹ᵁ V) from (f.app V r) • (show Γ(M, f ⁻¹ᵁ V) from m)) :=
  rfl

/-- A morphism `(f_* 𝒪_X)|_V ⟶ N|_V`, for `f⁻¹V` affine, is determined over a basic open `D(r)` of
`V` by its value on the sections over `V`: the sections of `f_* 𝒪_X` over `D(r)` are the
localization of `Γ(X, f⁻¹V)` at `f^♯ r`, and `r` is a unit over `D(r)`. -/
lemma restrictOver_pushforward_unit_hom_app_basicOpen_eq {V : Y.Opens}
    (hV' : IsAffineOpen (f ⁻¹ᵁ V))
    {χ₁ χ₂ : (PresheafOfModules.restrictOver Y.sheaf.obj V).obj
        ((pushforward f).obj (SheafOfModules.unit X.ringCatSheaf)).val ⟶
      (PresheafOfModules.restrictOver Y.sheaf.obj V).obj N.val}
    (h : χ₁.app (op (Over.mk (𝟙 V))) = χ₂.app (op (Over.mk (𝟙 V)))) (r : Γ(Y, V)) :
    χ₁.app (op (Over.mk (homOfLE (Y.basicOpen_le r)))) =
      χ₂.app (op (Over.mk (homOfLE (Y.basicOpen_le r)))) := by
  let i : f ⁻¹ᵁ Y.basicOpen r ⟶ f ⁻¹ᵁ V :=
    (TopologicalSpace.Opens.map f.base).map (homOfLE (Y.basicOpen_le r))
  let := (X.presheaf.map i.op).hom.toAlgebra
  have hloc := hV'.isLocalization_of_eq_basicOpen (f.app V r) i (Scheme.preimage_basicOpen f r)
  let g : Over.mk (homOfLE (Y.basicOpen_le r)) ⟶ Over.mk (𝟙 V) :=
    Over.homMk (homOfLE (Y.basicOpen_le r)) (Subsingleton.elim _ _)
  let ρ : Γ(Y, Y.basicOpen r) := Y.presheaf.map (homOfLE (Y.basicOpen_le r)).op r
  ext (b : Γ(X, f ⁻¹ᵁ Y.basicOpen r))
  obtain ⟨⟨b₀, _, n, rfl⟩, hb⟩ := IsLocalization.surj (S := Γ(X, f ⁻¹ᵁ Y.basicOpen r))
    (Submonoid.powers (f.app V r)) b
  have hρ : f.app _ ρ = X.presheaf.map i.op (f.app V r) :=
    ConcreteCategory.congr_hom (f.naturality (homOfLE (Y.basicOpen_le r)).op) r
  have hmid : (f.app _ (ρ ^ n) * b : Γ(X, f ⁻¹ᵁ Y.basicOpen r)) = X.presheaf.map i.op b₀ := by
    rw [map_pow, hρ, ← map_pow, mul_comm]
    exact hb
  have key (χ : (PresheafOfModules.restrictOver Y.sheaf.obj V).obj
        ((pushforward f).obj (SheafOfModules.unit X.ringCatSheaf)).val ⟶
      (PresheafOfModules.restrictOver Y.sheaf.obj V).obj N.val) :
      ρ ^ n • χ.app (op (Over.mk (homOfLE (Y.basicOpen_le r)))) b =
        N.val.map g.op.unop.left.op (χ.app (op (Over.mk (𝟙 V))) b₀) :=
    ((χ.app (op (Over.mk (homOfLE (Y.basicOpen_le r))))).hom.map_smul (ρ ^ n) b).symm.trans
      ((congrArg (χ.app _).hom hmid).trans (PresheafOfModules.naturality_apply χ g.op b₀))
  exact ((Y.toRingedSpace.isUnit_res_basicOpen r).pow n).smul_left_cancel.1
    ((key χ₁).trans (h ▸ (key χ₂).symm))

/-- A morphism `(f_* 𝒪_X)|_V ⟶ N|_V`, for `V` and `f⁻¹V` affine, is determined by its value on
the sections over `V`. -/
lemma restrictOver_pushforward_unit_hom_ext {V : Y.Opens} (hV : IsAffineOpen V)
    (hV' : IsAffineOpen (f ⁻¹ᵁ V))
    {χ₁ χ₂ : (PresheafOfModules.restrictOver Y.sheaf.obj V).obj
        ((pushforward f).obj (SheafOfModules.unit X.ringCatSheaf)).val ⟶
      (PresheafOfModules.restrictOver Y.sheaf.obj V).obj N.val}
    (h : χ₁.app (op (Over.mk (𝟙 V))) = χ₂.app (op (Over.mk (𝟙 V)))) : χ₁ = χ₂ := by
  refine PresheafOfModules.hom_ext fun W ↦ ?_
  ext b
  refine TopCat.Sheaf.eq_of_locally_eq' ⟨N.presheaf, N.isSheaf⟩
    (fun r : {r : Γ(Y, V) // Y.basicOpen r ≤ W.unop.left} ↦ Y.basicOpen r.1) W.unop.left
    (fun r ↦ homOfLE r.2) (fun x hx ↦ ?_) _ _ fun r ↦ ?_
  · obtain ⟨r, hr, hxr⟩ := hV.exists_basicOpen_le ⟨x, hx⟩ (W.unop.hom.le hx)
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨r, hr⟩, hxr⟩
  · let g : Over.mk (homOfLE (Y.basicOpen_le r.1)) ⟶ W.unop :=
      Over.homMk (homOfLE r.2) (Subsingleton.elim _ _)
    refine (PresheafOfModules.naturality_apply χ₁ g.op b).symm.trans ?_
    rw [restrictOver_pushforward_unit_hom_app_basicOpen_eq f hV' h r.1]
    exact PresheafOfModules.naturality_apply χ₂ g.op b

end AlgebraicGeometry.Scheme.Modules
