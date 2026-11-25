/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Galois.Prorepresentability
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.UniversalCover

/-!
# Lifts of geometric points to universal covers

Let `Y` be a connected quasi-compact quasi-separated scheme, `t : Spec K ⟶ Y` a geometric point
with universal cover `Ỹ_t` (`AlgebraicGeometry.Scheme.UniversalCover.cover`) and
`η : Spec Ω ⟶ Y` a geometric point with values in another separably closed field. A lift
`ξ : Spec Ω ⟶ Ỹ_t` of `η` defines a path `F_t ≅ F_η`
(`AlgebraicGeometry.Scheme.UniversalCover.liftPath`): a point `x ∈ F_t(P)` is the image of the
base point under a unique `Y`-morphism `Ỹ_t ⟶ P`, which maps `ξ` to a point of `F_η(P)`. Any
morphism of fibre functors is an isomorphism, so this is a path.

Two lifts `ξ₁, ξ₂` of `η` to universal covers `Ỹ_{t₁}`, `Ỹ_{t₂}` are related by the transport
along the path `F_{t₁} ≅ F_η ≅ F_{t₂}`
(`AlgebraicGeometry.Scheme.UniversalCover.comp_transport_liftPath`): every lift of `η` is
obtained from a given one by transport along a unique loop, and lifts with values in different
fields are compared through fibre functors. Lifts are compatible with the morphisms
`Ỹ_t ⟶ Ỹ_{t ≫ f}` (`AlgebraicGeometry.Scheme.UniversalCover.liftPath_map`).

These are used to compare the stalks of lisse sheaves at geometric points with values in
different fields, as needed for the inertia invariants at a boundary point (blueprint
`lemma-boundary-stalk--1`).
-/

@[expose] public section

universe u

open CategoryTheory Limits PreGaloisCategory

namespace AlgebraicGeometry.Scheme

open FiniteEtale

namespace FiniteEtale

variable {X Y : Scheme.{u}} {Ω Ω' : Type u} [Field Ω] [IsSepClosed Ω] [Field Ω'] [IsSepClosed Ω']

/-- The path `F_{y ≫ f} ≅ F_{z ≫ f}` induced by a path `τ : F_y ≅ F_z` between geometric points
with values in possibly different fields (`AlgebraicGeometry.Scheme.FiniteEtale.pullbackPathIso`
for different fields). -/
noncomputable def pullbackPathIso' (f : X ⟶ Y) {y : Spec (.of Ω) ⟶ X} {z : Spec (.of Ω') ⟶ X}
    (τ : fiber y ≅ fiber z) : fiber (y ≫ f) ≅ fiber (z ≫ f) :=
  (pullbackFiberIso f y).symm ≪≫ Functor.isoWhiskerLeft (pullback f) τ ≪≫ pullbackFiberIso f z

lemma pullbackPathIso'_hom_app_left (f : X ⟶ Y) {y : Spec (.of Ω) ⟶ X} {z : Spec (.of Ω') ⟶ X}
    (τ : fiber y ≅ fiber z) (P : Y.FiniteEtale) (x : (fiber (y ≫ f)).obj P) :
    ((pullbackPathIso' f τ).hom.app P x).left =
      (τ.hom.app ((pullback f).obj P) ((pullbackFiberIso f y).inv.app P x)).left ≫
        Limits.pullback.fst P.obj.hom f :=
  rfl

lemma pullbackPathIso'_trans (f : X ⟶ Y) {Ω'' : Type u} [Field Ω''] [IsSepClosed Ω'']
    {y : Spec (.of Ω) ⟶ X} {z : Spec (.of Ω') ⟶ X} {w : Spec (.of Ω'') ⟶ X}
    (τ : fiber y ≅ fiber z) (τ' : fiber z ≅ fiber w) :
    pullbackPathIso' f (τ ≪≫ τ') = pullbackPathIso' f τ ≪≫ pullbackPathIso' f τ' := by
  ext P x
  simp [pullbackPathIso']

lemma pullbackPathIso'_symm (f : X ⟶ Y) {y : Spec (.of Ω) ⟶ X} {z : Spec (.of Ω') ⟶ X}
    (τ : fiber y ≅ fiber z) : pullbackPathIso' f τ.symm = (pullbackPathIso' f τ).symm := by
  ext P x
  simp [pullbackPathIso']

lemma pullbackPathIso'_eq (f : X ⟶ Y) {y z : Spec (.of Ω) ⟶ X} (τ : fiber y ≅ fiber z) :
    pullbackPathIso' f τ = pullbackPathIso f τ :=
  rfl

end FiniteEtale

namespace UniversalCover

variable {Y : Scheme.{u}} [ConnectedSpace Y] [CompactSpace Y] [QuasiSeparatedSpace Y]
  {K : Type u} [Field K] [IsSepClosed K] {Ω : Type u} [Field Ω] [IsSepClosed Ω]

/-- The morphism of fibre functors `F_t ⟶ F_η` attached to a lift `ξ : Spec Ω ⟶ Ỹ_t` of `η`:
`x ↦ ξ ≫ toObj x`. -/
noncomputable def liftPathHom (t : Spec (.of K) ⟶ Y) {η : Spec (.of Ω) ⟶ Y}
    (ξ : Spec (.of Ω) ⟶ cover t) (hξ : ξ ≫ proj t = η) : fiber t ⟶ fiber η where
  app P := FintypeCat.homMk fun x ↦ fiberMk η P (ξ ≫ toObj t P x)
    (by rw [Category.assoc, toObj_hom, hξ])
  naturality P Q g := by
    ext x
    refine fiber_ext η ?_
    change ξ ≫ toObj t Q ((fiber t).map g x) = (ξ ≫ toObj t P x) ≫ g.hom.left
    rw [Category.assoc, toObj_comp]

instance (t : Spec (.of K) ⟶ Y) {η : Spec (.of Ω) ⟶ Y} (ξ : Spec (.of Ω) ⟶ cover t)
    (hξ : ξ ≫ proj t = η) : IsIso (liftPathHom t ξ hξ) := by
  obtain ⟨τ⟩ := nonempty_iso_of_fiberFunctor (fiber η) (fiber t)
  have : IsIso (liftPathHom t ξ hξ ≫ τ.hom) := FibreFunctor.end_isIso (fiber t) (.of _)
  exact IsIso.of_isIso_comp_right _ τ.hom

/-- **The path of a lift.** A lift `ξ : Spec Ω ⟶ Ỹ_t` of a geometric point `η` defines a path
`F_t ≅ F_η`, sending `x ∈ F_t(P)` to the image of `ξ` under the `Y`-morphism `Ỹ_t ⟶ P`
corresponding to `x`. -/
noncomputable def liftPath (t : Spec (.of K) ⟶ Y) {η : Spec (.of Ω) ⟶ Y}
    (ξ : Spec (.of Ω) ⟶ cover t) (hξ : ξ ≫ proj t = η) : fiber t ≅ fiber η :=
  asIso (liftPathHom t ξ hξ)

@[simp]
lemma liftPath_hom_app_left (t : Spec (.of K) ⟶ Y) {η : Spec (.of Ω) ⟶ Y}
    (ξ : Spec (.of Ω) ⟶ cover t) (hξ : ξ ≫ proj t = η) (P : Y.FiniteEtale)
    (x : (fiber t).obj P) : ((liftPath t ξ hξ).hom.app P x).left = ξ ≫ toObj t P x :=
  rfl

/-- The path of the base point is the identity. -/
lemma liftPath_pt (t : Spec (.of K) ⟶ Y) :
    liftPath t (pt t) (pt_proj t) = Iso.refl _ := by
  ext P x
  exact fiber_ext t (pt_toObj t P x)

/-- **Lifts are related by transport.** Two lifts `ξ₁ : Spec Ω ⟶ Ỹ_{t₁}` and
`ξ₂ : Spec Ω ⟶ Ỹ_{t₂}` of the same geometric point are related by the transport along the path
`F_{t₁} ≅ F_η ≅ F_{t₂}`. -/
lemma comp_transport_liftPath {t₁ t₂ : Spec (.of K) ⟶ Y} {η : Spec (.of Ω) ⟶ Y}
    (ξ₁ : Spec (.of Ω) ⟶ cover t₁) (hξ₁ : ξ₁ ≫ proj t₁ = η)
    (ξ₂ : Spec (.of Ω) ⟶ cover t₂) (hξ₂ : ξ₂ ≫ proj t₂ = η) :
    ξ₁ ≫ (transport (liftPath t₁ ξ₁ hξ₁ ≪≫ (liftPath t₂ ξ₂ hξ₂).symm)).hom = ξ₂ := by
  refine hom_ext t₂ fun P x ↦ ?_
  rw [Category.assoc, transport_hom, transportHom_toObj]
  have h := liftPath_hom_app_left t₁ ξ₁ hξ₁ P
    ((liftPath t₁ ξ₁ hξ₁ ≪≫ (liftPath t₂ ξ₂ hξ₂).symm).inv.app P x)
  rw [← h, ← liftPath_hom_app_left t₂ ξ₂ hξ₂ P x]
  congr 1
  simp only [Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app, FintypeCat.comp_apply]
  exact ConcreteCategory.congr_hom ((liftPath t₁ ξ₁ hξ₁).inv_hom_id_app P) _

section Map

variable {Y' : Scheme.{u}} [ConnectedSpace Y'] [CompactSpace Y'] [QuasiSeparatedSpace Y']
  (f : Y' ⟶ Y)

/-- **Lifts and the morphisms of universal covers.** The image of a lift `ξ` of `η` under
`Ỹ_t ⟶ Ỹ_{t ≫ f}` is a lift of `η ≫ f`, whose path is the path induced by that of `ξ`. -/
lemma liftPath_map (t : Spec (.of K) ⟶ Y') {η : Spec (.of Ω) ⟶ Y'}
    (ξ : Spec (.of Ω) ⟶ cover t) (hξ : ξ ≫ proj t = η)
    (h : (ξ ≫ map f t) ≫ proj (t ≫ f) = η ≫ f) :
    liftPath (t ≫ f) (ξ ≫ map f t) h = pullbackPathIso' f (liftPath t ξ hξ) := by
  ext P x
  refine fiber_ext (η ≫ f) ?_
  rw [liftPath_hom_app_left, pullbackPathIso'_hom_app_left, liftPath_hom_app_left,
    Category.assoc, map_toObj]
  rfl

end Map

end UniversalCover

end AlgebraicGeometry.Scheme
