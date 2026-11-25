/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import WeilConjectures.AlgebraicGeometry.DerivedHomMayerVietoris

/-! # Scalar action calculation for an affine chart -/

@[expose] public section
universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false in
/-- The chart ring map agrees with the pushforward ring map on the top section.
Source: Stacks Project, Tag 0098 and Tag 01IB.
The proof applies the chart ring isomorphism, uses naturality and
`isoSpec_hom_appTop`, then composes the restriction maps between opens. -/
private theorem affine_chart_scalar_transport_ring_compatibility (X : Scheme.{u}) (U : X.Opens)
    (hU : IsAffineOpen U) (a : Γ(X, U)) :
    let W := (TopologicalSpace.Opens.overEquivalence U).functor.obj ((Over.star U).obj U)
    (Spec Γ(X, U)).presheaf.map (hU.isoSpec.hom ''ᵁ W).leTop.op
      ((ΓSpecIso Γ(X, U)).inv a) =
    (hU.isoSpec.hom.appIso W).inv
      (((TopologicalSpace.Opens.sheafRestrictSheafEquivOver U).inv.app
        X.ringCatSheaf).hom.app (.op ((Over.star U).obj U))
        (((moduleRings X.toRingedSpace).obj.map Limits.prod.snd.op) a)) := by
  dsimp only
  apply (ConcreteCategory.isIso_iff_bijective
    (hU.isoSpec.hom.appIso _).hom).mp (by infer_instance) |>.injective
  simp only [Iso.inv_hom_id_apply]
  simp only [← ConcreteCategory.comp_apply, Hom.appIso_hom', Category.assoc,
    Hom.map_appLE]
  rw [Hom.appLE, ← Hom.appTop, IsAffineOpen.isoSpec_hom_appTop]
  simp only [← Category.assoc]
  let V := (Over.star U).obj U
  let i := (TopologicalSpace.Opens.overEquivalence U).unitIso.inv.app V
  have h := ConcreteCategory.congr_hom
    (X.presheaf.map_comp Limits.prod.snd.op i.left.op) a
  convert h using 1
  · rfl
  · simp only [Iso.inv_hom_id, Category.id_comp]
    change X.presheaf.map _ (X.presheaf.map _ a) = X.presheaf.map _ a
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
    congr 2
  · rfl


set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Transport along an affine chart and the slice equivalence carries the
coordinate-ring scalar action to the action on sections over the chart.
Source: Stacks Project, Tag 0098 (restriction of sheaves of modules),
Tag 01HV, Lemma 26.5.4 (7), and Tag 01IB.
(blueprint: lem-sc-affine-chart-scalar-transport).

Proof: Restriction along isoSpec evaluates a section map at the image open,
with scalars restricted through the inverse structure-ring isomorphism.
The inverse slice equivalence evaluates at the open of U corresponding to
the slice object U times U. Ordinary direct image uses the second projection
for its ring map. The canonical Spec scalar, pulled back along isoSpec, is
the restriction of a: on the top open this is isoSpec_hom_appTop and the
inverse identities of GammaSpecIso and U.topIso; on smaller opens it follows
by naturality. Thus the hypothesized scalar action becomes the restriction
of a along the second projection, which is precisely the scalar action in
the pushforward module. This works for arbitrary sheaves and their maps;
it needs neither a regular-module presentation nor a point or stalk. -/
theorem affine_chart_scalar_transport (X : Scheme.{u}) (U : X.Opens)
    (hU : IsAffineOpen U) (a : Γ(X, U))
    (M : (Spec Γ(X, U)).Modules) (f : M ⟶ M)
    (hf : ∀ (V : (Spec Γ(X, U)).Opens) (s : Γ(M, V)),
      (f.val.app (.op V)) s = a • s) :
    let T := Modules.restrictFunctor hU.isoSpec.hom ⋙ (Modules.overEquiv U).inverse
    let P := SheafOfModules.pushforward.{u}
      (SheafOfModules.pushforwardOver (R := moduleRings X.toRingedSpace) U)
    ∀ m : (P.obj (T.obj M)).val.obj (.op U),
      (P.map (T.map f)).val.app (.op U) m = a • m := by
  dsimp
  intro m
  change f.val.app _ m = _
  rw [hf]
  simp only [Modules.smul_Spec_def]
  rw [ModuleCat.restrictScalars.smul_def]
  congr 1
  convert affine_chart_scalar_transport_ring_compatibility X U hU a using 1 <;> rfl

end AlgebraicGeometry.Scheme
