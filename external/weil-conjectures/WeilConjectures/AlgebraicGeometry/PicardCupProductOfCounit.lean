/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PicardCupProductMap

/-! # An invertible counit preserves perfectness of a pushed-forward pairing

Source: Stacks Project, Tag 0BDP, final paragraph, the converse dual-basis calculation.
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory MonoidalClosed

namespace AlgebraicGeometry.Scheme.Modules

@[reassoc]
private theorem picardTensorObjIso_natural_right
    {X Y : Scheme.{u}} (p : X ⟶ Y) (N : Y.Modules) {P Q : Y.Modules} (a : P ⟶ Q) :
    (tensorPullback p).map (N ◁ a) ≫ (picardTensorObjIso p N Q).hom =
      (picardTensorObjIso p N P).hom ≫ (tensorPullback p).obj N ◁
        (tensorPullback p).map a := by
  simp only [picardTensorObjIso, Iso.trans_hom, Iso.symm_hom, tensorIso_hom,
    Category.assoc]
  erw [(picardTensorComparison p).hom.naturality_assoc]
  simp only [Functor.Monoidal.μIso_inv]
  rw [← Functor.OplaxMonoidal.δ_natural_right_assoc]
  simp only [tensorHom_def, Category.assoc]
  erw [whisker_exchange_assoc ((picardTensorComparison p).app N).inv
    ((pullback p).map a)]
  erw [← whiskerLeft_comp]
  erw [(picardTensorComparison p).inv.naturality a]
  simp only [whiskerLeft_comp]
  rfl

/-- If a pairing on X is perfect and the counit at its first factor is invertible,
its pushforward pairing is perfect when the structure-sheaf unit is invertible.
No finite local freeness or rank condition on the direct image is required.

Source: Stacks Project, Tag 0BDP, final paragraph, converse implication.
(blueprint: lem-sc-picard-perfect-pairing-of-counit)

Proof: For each Y-module P, adjunction identifies maps P to p_*D with maps p^*P
to D. Perfectness identifies the latter with maps M tensor p^*P to O_X.
Use the invertible counit to replace M by p^*p_*M, and the tensor comparison to
replace this tensor product by p^*(p_*M tensor P). The unit comparison and
adjunction then identify these maps with maps p_*M tensor P to p_*p^*O_Y.
The invertible structure-sheaf unit identifies the last target with O_Y.
Transposition now gives maps P to dual(p_*M). This is a chain of bijections.
Its section formula, or naturality of the tensor comparison and adjunction,
says that it sends a to a followed by the cup transpose. Yoneda therefore makes
the cup transpose invertible. This works for arbitrary modules P and for empty
schemes and zero objects. -/
theorem isIso_curry_picardPushforwardPairing_of_isIso_counit
    {X Y : Scheme.{u}} (p : X ⟶ Y)
    (hO : IsIso ((Classical.choose (exists_tensorPullbackAdjunction p)).unit.app
      (SheafOfModules.unit Y.ringCatSheaf)))
    (M D : X.Modules) (ev : M ⊗ D ⟶ SheafOfModules.unit X.ringCatSheaf)
    (hev : IsIso (curry ev))
    (hε : IsIso ((Classical.choose (exists_tensorPullbackAdjunction p)).counit.app M)) :
    IsIso (curry (picardPushforwardPairing p hO M D ev)) := by
  let adj := Classical.choose (exists_tensorPullbackAdjunction p)
  let N := (pushforward p).obj M
  let := hO
  let := hev
  let := hε
  rw [isIso_iff_yoneda_map_bijective]
  intro P
  let e : (P ⟶ (pushforward p).obj D) ≃ (P ⟶ dual N) :=
    ((adj.homEquiv P D).symm.trans
      (Iso.homCongr (Iso.refl _) (asIso (curry ev)))).trans
      (((ihom.adjunction M).homEquiv _ _).symm.trans
        ((Iso.homCongr ((asIso (adj.counit.app M)).symm ⊗ᵢ Iso.refl _) (Iso.refl _)).trans
          ((Iso.homCongr (picardTensorObjIso p N P).symm (Iso.refl _)).trans
            ((Iso.homCongr (Iso.refl _) (picardTensorUnitIso p).symm).trans
              ((adj.homEquiv _ _).trans
                ((Iso.homCongr (Iso.refl _) (asIso (adj.unit.app
                  (SheafOfModules.unit Y.ringCatSheaf))).symm).trans
                    ((ihom.adjunction N).homEquiv _ _)))))))
  have he (a : P ⟶ (pushforward p).obj D) :
      e a = a ≫ curry (picardPushforwardPairing p hO M D ev) := by
    change curry (adj.homEquiv _ _
      (((picardTensorObjIso p N P).hom ≫
        ((adj.counit.app M ⊗ₘ 𝟙 _) ≫
          uncurry ((adj.homEquiv P D).symm a ≫ curry ev))) ≫
            (picardTensorUnitIso p).inv) ≫ inv (adj.unit.app _)) = _
    rw [uncurry_natural_left, uncurry_curry]
    rw [← curry_natural_left]
    apply congrArg curry
    rw [Adjunction.homEquiv_counit]
    simp only [tensorHom_def, Category.assoc, whiskerLeft_comp, whiskerLeft_id,
      Category.id_comp, Functor.id_obj]
    erw [← whisker_exchange_assoc (adj.counit.app M) ((tensorPullback p).map a)]
    erw [← picardTensorObjIso_natural_right_assoc]
    rw [adj.homEquiv_naturality_left, adj.homEquiv_naturality_right]
    simp only [picardPushforwardPairing, adj, N, tensorHom_def, Category.assoc,
      Adjunction.homEquiv_unit, Functor.map_comp, Functor.id_obj]
  have he' : (fun a ↦ a ≫ curry (picardPushforwardPairing p hO M D ev)) = e :=
    funext fun a ↦ (he a).symm
  rw [he']
  exact e.bijective

end AlgebraicGeometry.Scheme.Modules
