/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleSetConstantPullbackComparison
public import WeilConjectures.AlgebraicGeometry.EtaleSetInverseImageCompositionUnits
import WeilConjectures.Mathlib.CategoryTheory.MorphismProperty.OverAdjunction

/-! # Identity transport of a map out of a constant sheaf

Source: Stacks Project, Tags 03CB, 03CC, and 03P5.
(blueprint: lem-weil-pbc-etale-set-constant-transport-identity).
-/

@[expose] public section

universe u
open CategoryTheory Opposite
namespace AlgebraicGeometry

private instance transportIdentity_isContinuous {S T : Scheme.{u}} (f : T ⟶ S) :
    (MorphismProperty.Over.pullback @Etale ⊤ f).IsContinuous
      S.smallEtaleTopology T.smallEtaleTopology := Etale.isContinuous_overPullback f

private noncomputable def setAdj {S T : Scheme.{u}} (f : T ⟶ S) :=
  Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (MorphismProperty.Over.pullback @Etale ⊤ f) (Type (u + 1))
    S.smallEtaleTopology T.smallEtaleTopology

private noncomputable def pushId (P : Scheme.{u}) :=
  Functor.sheafPushforwardContinuousId'
    (MorphismProperty.Over.pullbackId @Etale ⊤ P) (Type (u + 1)) P.smallEtaleTopology

private noncomputable def pullId (P : Scheme.{u}) :
    Scheme.etaleSetPullback (𝟙 P) ≅ 𝟭 _ :=
  ((setAdj (𝟙 P)).ofNatIsoRight (pushId P)).leftAdjointUniq Adjunction.id

private lemma pullId_unit (P : Scheme.{u})
    (F : Sheaf P.smallEtaleTopology (Type (u + 1))) :
    (setAdj (𝟙 P)).unit.app F ≫
      ((MorphismProperty.Over.pullback @Etale ⊤ (𝟙 P)).sheafPushforwardContinuous
        (Type (u + 1)) P.smallEtaleTopology P.smallEtaleTopology).map
          ((pullId P).hom.app F) = (pushId P).inv.app F := by
  have h := Adjunction.unit_leftAdjointUniq_hom_app
    ((setAdj (𝟙 P)).ofNatIsoRight (pushId P)) Adjunction.id F
  simp only [pullId] at h ⊢
  simp only [Adjunction.ofNatIsoRight_unit, NatTrans.comp_app,
    Functor.whiskerLeft_app, Adjunction.id_unit, NatTrans.id_app] at h
  rw [Category.assoc, ← (pushId P).hom.naturality] at h
  simpa only [Functor.id_obj, Category.assoc, Iso.hom_inv_id_app,
    Category.comp_id, Category.id_comp]
    using congrArg (fun t ↦ t ≫ (pushId P).inv.app F) h

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private lemma comp_id (S P : Scheme.{u}) (s : P ⟶ S)
    (F : Sheaf S.smallEtaleTopology (Type (u + 1))) :
    ((Classical.choose etaleSetInverseImageCompositionUnits.2.2)
      S P P s (𝟙 P)).hom.app F =
      (pullId P).hom.app ((Scheme.etaleSetPullback s).obj F) ≫
        eqToHom (congrArg
          (fun k : P ⟶ S ↦ (Scheme.etaleSetPullback k).obj F)
          (Category.id_comp s)).symm := by
  symm
  apply (Classical.choose_spec etaleSetInverseImageCompositionUnits.2.2).2.1
  intro U t
  have h := congrArg (fun k ↦ k.hom.app
    (op ((MorphismProperty.Over.pullback @Etale ⊤ s).obj U))
      (((setAdj s).unit.app F).hom.app (op U) t))
    (pullId_unit P ((Scheme.etaleSetPullback s).obj F))
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    Functor.sheafPushforwardContinuous_map_hom_app] at h
  have aux (k : P ⟶ S) (hk : k = s) :
      (((pullId P).hom.app ((Scheme.etaleSetPullback s).obj F) ≫
        eqToHom (congrArg (fun a ↦ (Scheme.etaleSetPullback a).obj F) hk.symm)).hom.app
          (op ((MorphismProperty.Over.pullback @Etale ⊤ (𝟙 P)).obj
            ((MorphismProperty.Over.pullback @Etale ⊤ s).obj U))))
        ((((setAdj (𝟙 P)).unit.app ((Scheme.etaleSetPullback s).obj F)).hom.app
          (op ((MorphismProperty.Over.pullback @Etale ⊤ s).obj U)))
            (((setAdj s).unit.app F).hom.app (op U) t)) =
      ((Scheme.etaleSetPullback k).obj F).obj.map
        ((MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤) (𝟙 P) s k
          (hk.trans (Category.id_comp s).symm)).inv.app U).op
        (((setAdj k).unit.app F).hom.app (op U) t) := by
    subst k
    simp only [MorphismProperty.Over.pullbackComp_id_left]
    convert h using 1 <;> simp [pushId]
    all_goals rfl
  exact aux (𝟙 P ≫ s) (Category.id_comp s)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private lemma constant_id (P : Scheme.{u}) (A : Type (u + 1)) :
    (etaleSetConstantPullbackComparison (𝟙 P)).hom.app A =
      (pullId P).hom.app ((constantSheaf P.smallEtaleTopology (Type (u + 1))).obj A) := by
  let adjC := constantSheafAdj P.smallEtaleTopology (Type (u + 1))
    CategoryTheory.Limits.terminalIsTerminal
  let adj := adjC.comp (setAdj (𝟙 P))
  unfold etaleSetConstantPullbackComparison
  apply (adj.homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit]
  let b := MorphismProperty.Over.pullback @Etale ⊤ (𝟙 P)
  let e : b.sheafPushforwardContinuous (Type (u + 1))
      P.smallEtaleTopology P.smallEtaleTopology ⋙
        (sheafSections P.smallEtaleTopology (Type (u + 1))).obj
          (op (CategoryTheory.Limits.terminal P.Etale)) ≅
      (sheafSections P.smallEtaleTopology (Type (u + 1))).obj
        (op (CategoryTheory.Limits.terminal P.Etale)) :=
    NatIso.ofComponents
      (fun H ↦ H.obj.mapIso (CategoryTheory.Limits.PreservesTerminal.iso b).op.symm)
      (fun α ↦ (α.hom.naturality _).symm)
  have hc := Adjunction.unit_leftAdjointUniq_hom_app
    (adj.ofNatIsoRight e) adjC A
  change adj.unit.app A ≫ _ = adj.unit.app A ≫ _
  have he (H : Sheaf P.smallEtaleTopology (Type (u + 1))) :
      e.hom.app H =
        ((sheafSections P.smallEtaleTopology (Type (u + 1))).obj
          (op (CategoryTheory.Limits.terminal P.Etale))).map ((pushId P).hom.app H) := by
    have ht : CategoryTheory.Limits.PreservesTerminal.iso b =
        (MorphismProperty.Over.pullbackId @Etale ⊤ P).app
          (CategoryTheory.Limits.terminal P.Etale) := by
      apply Iso.ext
      exact CategoryTheory.Limits.terminalIsTerminal.hom_ext _ _
    simp [e, ht, pushId, Functor.sheafPushforwardContinuousId',
      Functor.sheafPushforwardContinuousIso, Functor.sheafPushforwardContinuousNatTrans]
  simp only [Adjunction.ofNatIsoRight_unit, NatTrans.comp_app,
    Functor.whiskerLeft_app, Category.assoc] at hc
  rw [← e.hom.naturality] at hc
  have hp := pullId_unit P ((constantSheaf P.smallEtaleTopology (Type (u + 1))).obj A)
  apply (cancel_mono (e.hom.app
    ((constantSheaf P.smallEtaleTopology (Type (u + 1))).obj A))).1
  rw [Category.assoc]
  refine hc.trans ?_
  rw [he]
  simp only [adj, Adjunction.comp_unit_app, Functor.comp_map, Category.assoc,
    ← Functor.map_comp]
  simp only [← Category.assoc]
  rw [hp]
  simp

/-- Transporting a map from a constant sheaf along the identity changes only
its target by the identity-composition cast. The map need not be invertible.

Source: Stacks Project, Tags 03CB, 03CC, and 03P5.
(blueprint: lem-weil-pbc-etale-set-constant-transport-identity).

Proof: the inverse-image adjunction for the identity is identified with the identity
adjunction by restriction along the canonical isomorphism from base change by the
identity to the identity functor. Its unit equation identifies the chosen composition
comparison with this identity comparison on the inverse image of F: both have the
same value on every twice unit-pulled section, so fixed-sheaf uniqueness in
etaleSetInverseImageCompositionUnits applies. The constant comparison is constructed
by uniqueness of left adjoints and therefore satisfies the same identity unit equation
on the constant sheaf. Naturality of the identity comparison with respect to tau
cancels the two identity comparisons. The only remaining map is transport from s to
identity composed with s, which is exactly the inverse of the displayed eqToHom. -/
theorem etaleSetConstantTransportIdentity
    (S P : Scheme.{u}) (s : P ⟶ S)
    (F : Sheaf S.smallEtaleTopology (Type (u + 1))) (A : Type (u + 1))
    (τ : (constantSheaf P.smallEtaleTopology (Type (u + 1))).obj A ⟶
      (Scheme.etaleSetPullback s).obj F) :
    (etaleSetConstantPullbackComparison (𝟙 P)).inv.app A ≫
        (Scheme.etaleSetPullback (𝟙 P)).map τ ≫
        ((Classical.choose etaleSetInverseImageCompositionUnits.2.2)
          S P P s (𝟙 P)).hom.app F =
      τ ≫ eqToHom (congrArg
        (fun k : P ⟶ S ↦ (Scheme.etaleSetPullback k).obj F)
        (Category.id_comp s)).symm := by
  rw [comp_id]
  rw [(pullId P).hom.naturality_assoc τ]
  simp only [Functor.id_map]
  rw [← constant_id P A]
  simp

end AlgebraicGeometry
