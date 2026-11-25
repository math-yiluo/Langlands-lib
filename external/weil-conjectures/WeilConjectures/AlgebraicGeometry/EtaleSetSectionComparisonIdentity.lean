/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleSetSectionComparison
import WeilConjectures.AlgebraicGeometry.EtaleSetInverseImageCompositionUnits

/-! # Identity calculation for étale section comparisons

Source: Stacks Project, Sites Tags 03CB and 03CC, and Étale Cohomology Tag 09YQ.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

private noncomputable abbrev L {S T : Scheme.{u}} (e : T ⟶ S) :=
  Scheme.etaleSetPullback e

private noncomputable abbrev b {S T : Scheme.{u}} (e : T ⟶ S) :=
  MorphismProperty.Over.pullback @Etale ⊤ e

private noncomputable def push {S T : Scheme.{u}} (e : T ⟶ S) :=
  Functor.sheafPushforwardContinuous (b e) (Type (u + 1))
    (S.smallGrothendieckTopology @Etale) (T.smallGrothendieckTopology @Etale)

private noncomputable def adj {S T : Scheme.{u}} (e : T ⟶ S) : L e ⊣ push e :=
  Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (b e) (Type (u + 1))
    (S.smallGrothendieckTopology @Etale) (T.smallGrothendieckTopology @Etale)

private noncomputable def pushId (S : Scheme.{u}) : push (𝟙 S) ≅ 𝟭 _ :=
  Functor.sheafPushforwardContinuousId' (MorphismProperty.Over.pullbackId @Etale ⊤ S)
    (Type (u + 1)) (S.smallGrothendieckTopology @Etale)


/-- The scheme-level identity calculation, before specializing to a diagram.

Source: Stacks Project, Sites Tags 03CB and 03CC (composition of morphisms of sites),
with the identity adjunction and fibre-product pasting as in Étale Cohomology Tag 09YQ.
(blueprint: lem-weil-pbc-sets-section-comparison-identity).

Proof: identify base change by the identity of `S` with the identity functor using
`MorphismProperty.Over.pullbackId`. Restriction along this isomorphism identifies the
right adjoint with the identity. Uniqueness of left adjoints therefore identifies
inverse image by the identity with the identity, compatibly with its adjunction unit.
For the fixed sheaf `G`, the composition of this identification on the inverse image
by `f` with the inverse-image composition isomorphism has the same unit equation as
the identity morphism of that inverse image: naturality of the identity identification
moves the `f`-unit through it, and the two identity fibre-product identifications cancel.
The fixed-sheaf uniqueness clause of `etaleSetInverseImageCompositionUnits` identifies
these sheaf morphisms. Evaluate at the base change of `U` by `f`. In the definition of
`etaleSetSectionComparison`, the remaining unit and restriction along the identity
pasting isomorphism cancel by the unit-compatible identity adjunction. Equality
transport is independent of its proof. Thus the resulting section map is the identity.
This argument also works for an empty scheme or a sheaf with no sections: it is an
identity of sheaf morphisms, evaluated at an arbitrary site object. -/
theorem etaleSetSectionComparisonIdentity
    {R S : Scheme.{u}} (f : S ⟶ R)
    (G : Sheaf R.smallEtaleTopology (Type (u + 1))) (U : R.Etale) :
    etaleSetSectionComparison (𝟙 S) f f (Category.id_comp f) G U = 𝟙 _ := by
  let F := (L f).obj G
  let c := Classical.choose etaleSetInverseImageCompositionUnits.2.2 R S S f (𝟙 S)
  let t : (L (𝟙 S)).obj F ⟶ F := c.hom.app G ≫
    eqToHom (congrArg (fun a : S ⟶ R ↦ (L a).obj G) (Category.id_comp f))
  let p : F ⟶ F := (adj (𝟙 S)).unit.app F ≫ (push (𝟙 S)).map t ≫
    (pushId S).hom.app F
  have hp : p = 𝟙 F := by
    apply (adj f).homEquiv G F |>.injective
    rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
    ext V s
    obtain ⟨V⟩ := V
    have hc := (Classical.choose_spec etaleSetInverseImageCompositionUnits.2.2).1
      R S S f (𝟙 S) G V s
    have hm := congrArg
      (fun z ↦ F.obj.map ((MorphismProperty.Over.pullbackId @Etale ⊤ S).inv.app
        ((b f).obj V)).op z) hc
    simp only [MorphismProperty.Over.pullbackComp_id_left,
      MorphismProperty.Over.pullbackCongr_refl, Iso.trans_inv,
      NatTrans.comp_app, Functor.isoWhiskerLeft_inv, Functor.whiskerLeft_app,
      Iso.symm_inv, Functor.rightUnitor_hom_app, Iso.refl_inv,
      NatTrans.id_app] at hm
    have hcancel (z : F.obj.obj (op ((b f).obj V))) :
        F.obj.map ((MorphismProperty.Over.pullbackId @Etale ⊤ S).inv.app
          ((b f).obj V)).op
          (F.obj.map ((MorphismProperty.Over.pullbackId @Etale ⊤ S).hom.app
            ((b f).obj V)).op z) = z := by
      rw [← comp_apply, ← Functor.map_comp, ← op_comp, Iso.inv_hom_id_app,
        op_id, CategoryTheory.Functor.map_id, id_apply]
    change _ = F.obj.map ((MorphismProperty.Over.pullbackId @Etale ⊤ S).inv.app
      ((b f).obj V)).op
      (F.obj.map ((MorphismProperty.Over.pullbackId @Etale ⊤ S).hom.app
        ((b f).obj V)).op (((adj f).unit.app G).hom.app (op V) s)) at hm
    rw [hcancel] at hm
    simp only [p, t, c, F, pushId, push, adj, Functor.map_comp,
      Functor.sheafPushforwardContinuous_map_hom_app,
      Functor.sheafPushforwardContinuousId'_hom_app_hom_app,
      ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
      CategoryTheory.Functor.map_id, ObjectProperty.FullSubcategory.id_hom,
      NatTrans.id_app, eqToHom_refl, Category.comp_id]
    dsimp
    convert hm using 1
    all_goals rfl
  have hpV := NatTrans.congr_app (congrArg (fun q ↦ q.hom) hp) (op ((b f).obj U))
  dsimp [p, t, c, F, pushId, push, adj] at hpV
  unfold etaleSetSectionComparison
  simpa [Functor.map_comp, pushId, push,
    MorphismProperty.Over.pullbackComp_id_left,
    Functor.sheafPushforwardContinuousId'_hom_app_hom_app] using hpV

end AlgebraicGeometry
