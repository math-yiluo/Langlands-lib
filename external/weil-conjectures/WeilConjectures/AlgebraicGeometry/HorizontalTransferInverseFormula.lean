/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.HorizontalDualityMateComparisons
public import WeilConjectures.AlgebraicGeometry.QCohInverseBaseChangeMate

/-! # Canonical isomorphism transfer from its inverse formula

Source: Stacks Project, Tags 0D5S, 0D5T and 08HY.
(blueprint: lem-sc-horizontal-transfer-inverse-formula).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.TwoSquare
namespace AlgebraicGeometry

private theorem restricted_unit_map
    {C E : Type*} [Category* C] [Category* E]
    (P : ObjectProperty C) (Q : ObjectProperty E)
    (L : C ⥤ E) (R : E ⥤ C) (adj : L ⊣ R)
    (hL : ∀ X : P.FullSubcategory, Q (L.obj X.obj))
    (hR : ∀ X : Q.FullSubcategory, P (R.obj X.obj))
    (X : P.FullSubcategory) :
    P.ι.map ((adj.restrictFullyFaithful P.fullyFaithfulι Q.fullyFaithfulι
      (L := Q.lift (P.ι ⋙ L) hL) (R := P.lift (Q.ι ⋙ R) hR)
      (Iso.refl _) (Iso.refl _)).unit.app X) = adj.unit.app X.obj := by
  rw [Adjunction.map_restrictFullyFaithful_unit_app]
  dsimp only [Iso.refl_hom, NatTrans.id_app]
  dsimp only [Functor.comp_obj, ObjectProperty.ι_obj, ObjectProperty.lift]
  erw [R.map_id, Category.comp_id, Category.comp_id]

private theorem restricted_counit_map
    {C E : Type*} [Category* C] [Category* E]
    (P : ObjectProperty C) (Q : ObjectProperty E)
    (L : C ⥤ E) (R : E ⥤ C) (adj : L ⊣ R)
    (hL : ∀ X : P.FullSubcategory, Q (L.obj X.obj))
    (hR : ∀ X : Q.FullSubcategory, P (R.obj X.obj))
    (X : Q.FullSubcategory) :
    Q.ι.map ((adj.restrictFullyFaithful P.fullyFaithfulι Q.fullyFaithfulι
      (L := Q.lift (P.ι ⋙ L) hL) (R := P.lift (Q.ι ⋙ R) hR)
      (Iso.refl _) (Iso.refl _)).counit.app X) = adj.counit.app X.obj := by
  rw [Adjunction.map_restrictFullyFaithful_counit_app]
  dsimp only [Iso.refl_inv, NatTrans.id_app]
  dsimp only [Functor.comp_obj, ObjectProperty.ι_obj, ObjectProperty.lift]
  erw [L.map_id, Category.id_comp, Category.id_comp]

/-- Identify the equivalence-unit transfer by its adjunction-unit inverse formula.
Source: Stacks Project, Tags 0D5S, 0D5T and 08HY.
(blueprint: lem-sc-horizontal-transfer-inverse-formula)

Proof: Substitute k = k₀. Write L for pullback along e.hom, Rq for direct
image along q, η for the pinned adjunction unit, U for ev.unitIso, and δ for
the restricted conjugate d (including transport along hp). The fully faithful
QCoh inclusions map the restricted adjunction units and counits to the ambient
ones. Expanding conjugation into units and counits therefore shows that δ is
exactly the transport from R(p) to R(e.hom) followed by Rq used in li.
Consequently the constructed transfer component at D is
δ.hom at L(D), followed by Rq applied to ri.hom at L(D), then Rq applied to
U.inv at D. The supplied inverse component of j is Rq applied to η at D,
followed by δ.inv at L(D). Compose j.inv with the constructed transfer:
δ.inv and δ.hom cancel. By unit_rightAdjointUniq_hom_app, η at D followed
by ri.hom at L(D) equals U.hom at D. Functoriality of Rq and cancellation
of U.hom with U.inv make the composite the identity. The ambient computation
reflects through the faithful QCoh inclusion. Precompose with j.hom and cancel
j.hom followed by j.inv, obtaining k.app D = j.hom.app D.
The argument uses only functorial and adjunction identities and applies also to
identity arrows, empty schemes and zero objects. No base-change map is used. -/
theorem horizontal_transfer_eq_of_inverse_formula
    [∀ Z : Scheme.{u}, HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    {P Q Z : Scheme.{u}}
    [CompactSpace P] [QuasiSeparatedSpace P] [CompactSpace Q] [QuasiSeparatedSpace Q]
    [CompactSpace Z] [QuasiSeparatedSpace Z]
    (e : P ≅ Q) (q : Q ⟶ Z) (p : P ⟶ Z)
    [QuasiCompact q] [QuasiSeparated q] [QuasiCompact p] [QuasiSeparated p]
    (hp : e.hom ≫ q = p) :
    let ev := horizontalMateEquivalence e
    let ri := (horizontalMateAdjunction e.hom).rightAdjointUniq ev.toAdjunction
    let li := eqToIso (congrArg qcDirectImage hp.symm) ≪≫
      horizontalMatePushComp e.hom q ≪≫
      Functor.isoWhiskerRight ri (horizontalMatePushforward q)
    let k₀ : TwoSquare (horizontalMatePullback e.hom) (horizontalMatePushforward q)
        (horizontalMatePushforward p) (𝟭 (schemeDerivedQCohCategory Z)) :=
      .mk _ _ _ _ <|
        (Functor.isoWhiskerLeft (horizontalMatePullback e.hom) li).hom ≫
          (Functor.associator _ _ _).inv ≫
          Functor.whiskerRight ev.unitIso.inv (horizontalMatePushforward q) ≫
          (Functor.leftUnitor (horizontalMatePushforward q)).hom ≫
          (Functor.rightUnitor (horizontalMatePushforward q)).inv
    let a := fun {A B : Scheme.{u}} (r : A ⟶ B) ↦
      Classical.choose (exists_schemeDerivedAdjunction r
        (hAdd := (Classical.choose exists_derivedPullbackComposition) r)
        ((Classical.choose (Classical.choose_spec exists_derivedPullbackComposition)) r)
        ((Classical.choose (Classical.choose_spec
          (Classical.choose_spec exists_derivedPullbackComposition))) r))
    let d := conjugateIsoEquiv (a p) ((a q).comp (a e.hom))
      (horizontalMateAmbientComp e.hom q ≪≫
        eqToIso (congrArg (fun r ↦ derivedPullback.{u, w} r) hp))
    ∀ (k : TwoSquare (horizontalMatePullback e.hom) (horizontalMatePushforward q)
        (horizontalMatePushforward p) (𝟭 (schemeDerivedQCohCategory Z))), k = k₀ →
    ∀ (j : qcPullback e.hom ⋙ qcDirectImage p ≅ qcDirectImage q),
      (∀ D : schemeDerivedQCohCategory Q,
        (schemeDerivedQCohProperty Z).ι.map (j.inv.app D) =
          (schemeDerivedDirectImage q).map ((a e.hom).unit.app D.obj) ≫
            d.inv.app ((derivedPullback e.hom).obj D.obj)) →
      ∀ D : schemeDerivedQCohCategory Q, k.app D = j.hom.app D := by
  classical
  subst p
  intro ev ri li k₀ a d k hk j hj D
  subst k
  have hu : (schemeDerivedQCohProperty Q).ι.map
      ((horizontalMateAdjunction e.hom).unit.app D) = (a e.hom).unit.app D.obj := by
    exact restricted_unit_map _ _ _ _ _ _ _ D
  have hd : (schemeDerivedQCohProperty Z).ι.map
      ((horizontalMatePushComp e.hom q).hom.app
        ((horizontalMatePullback e.hom).obj D)) =
      d.hom.app ((derivedPullback e.hom).obj D.obj) := by
    simp only [d, eqToIso_refl, Iso.trans_refl]
    simp only [horizontalMatePushComp, conjugateIsoEquiv_apply_hom,
      conjugateEquiv_apply_app, Adjunction.comp_unit_app, Functor.map_comp]
    dsimp only [horizontalMatePushforward, ObjectProperty.ι_obj_lift_map,
      Functor.comp_map]
    simp only [horizontalMateAdjunction, restricted_unit_map, restricted_counit_map]
    simp only [horizontalMateComp, Functor.fullyFaithfulCancelRight_hom_app,
      Functor.map_preimage, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app]
    rfl
  apply (cancel_epi (j.inv.app D)).mp
  rw [j.inv_hom_id_app]
  apply (schemeDerivedQCohProperty Z).fullyFaithfulι.map_injective
  rw [Functor.map_comp, hj]
  have hkcomp : k₀.app D =
      (horizontalMatePushComp e.hom q).hom.app ((horizontalMatePullback e.hom).obj D) ≫
        (horizontalMatePushforward q).map
          (ri.hom.app ((horizontalMatePullback e.hom).obj D)) ≫
        (horizontalMatePushforward q).map (ev.unitIso.inv.app D) := by
    dsimp only [k₀, li, eqToIso_refl, Iso.trans_hom, Functor.isoWhiskerLeft_hom,
      Functor.isoWhiskerRight_hom, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, Functor.associator_inv_app,
      Functor.leftUnitor_hom_app, Functor.rightUnitor_inv_app]
    simp only [Category.id_comp, Category.comp_id, Category.assoc]
    erw [Iso.refl_hom, NatTrans.id_app, Category.id_comp, Category.comp_id]
  rw [hkcomp, Functor.map_comp, hd]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc, Functor.map_comp]
  change (schemeDerivedDirectImage q).map ((a e.hom).unit.app D.obj) ≫
    (schemeDerivedDirectImage q).map ((schemeDerivedQCohProperty Q).ι.map
      (ri.hom.app ((horizontalMatePullback e.hom).obj D))) ≫
    (schemeDerivedDirectImage q).map ((schemeDerivedQCohProperty Q).ι.map
      (ev.unitIso.inv.app D)) = 𝟙 _
  rw [← hu, ← Functor.map_comp, ← Functor.map_comp]
  rw [← Functor.map_comp, ← Functor.map_comp]
  dsimp only [ri]
  erw [Adjunction.unit_rightAdjointUniq_hom_app_assoc]
  change (schemeDerivedDirectImage q).map ((schemeDerivedQCohProperty Q).ι.map
    (ev.unitIso.hom.app D ≫ ev.unitIso.inv.app D)) = 𝟙 _
  rw [Iso.hom_inv_id_app]
  erw [CategoryTheory.Functor.map_id]

end AlgebraicGeometry
