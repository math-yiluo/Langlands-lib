/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Category.Grp.AB
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import WeilConjectures.AlgebraicGeometry.ProEtale.AffineClosedSiteFunctorProperties
import WeilConjectures.AlgebraicGeometry.ProEtale.ClosedSiteAdjunction
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Conservative
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Iso

/-!
# The closed counit on abelian pro-etale sheaves

Source: Stacks Project, Tags 09AA, 09BL and 09BK
(auxiliary; not a blueprint node).
-/

@[expose] public section

universe u u'

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits Opposite

/-- Compute a mate on sections before specializing the site categories to schemes. -/
private theorem sheaf_mate_app
    {CU CZ CU' CZ' A : Type*} [Category CU] [Category CZ] [Category CU']
    [Category CZ'] [Category A]
    (JU : GrothendieckTopology CU) (JZ : GrothendieckTopology CZ)
    (JU' : GrothendieckTopology CU') (JZ' : GrothendieckTopology CZ')
    {J : CU ⥤ CZ} {R : CZ ⥤ CU} {J' : CU' ⥤ CZ'} {R' : CZ' ⥤ CU'}
    (a : J ⊣ R) (a' : J' ⊣ R') {K : CU ⥤ CU'} {L : CZ ⥤ CZ'}
    [J.IsContinuous JU JZ] [R.IsContinuous JZ JU]
    [J'.IsContinuous JU' JZ'] [R'.IsContinuous JZ' JU']
    [K.IsContinuous JU JU'] [L.IsContinuous JZ JZ']
    [(K ⋙ J').IsContinuous JU JZ'] [(J ⋙ L).IsContinuous JU JZ']
    (τ : K ⋙ J' ⟶ J ⋙ L) (F : Sheaf JU' A) (b : CZ) :
    (((mateEquiv (a'.sheafPushforwardContinuous (E := A) JU' JZ')
        (a.sheafPushforwardContinuous (E := A) JU JZ))
      (TwoSquare.mk (L.sheafPushforwardContinuous A JZ JZ')
        (J'.sheafPushforwardContinuous A JU' JZ')
        (J.sheafPushforwardContinuous A JU JZ) (K.sheafPushforwardContinuous A JU JU')
        (Functor.sheafPushforwardContinuousNatTrans τ A JU JZ'))).app F).hom.app
          (op b) =
      F.obj.map (a'.unit.app (K.obj (R.obj b)) ≫
        R'.map (τ.app (R.obj b)) ≫ R'.map (L.map (a.counit.app b))).op := by
  simp only [mateEquiv, Adjunction.sheafPushforwardContinuous,
    Functor.sheafPushforwardContinuousNatTrans, Equiv.coe_fn_mk, NatTrans.comp_app,
    Functor.rightUnitor_inv_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.comp_map, Functor.leftUnitor_hom_app, id_comp,
    ObjectProperty.FullSubcategory.comp_hom, Adjunction.whiskerLeft_unit_app_app,
    Functor.op_obj, Adjunction.op_unit_app, NatTrans.op_app, Adjunction.whiskerLeft_counit_app_app,
    Adjunction.op_counit_app, Functor.sheafPushforwardContinuous, ObjectProperty.lift,
    ObjectProperty.ι_obj, ObjectProperty.ι_map, ObjectProperty.FullSubcategory.id_hom,
    NatTrans.id_app, ObjectProperty.homMk, Functor.whiskeringLeft, Functor.whiskerLeft,
    Functor.whiskerRight]
  simp only [sheafToPresheaf, ObjectProperty.ι_obj, Functor.comp_obj, Functor.comp_map,
    Functor.op_map, Functor.op_obj, Quiver.Hom.unop_op,
    Functor.id_obj, comp_id, id_comp,
    Functor.map_comp, op_comp, Category.assoc]

/-- The site mate is the canonical comparison between two iterated pullbacks. -/
private theorem restriction_mate_site {C : Type*} [Category C] [HasPullbacks C]
    (P : MorphismProperty C) [P.IsStableUnderBaseChange] [P.IsStableUnderComposition]
    {U' U Z' Z : C} {g' : U' ⟶ U} {j' : U' ⟶ Z'} {j : U ⟶ Z} {g'' : Z' ⟶ Z}
    (hj : P j) (hj' : P j') (sq : CommSq g' j' j g'') (b : P.Over ⊤ Z) :
    (MorphismProperty.Over.mapPullbackAdj P ⊤ j' hj' trivial).unit.app
        ((MorphismProperty.Over.pullback P ⊤ g').obj
          ((MorphismProperty.Over.pullback P ⊤ j).obj b)) ≫
      (MorphismProperty.Over.pullback P ⊤ j').map
        ((MorphismProperty.Over.pullbackMapComparison hj hj' sq).app
          ((MorphismProperty.Over.pullback P ⊤ j).obj b)) ≫
      (MorphismProperty.Over.pullback P ⊤ j').map
        ((MorphismProperty.Over.pullback P ⊤ g'').map
          ((MorphismProperty.Over.mapPullbackAdj P ⊤ j hj trivial).counit.app b)) =
    (MorphismProperty.Over.pullbackComp g' j).inv.app b ≫
      (MorphismProperty.Over.pullbackCongr (P := P) (Q := ⊤) sq.w.symm).inv.app b ≫
      (MorphismProperty.Over.pullbackComp j' g'').hom.app b := by
  apply MorphismProperty.Over.Hom.ext
  simp only [MorphismProperty.Comma.comp_left,
    MorphismProperty.Over.pullback_map_left,
    MorphismProperty.Over.mapPullbackAdj_unit_app,
    MorphismProperty.Over.mapPullbackAdj_counit_app]
  apply pullback.hom_ext
  · apply pullback.hom_ext <;>
      simp [MorphismProperty.Over.pullbackCongr, MorphismProperty.Over.pullback,
        MorphismProperty.Over.mk, MorphismProperty.Over.map,
        MorphismProperty.Comma.mapRight, CategoryTheory.Comma.mapRight,
        MorphismProperty.Comma.lift, MorphismProperty.Comma.forget]
  · simp [MorphismProperty.Over.pullbackCongr, MorphismProperty.Over.pullback,
      MorphismProperty.Over.mk, MorphismProperty.Over.map,
      MorphismProperty.Comma.mapRight, CategoryTheory.Comma.mapRight,
      MorphismProperty.Comma.lift, MorphismProperty.Comma.forget]

namespace AlgebraicGeometry.ProEtale

open Scheme MorphismProperty

open Scheme.AffineProEt in
private theorem affine_ff (A : Type u) [CommRing A] (I : Ideal A) :
    (lowerStar Ab.{u + 1}
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))).Full ∧
    (lowerStar Ab.{u + 1}
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))).Faithful := by
  let X := Spec (.of A)
  let Z := Spec (.of (A ⧸ I))
  let v := closedSiteLift A I
  let b := closedSiteBaseChange A I
  obtain ⟨adj, hunit⟩ := exists_closedSiteAdjunction A I
  have : IsIso adj.unit := hunit
  have : IsIso adj.op.counit := by
    change IsIso (NatTrans.op adj.unit)
    exact (NatTrans.isIso_iff_isIso_app _).mpr (fun V ↦ by
      change IsIso (adj.unit.app V.unop).op
      infer_instance)
  let a := adj.op.whiskerLeft Ab.{u + 1}
  have : IsIso a.counit := by
    apply (NatTrans.isIso_iff_isIso_app _).mpr
    intro F
    dsimp [a, Adjunction.whiskerLeft]
    infer_instance
  have ff := a.fullyFaithfulROfIsIsoCounit
  have : ((Functor.whiskeringLeft _ _ Ab.{u + 1}).obj b.op).Full := ff.full
  have : ((Functor.whiskeringLeft _ _ Ab.{u + 1}).obj b.op).Faithful := ff.faithful
  obtain ⟨_, _, _, _, hco, _, _, _⟩ := affine_closed_site_functor_properties A I
  let : v.IsCocontinuous (topology Z) (topology X) := hco
  let : b.IsContinuous (topology X) (topology Z) :=
    adj.isContinuous_of_isCocontinuous _ _
  let R := b.sheafPushforwardContinuous Ab.{u + 1} (topology X) (topology Z)
  have : (R ⋙ sheafToPresheaf (topology X) Ab.{u + 1}).Full := by
    change (sheafToPresheaf (topology Z) Ab.{u + 1} ⋙
      (Functor.whiskeringLeft _ _ Ab.{u + 1}).obj b.op).Full
    infer_instance
  have : (R ⋙ sheafToPresheaf (topology X) Ab.{u + 1}).Faithful := by
    change (sheafToPresheaf (topology Z) Ab.{u + 1} ⋙
      (Functor.whiskeringLeft _ _ Ab.{u + 1}).obj b.op).Faithful
    infer_instance
  have : R.Full := Functor.Full.of_comp_faithful _
    (sheafToPresheaf (topology X) Ab.{u + 1})
  have : R.Faithful := Functor.Faithful.of_comp _
    (sheafToPresheaf (topology X) Ab.{u + 1})
  let RX := (Scheme.AffineProEt.toProEt X).sheafPushforwardContinuous Ab.{u + 1}
    (topology X) (Scheme.ProEt.topology X)
  let RZ := (Scheme.AffineProEt.toProEt Z).sheafPushforwardContinuous Ab.{u + 1}
    (topology Z) (Scheme.ProEt.topology Z)
  let i : Z ⟶ X := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))
  have h : lowerStar Ab.{u + 1} i ⋙ RX ≅ RZ ⋙ R := Iso.refl _
  have : (lowerStar Ab.{u + 1} i ⋙ RX).Full := Functor.Full.of_iso h.symm
  have : (lowerStar Ab.{u + 1} i ⋙ RX).Faithful := Functor.Faithful.of_iso h.symm
  exact ⟨Functor.Full.of_comp_faithful _ RX, Functor.Faithful.of_comp _ RX⟩

private theorem affine_ff_of_affine {X Z : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] [IsAffine X] :
    (lowerStar Ab.{u + 1} i).Full ∧ (lowerStar Ab.{u + 1} i).Faithful := by
  let e := X.isoSpec
  have : IsClosedImmersion (i ≫ e.hom) := inferInstance
  obtain ⟨I, eZ, he⟩ := IsClosedImmersion.Spec_iff.mp this
  obtain ⟨hfull, hfaith⟩ := affine_ff Γ(X, ⊤) I
  let q := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))
  have : (lowerStar Ab.{u + 1} q).Full := hfull
  have : (lowerStar Ab.{u + 1} q).Faithful := hfaith
  have : (lowerStar Ab.{u + 1} (i ≫ e.hom)).Full := by
    rw [he]
    exact Functor.Full.of_iso (lowerStarComp Ab.{u + 1} eZ.hom q)
  have : (lowerStar Ab.{u + 1} (i ≫ e.hom)).Faithful := by
    rw [he]
    exact Functor.Faithful.of_iso (lowerStarComp Ab.{u + 1} eZ.hom q)
  have : (lowerStar Ab.{u + 1} i ⋙ lowerStar Ab.{u + 1} e.hom).Full :=
    Functor.Full.of_iso (lowerStarComp Ab.{u + 1} i e.hom).symm
  have : (lowerStar Ab.{u + 1} i ⋙ lowerStar Ab.{u + 1} e.hom).Faithful :=
    Functor.Faithful.of_iso (lowerStarComp Ab.{u + 1} i e.hom).symm
  exact ⟨Functor.Full.of_comp_faithful _ (lowerStar Ab.{u + 1} e.hom),
    Functor.Faithful.of_comp _ (lowerStar Ab.{u + 1} e.hom)⟩

section Localization

variable (A : Type u') [Category.{u + 1} A] [Abelian A]
  [IsGrothendieckAbelian.{u + 1} A]
variable {U' U Z' Z : Scheme.{u}} {g' : U' ⟶ U} {j' : U' ⟶ Z'}
  {j : U ⟶ Z} {g'' : Z' ⟶ Z}

variable [WeaklyEtale j] [WeaklyEtale j']

private theorem counitPullbackMapContinuous :
    (MorphismProperty.Over.pullback @WeaklyEtale ⊤ g' ⋙
    MorphismProperty.Over.map ⊤ (inferInstance : @WeaklyEtale _ _ j')).IsContinuous
      (Scheme.ProEt.topology U) (Scheme.ProEt.topology Z') :=
  have := Scheme.ProEt.isContinuous_overPullback g'
  have := Scheme.ProEt.isContinuous_overMap (inferInstance : @WeaklyEtale _ _ j')
  Functor.isContinuous_comp _ _ _ (Scheme.ProEt.topology U') _

private theorem counitMapPullbackContinuous :
    (MorphismProperty.Over.map ⊤ (inferInstance : @WeaklyEtale _ _ j) ⋙
    MorphismProperty.Over.pullback @WeaklyEtale ⊤ g'').IsContinuous
      (Scheme.ProEt.topology U) (Scheme.ProEt.topology Z') :=
  have := Scheme.ProEt.isContinuous_overPullback g''
  have := Scheme.ProEt.isContinuous_overMap (inferInstance : @WeaklyEtale _ _ j)
  Functor.isContinuous_comp _ _ _ (Scheme.ProEt.topology Z) _

attribute [local instance] counitPullbackMapContinuous counitMapPullbackContinuous

/-- The base change map `g''_* ⋙ j^* ⟶ j'^* ⋙ g'_*` on pro-étale sheaves, with the pullbacks
along the weakly étale morphisms `j` and `j'` computed as restrictions along the localization
functors: the map induced by `CategoryTheory.MorphismProperty.Over.pullbackMapComparison`. -/
private noncomputable def counitRestrictionBaseChangeMap (sq : CommSq g' j' j g'') :
    (g'')_*[A] ⋙ ProEtale.localizationRestriction A j inferInstance ⟶
      ProEtale.localizationRestriction A j' inferInstance ⋙ (g')_*[A] :=
  Functor.sheafPushforwardContinuousNatTrans
    (MorphismProperty.Over.pullbackMapComparison (inferInstance : @WeaklyEtale _ _ j)
      (inferInstance : @WeaklyEtale _ _ j') sq) A
    (Scheme.ProEt.topology U) (Scheme.ProEt.topology Z')

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
/-- The restriction comparison is invertible for a cartesian square. -/
private theorem isIso_counitRestrictionBaseChangeMap_of_isPullback
    (hsq : IsPullback g' j' j g'') :
    IsIso (counitRestrictionBaseChangeMap A hsq.toCommSq) :=
  have := MorphismProperty.Over.isIso_pullbackMapComparison_of_isPullback
    (inferInstance : @WeaklyEtale _ _ j) (inferInstance : @WeaklyEtale _ _ j') hsq
  inferInstanceAs (IsIso (Functor.sheafPushforwardContinuousNatTrans
    (MorphismProperty.Over.pullbackMapComparison (inferInstance : @WeaklyEtale _ _ j)
      (inferInstance : @WeaklyEtale _ _ j') hsq.toCommSq) A
    (Scheme.ProEt.topology U) (Scheme.ProEt.topology Z')))

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
/-- The horizontal mate of restriction base change is invertible. -/
private theorem isIso_counitRestrictionMate (sq : CommSq g' j' j g'') :
    IsIso (mateEquiv
      (ProEtale.localizationRestrictionLowerStarAdjunction A j' inferInstance)
      (ProEtale.localizationRestrictionLowerStarAdjunction A j inferInstance)
      (TwoSquare.mk _ _ _ _ (counitRestrictionBaseChangeMap A sq))) := by
  apply (NatTrans.isIso_iff_isIso_app _).mpr
  intro F
  rw [← isIso_iff_of_reflects_iso _ (sheafToPresheaf (Scheme.ProEt.topology Z) A)]
  apply (NatTrans.isIso_iff_isIso_app _).mpr
  rintro ⟨b⟩
  dsimp only [sheafToPresheaf, ObjectProperty.ι_map,
    localizationRestrictionLowerStarAdjunction, counitRestrictionBaseChangeMap,
    localizationRestriction, lowerStar]
  rw [sheaf_mate_app, restriction_mate_site]
  infer_instance

private theorem isIso_localized_counit
    (hsq : IsPullback g' j' j g'')
    [IsIso (upperStarLowerStarAdjunction A g').counit]
    (F : Sheaf (Scheme.ProEt.topology Z') A) :
    IsIso ((localizationRestriction A j' inferInstance).map
      ((upperStarLowerStarAdjunction A g'').counit.app F)) := by
  let a₁ := upperStarLowerStarAdjunction A g''
  let a₂ := upperStarLowerStarAdjunction A g'
  let a₃ := localizationRestrictionLowerStarAdjunction A j inferInstance
  let a₄ := localizationRestrictionLowerStarAdjunction A j' inferInstance
  let β := TwoSquare.mk _ _ _ _ (counitRestrictionBaseChangeMap A hsq.toCommSq)
  let α := (mateEquiv a₁ a₂).symm β
  have hβ : IsIso β :=
    isIso_counitRestrictionBaseChangeMap_of_isPullback A hsq
  have hm : IsIso ((mateEquiv a₄ a₃ β)) :=
    isIso_counitRestrictionMate A hsq.toCommSq
  have hα : IsIso α := by
    have he := iterated_mateEquiv_conjugateEquiv a₁ a₂ a₃ a₄ α
    have : IsIso (conjugateEquiv (a₁.comp a₄) (a₃.comp a₂) α) := by
      rw [← he]
      simpa only [α, Equiv.apply_symm_apply] using hm
    exact conjugateEquiv_of_iso (a₁.comp a₄) (a₃.comp a₂) α
  have hc := mateEquiv_counit_symm a₁ a₂ β F
  have : IsIso (α.app ((lowerStar A g'').obj F) ≫
      (localizationRestriction A j' inferInstance).map (a₁.counit.app F)) := by
    rw [← hc]
    infer_instance
  exact IsIso.of_isIso_comp_left (α.app _) _

end Localization

/-- Closed direct image on abelian pro-etale sheaves is fully faithful, expressed by the
invertibility of the actual inverse-image/direct-image adjunction counit.

Source: Stacks Project, Tags 09AA, 09BL and 09BK
(auxiliary; not a blueprint node).

Proof:
1. For a quotient immersion Spec(A/I) → Spec A, take the opposite of the closed-site
adjunction and whisker with abelian-group-valued presheaves. Its counit is invertible,
since the original site unit is invertible. Hence precomposition with base change is
fully faithful. Cocontinuity of the lift gives continuity of base change, so this functor
restricts to sheaves. Full faithfulness of the sheaf-to-presheaf inclusions then gives
full faithfulness on the affine bases.
2. The affine-basis restriction equivalences commute with the actual direct image.
Cancel the faithful restriction functor to obtain full faithfulness of direct image.
Every closed immersion into an affine scheme is isomorphic to a quotient immersion;
composition and isomorphism invariance give full faithfulness in that case as well.
Its actual adjunction counit is consequently invertible.
3. For the inverse images of affine opens, restriction base change is induced by the
canonical comparison of site pullbacks. It is invertible for a cartesian square. Its
horizontal mate is invertible too: on sections it is induced by the composite of the
site unit, the comparison, and the site counit, which is the canonical isomorphism between
iterated pullbacks. The double-mate identity and the mate-counit identity show that each
open restriction of the global counit is a composite of isomorphisms, using the affine
counit from step 2.
4. Restrictions along an open cover are jointly conservative. Indeed, each weakly etale
object is covered by its base changes along that cover; any member of the generated sieve
factors through a covering open. The sheaf-local isomorphism criterion applies. Thus every
component of the global counit, and then the counit itself, is invertible. Empty closed
schemes and nonreduced closed thickenings are included; there is no finite-presentation
or quasi-compact-open-complement hypothesis. -/
theorem abelian_closed_counit {X Z : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] :
    IsIso (upperStarLowerStarAdjunction Ab.{u + 1} i).counit := by
  apply (NatTrans.isIso_iff_isIso_app _).mpr
  intro F
  let C := X.affineCover.pullback₁ i
  refine isIso_of_isIso_localizationRestriction Ab.{u + 1} _ C.f
    (Scheme.zariskiPrecoverage_le_proetalePrecoverage _ C.mem₀) fun k ↦ ?_
  obtain ⟨hfull, hfaith⟩ := affine_ff_of_affine (pullback.snd i (X.affineCover.f k))
  have : (lowerStar Ab.{u + 1} (pullback.snd i (X.affineCover.f k))).Full := hfull
  have : (lowerStar Ab.{u + 1} (pullback.snd i (X.affineCover.f k))).Faithful := hfaith
  have : IsIso (upperStarLowerStarAdjunction Ab.{u + 1}
      (pullback.snd i (X.affineCover.f k))).counit :=
    Adjunction.counit_isIso_of_R_fully_faithful _
  exact isIso_localized_counit Ab.{u + 1}
    (IsPullback.of_hasPullback i (X.affineCover.f k)).flip F

end AlgebraicGeometry.ProEtale
