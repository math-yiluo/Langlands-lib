/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Support.SupportComparisonPullbackCoherence
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
public import Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModulesSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
public import WeilConjectures.AlgebraicGeometry.StrictTower.FiniteConstantCoefficientTransport
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
import all WeilConjectures.AlgebraicGeometry.StrictTower.FiniteConstantCoefficientTransport
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Unique

/-! # Canonical geometric pullback comparison under etale localization

## References

* Stacks Project, Tags 03CE, 03CF and 04J0
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 2048
set_option maxRecDepth 2048

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.ProEtale.LocalizedPullback

variable (A : Type (u + 1)) [CommRing A] [Finite A]
variable {U T : Scheme.{u}} (e : U ⟶ T) [Etale e]

/-- The specified chi: first undo etale restriction, then use the geometric comparison,
then pass to pro-etale restriction. No comparison is chosen arbitrarily. -/
def chi :
    Etale.localizationRestriction (ModuleCat.{u + 1} A) e inferInstance ⋙
        comparisonUpperStar (ModuleCat.{u + 1} A) U ≅
      comparisonUpperStar (ModuleCat.{u + 1} A) T ⋙
        localizationRestriction (ModuleCat.{u + 1} A) e inferInstance :=
  Functor.isoWhiskerRight
      (Etale.upperStarIsoLocalizationRestriction (ModuleCat.{u + 1} A) e inferInstance).symm
      (comparisonUpperStar (ModuleCat.{u + 1} A) U) ≪≫
    supportSiteComparisonCoefficientPullbackIso (ModuleCat.{u + 1} A) e ≪≫
      Functor.isoWhiskerLeft (comparisonUpperStar (ModuleCat.{u + 1} A) T)
        (upperStarIsoLocalizationRestriction (ModuleCat.{u + 1} A) e inferInstance)

/-- The sectionwise identity beta: both restrictions evaluate at the same composite
object W over T, with identical scalar actions and restriction maps. -/
def beta :
    comparisonLowerStar (ModuleCat.{u + 1} A) T ⋙
        Etale.localizationRestriction (ModuleCat.{u + 1} A) e inferInstance ≅
      localizationRestriction (ModuleCat.{u + 1} A) e inferInstance ⋙
        comparisonLowerStar (ModuleCat.{u + 1} A) U :=
  Iso.refl _

/-- Projection/graph normalization and uniqueness for the etale comparison.
The counit of the site adjunction is the first projection, and its unit is the graph. -/
def EtaleNormalized
    (ρ : Etale.upperStar (ModuleCat.{u + 1} A) e ≅
      Etale.localizationRestriction (ModuleCat.{u + 1} A) e inferInstance) : Prop :=
  (∀ (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) (W : T.Etale),
    (((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) e).unit.app F ≫
      (Etale.lowerStar (ModuleCat.{u + 1} A) e).map (ρ.hom.app F)).hom.app (op W)) =
        F.obj.map ((MorphismProperty.Over.mapPullbackAdj @Etale ⊤ e
          inferInstance trivial).counit.app W).op) ∧
  (∀ (G : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) (W : U.Etale),
    ((Etale.localizationRestrictionLowerStarAdjunction
      (ModuleCat.{u + 1} A) e inferInstance).counit.app G).hom.app (op W) =
        G.obj.map ((MorphismProperty.Over.mapPullbackAdj @Etale ⊤ e
          inferInstance trivial).unit.app W).op) ∧
  (∀ ρ' : Etale.upperStar (ModuleCat.{u + 1} A) e ≅
      Etale.localizationRestriction (ModuleCat.{u + 1} A) e inferInstance,
    (∀ F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A),
      (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) e).unit.app F ≫
        (Etale.lowerStar (ModuleCat.{u + 1} A) e).map (ρ'.hom.app F) =
          (Etale.localizationRestrictionLowerStarAdjunction
            (ModuleCat.{u + 1} A) e inferInstance).unit.app F) → ρ' = ρ)

/-- Projection/graph normalization and uniqueness for the pro-etale comparison.
This uses weak etaleness of e and does not require e to be a monomorphism. -/
def ProEtaleNormalized
    (ρ : upperStar (ModuleCat.{u + 1} A) e ≅
      localizationRestriction (ModuleCat.{u + 1} A) e inferInstance) : Prop :=
  (∀ (F : Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A)) (W : T.ProEt),
    (((upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) e).unit.app F ≫
      (lowerStar (ModuleCat.{u + 1} A) e).map (ρ.hom.app F)).hom.app (op W)) =
        F.obj.map ((MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ e
          inferInstance trivial).counit.app W).op) ∧
  (∀ (G : Sheaf (Scheme.ProEt.topology U) (ModuleCat.{u + 1} A)) (W : U.ProEt),
    ((localizationRestrictionLowerStarAdjunction
      (ModuleCat.{u + 1} A) e inferInstance).counit.app G).hom.app (op W) =
        G.obj.map ((MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ e
          inferInstance trivial).unit.app W).op) ∧
  (∀ ρ' : upperStar (ModuleCat.{u + 1} A) e ≅
      localizationRestriction (ModuleCat.{u + 1} A) e inferInstance,
    (∀ F : Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A),
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) e).unit.app F ≫
        (lowerStar (ModuleCat.{u + 1} A) e).map (ρ'.hom.app F) =
          (localizationRestrictionLowerStarAdjunction
            (ModuleCat.{u + 1} A) e inferInstance).unit.app F) → ρ' = ρ)

local notation "D" => ModuleCat A

omit [Finite A] in
/-- The unit-normalized etale restriction comparison. -/
private theorem normalized_etale :
    EtaleNormalized A e (Etale.upperStarIsoLocalizationRestriction D e inferInstance) := by
  let a := Etale.upperStarLowerStarAdjunction D e
  let r := Etale.localizationRestrictionLowerStarAdjunction D e inferInstance
  refine ⟨?_, ?_, ?_⟩
  · intro F W
    have h := a.unit_leftAdjointUniq_hom_app r F
    calc
      _ = (r.unit.app F).hom.app (op W) := congrArg (fun f ↦ f.hom.app (op W)) h
      _ = _ := by simp [r, Etale.localizationRestrictionLowerStarAdjunction]
  · intro G W
    simp [Etale.localizationRestrictionLowerStarAdjunction]
  · intro ρ' h
    apply Iso.ext
    apply NatTrans.ext
    funext F
    apply (a.homEquiv _ _).injective
    exact (h F).trans (a.homEquiv_leftAdjointUniq_hom_app r F).symm

omit [Finite A] in
/-- The unit-normalized pro-etale restriction comparison. -/
private theorem normalized_proEtale :
    ProEtaleNormalized A e (upperStarIsoLocalizationRestriction D e inferInstance) := by
  let b := upperStarLowerStarAdjunction D e
  let s := localizationRestrictionLowerStarAdjunction D e inferInstance
  refine ⟨?_, ?_, ?_⟩
  · intro F W
    have h := b.unit_leftAdjointUniq_hom_app s F
    calc
      _ = (s.unit.app F).hom.app (op W) := congrArg (fun f ↦ f.hom.app (op W)) h
      _ = _ := by simp [s, localizationRestrictionLowerStarAdjunction]
  · intro G W
    simp [localizationRestrictionLowerStarAdjunction]
  · intro ρ' h
    apply Iso.ext
    apply NatTrans.ext
    funext F
    apply (b.homEquiv _ _).injective
    exact (h F).trans (b.homEquiv_leftAdjointUniq_hom_app s F).symm

/-- Conjugating the specified chi gives the sectionwise direct-image comparison. -/
private theorem chi_conjugate :
    conjugateEquiv
      ((Scheme.proEtaleSiteComparisonModules T A).comp
        (localizationRestrictionLowerStarAdjunction D e inferInstance))
      ((Etale.localizationRestrictionLowerStarAdjunction D e inferInstance).comp
        (Scheme.proEtaleSiteComparisonModules U A)) (chi A e).hom =
      (supportSiteComparisonCoefficientDirectImageIso D e).hom := by
  let a := Etale.upperStarLowerStarAdjunction D e
  let b := upperStarLowerStarAdjunction D e
  let r := Etale.localizationRestrictionLowerStarAdjunction D e inferInstance
  let s := localizationRestrictionLowerStarAdjunction D e inferInstance
  let n := Scheme.proEtaleSiteComparisonModules T A
  let m := Scheme.proEtaleSiteComparisonModules U A
  let δ := supportSiteComparisonCoefficientDirectImageIso D e
  let cgeo := supportSiteComparisonCoefficientPullbackIso D e
  have hcgeo : conjugateEquiv (n.comp b) (a.comp m) cgeo.hom = δ.hom := by
    exact (conjugateEquiv (n.comp b) (a.comp m)).apply_symm_apply δ.hom
  have hc : conjugateEquiv (n.comp s) (r.comp m) (chi A e).hom = δ.hom := by
    change conjugateEquiv (n.comp s) (r.comp m)
      (Functor.whiskerRight (a.leftAdjointUniq r).inv (comparisonUpperStar D U) ≫
        cgeo.hom ≫ Functor.whiskerLeft (comparisonUpperStar D T)
          (b.leftAdjointUniq s).hom) = _
    rw [← Category.assoc,
      ← conjugateEquiv_comp (n.comp s) (n.comp b) (r.comp m),
      ← conjugateEquiv_comp (n.comp b) (a.comp m) (r.comp m),
      conjugateEquiv_whiskerLeft, conjugateEquiv_whiskerRight,
      conjugateEquiv_leftAdjointUniq_hom, conjugateEquiv_leftAdjointUniq_inv]
    simpa using hcgeo
  exact hc

omit [Finite A] in
/-- The second mate of beta is the direct-image identity, by the site right triangle. -/
private theorem beta_mate :
    (mateEquiv (localizationRestrictionLowerStarAdjunction D e inferInstance)
      (Etale.localizationRestrictionLowerStarAdjunction D e inferInstance)
      (TwoSquare.mk _ _ _ _ (beta A e).hom)) =
        (supportSiteComparisonCoefficientDirectImageIso D e).hom := by
  let r := Etale.localizationRestrictionLowerStarAdjunction D e inferInstance
  let s := localizationRestrictionLowerStarAdjunction D e inferInstance
  let δ := supportSiteComparisonCoefficientDirectImageIso D e
  apply NatTrans.ext
  funext G
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext W
  dsimp [mateEquiv, beta, s, r, localizationRestrictionLowerStarAdjunction,
    Etale.localizationRestrictionLowerStarAdjunction, δ,
    supportSiteComparisonCoefficientDirectImageIso,
    supportSiteComparisonSiteBaseChangeIso, Adjunction.sheafPushforwardContinuous,
    Adjunction.op, Adjunction.whiskerLeft, Etale.lowerStar, lowerStar,
    comparisonLowerStar, Functor.sheafPushforwardContinuous,
    Etale.localizationRestriction, localizationRestriction]
  erw [Category.id_comp, Category.id_comp, ← G.obj.map_comp]
  let t := MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ e inferInstance trivial
  change G.obj.map ((t.unit.app ((MorphismProperty.Over.pullback
    @WeaklyEtale ⊤ e).obj ((Scheme.toProEt T).obj W.unop)) ≫
      (MorphismProperty.Over.pullback @WeaklyEtale ⊤ e).map
        (t.counit.app ((Scheme.toProEt T).obj W.unop))).op) = _
  rw [t.right_triangle_components]
  rfl

/-- Injectivity of the second mate identifies the first mate of chi. -/
private theorem chi_mate :
    (mateEquiv (Scheme.proEtaleSiteComparisonModules T A)
      (Scheme.proEtaleSiteComparisonModules U A)
      (TwoSquare.mk _ _ _ _ (chi A e).hom)) = (beta A e).hom := by
  let r := Etale.localizationRestrictionLowerStarAdjunction D e inferInstance
  let s := localizationRestrictionLowerStarAdjunction D e inferInstance
  let n := Scheme.proEtaleSiteComparisonModules T A
  let m := Scheme.proEtaleSiteComparisonModules U A
  apply (mateEquiv s r).injective
  exact (iterated_mateEquiv_conjugateEquiv n m r s
    (TwoSquare.mk _ _ _ _ (chi A e).hom)).trans
      ((chi_conjugate A e).trans (beta_mate A e).symm)

/-- Cancellation for an invertible horizontal paste. The calculation takes place in arbitrary
functor categories, so no geometric functor is unfolded. -/
private theorem inverse_horizontal_paste
    {C₁ C₂ C₃ C₄ C₅ C₆ : Type*}
    [Category C₁] [Category C₂] [Category C₃] [Category C₄] [Category C₅] [Category C₆]
    {G₁ : C₁ ⥤ C₂} {P₁ : C₁ ⥤ C₃} {P₂ : C₂ ⥤ C₄} {H₁ : C₃ ⥤ C₄}
    {G₂ : C₂ ⥤ C₅} {P₃ : C₅ ⥤ C₆} {H₂ : C₄ ⥤ C₆}
    (i : P₁ ⋙ H₁ ≅ G₁ ⋙ P₂) (β : TwoSquare G₂ P₂ P₃ H₂)
    [IsIso (TwoSquare.hComp i.inv β)] :
    inv (TwoSquare.hComp i.inv β) ≫ Functor.whiskerLeft G₁ β =
      Functor.whiskerRight i.hom H₂ := by
  apply (cancel_epi (TwoSquare.hComp i.inv β)).1
  simp only [← Category.assoc, IsIso.hom_inv_id, Category.id_comp]
  apply NatTrans.ext
  funext X
  simp [TwoSquare.hComp, Category.assoc, ← Functor.map_comp]

omit [Etale e] in
/-- Horizontal mate pasting identifies the specified coefficient inverse comparison. -/
private theorem coefficient_comparison [TopologicalSpace A] [DiscreteTopology A] :
    ∃ j : StrictTower.C A T A (RingHom.id A) ⋙ StrictTower.modulePullback A e ≅
        upperStar (ModuleCat.{u + 1} A) e ⋙ StrictTower.C A U A (RingHom.id A),
      j.hom =
        ((mateEquiv (supportSiteProEtaleComparisonAdjunction (ModuleCat.{u + 1} A) e)
          (Scheme.proEtaleRingModuleAdjunction e (StrictTower.coefficients A T)
            (StrictTower.coefficients A U) (StrictTower.constantRingIso A e))).symm
          (StrictTower.cDirect A e A (RingHom.id A)).hom) ∧
      (@inv _ _ _ _ (StrictTower.hPullbackInv A e A (RingHom.id A))
        (StrictTower.hPullbackInv_isIso A e A (RingHom.id A))) ≫
          Functor.whiskerLeft (comparisonUpperStar (ModuleCat.{u + 1} A) T) j.hom =
        Functor.whiskerRight
          (supportSiteComparisonCoefficientPullbackIso (ModuleCat.{u + 1} A) e).hom
          (StrictTower.C A U A (RingHom.id A)) := by
  let a := Etale.upperStarLowerStarAdjunction D e
  let b := upperStarLowerStarAdjunction D e
  let c := Scheme.proEtaleRingModuleAdjunction e (StrictTower.coefficients A T)
    (StrictTower.coefficients A U) (StrictTower.constantRingIso A e)
  let α := (supportSiteComparisonCoefficientPullbackIso D e).inv
  let β := (mateEquiv b c).symm (StrictTower.cDirect A e A (RingHom.id A)).hom
  have hi : IsIso β := StrictTower.cPullback_isIso A e A (RingHom.id A)
  let j := asIso β
  have : IsIso (StrictTower.hPullbackInv A e A (RingHom.id A)) :=
    StrictTower.hPullbackInv_isIso A e A (RingHom.id A)
  have hp := mateEquiv_vcomp a b c α β
  rw [Equiv.apply_symm_apply] at hp
  have he : StrictTower.hPullbackInv A e A (RingHom.id A) =
      (TwoSquare.hComp α β) := by
    apply (mateEquiv a c).injective
    change (mateEquiv a c) ((mateEquiv a c).symm
      (StrictTower.hDirect A e A (RingHom.id A))) = _
    rw [Equiv.apply_symm_apply]
    exact hp.symm
  have htransport :
      (@inv _ _ _ _ (StrictTower.hPullbackInv A e A (RingHom.id A))
        (StrictTower.hPullbackInv_isIso A e A (RingHom.id A))) ≫
          Functor.whiskerLeft (comparisonUpperStar D T) j.hom =
      Functor.whiskerRight (supportSiteComparisonCoefficientPullbackIso D e).hom
        (StrictTower.C A U A (RingHom.id A)) := by
    have : IsIso (TwoSquare.hComp α β) := by
      rw [← he]
      infer_instance
    have hinv :
        (@inv _ _ _ _ (StrictTower.hPullbackInv A e A (RingHom.id A))
          (StrictTower.hPullbackInv_isIso A e A (RingHom.id A))) =
        inv (TwoSquare.hComp α β) := (IsIso.inv_eq_inv).2 he
    rw [hinv]
    exact inverse_horizontal_paste (supportSiteComparisonCoefficientPullbackIso D e) β
  exact ⟨j, rfl, htransport⟩

/-- The étale and pro-étale localization comparisons are normalized, the geometric comparison
`beta` is the identity on sections, is the mate of `chi` and is compatible with the comparison
units, and the canonical scalar pullback comparison `j` (the inverse mate of `cDirect`)
satisfies the transport-back identities relating `hPullbackInv`, `j` and `chi`. -/
theorem normalization [TopologicalSpace A] [DiscreteTopology A] :
    EtaleNormalized A e
      (Etale.upperStarIsoLocalizationRestriction (ModuleCat.{u + 1} A) e inferInstance) ∧
    ProEtaleNormalized A e
      (upperStarIsoLocalizationRestriction (ModuleCat.{u + 1} A) e inferInstance) ∧
    (∀ (G : Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A)) (W : U.Etale),
      ((beta A e).hom.app G).hom.app (op W) = 𝟙 _) ∧
    (mateEquiv (Scheme.proEtaleSiteComparisonModules T A)
      (Scheme.proEtaleSiteComparisonModules U A)
      (TwoSquare.mk _ _ _ _ (chi A e).hom)) =
        (beta A e).hom ∧
    (∀ F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A),
      (Scheme.proEtaleSiteComparisonModules U A).unit.app
          ((Etale.localizationRestriction (ModuleCat.{u + 1} A) e inferInstance).obj F) ≫
        (comparisonLowerStar (ModuleCat.{u + 1} A) U).map ((chi A e).hom.app F) =
      (Etale.localizationRestriction (ModuleCat.{u + 1} A) e inferInstance).map
          ((Scheme.proEtaleSiteComparisonModules T A).unit.app F) ≫
        (beta A e).hom.app ((comparisonUpperStar (ModuleCat.{u + 1} A) T).obj F)) ∧
    ∃ j : StrictTower.C A T A (RingHom.id A) ⋙ StrictTower.modulePullback A e ≅
        upperStar (ModuleCat.{u + 1} A) e ⋙ StrictTower.C A U A (RingHom.id A),
      j.hom =
        ((mateEquiv (supportSiteProEtaleComparisonAdjunction (ModuleCat.{u + 1} A) e)
          (Scheme.proEtaleRingModuleAdjunction e (StrictTower.coefficients A T)
            (StrictTower.coefficients A U) (StrictTower.constantRingIso A e))).symm
          (StrictTower.cDirect A e A (RingHom.id A)).hom) ∧
      (@inv _ _ _ _ (StrictTower.hPullbackInv A e A (RingHom.id A))
        (StrictTower.hPullbackInv_isIso A e A (RingHom.id A))) ≫
          Functor.whiskerLeft (comparisonUpperStar (ModuleCat.{u + 1} A) T) j.hom =
        Functor.whiskerRight
          (supportSiteComparisonCoefficientPullbackIso (ModuleCat.{u + 1} A) e).hom
          (StrictTower.C A U A (RingHom.id A)) ∧
      Functor.whiskerRight
          (Functor.whiskerRight
            (Etale.upperStarIsoLocalizationRestriction
              (ModuleCat.{u + 1} A) e inferInstance).inv
            (comparisonUpperStar (ModuleCat.{u + 1} A) U))
          (StrictTower.C A U A (RingHom.id A)) ≫
        (@inv _ _ _ _ (StrictTower.hPullbackInv A e A (RingHom.id A))
          (StrictTower.hPullbackInv_isIso A e A (RingHom.id A))) ≫
        Functor.whiskerLeft (comparisonUpperStar (ModuleCat.{u + 1} A) T) j.hom ≫
        Functor.whiskerRight
          (Functor.whiskerLeft (comparisonUpperStar (ModuleCat.{u + 1} A) T)
            (upperStarIsoLocalizationRestriction
              (ModuleCat.{u + 1} A) e inferInstance).hom)
          (StrictTower.C A U A (RingHom.id A)) =
        Functor.whiskerRight (chi A e).hom (StrictTower.C A U A (RingHom.id A)) := by
  have hmate := chi_mate A e
  refine ⟨normalized_etale A e, normalized_proEtale A e, (fun G W ↦ rfl),
    hmate, ?_, ?_⟩
  · intro F
    have h := unit_mateEquiv (Scheme.proEtaleSiteComparisonModules T A)
      (Scheme.proEtaleSiteComparisonModules U A)
      (TwoSquare.mk _ _ _ _ (chi A e).hom) F
    change _ ≫ ((mateEquiv (Scheme.proEtaleSiteComparisonModules T A)
      (Scheme.proEtaleSiteComparisonModules U A)
      (TwoSquare.mk _ _ _ _ (chi A e).hom))).app _ = _ at h
    rw [hmate] at h
    exact h.symm
  · obtain ⟨j, hj, htransport⟩ := coefficient_comparison A e
    refine ⟨j, hj, htransport, ?_⟩
    have h := congrArg (fun q ↦
      Functor.whiskerRight
        (Functor.whiskerRight (Etale.upperStarIsoLocalizationRestriction D e
          inferInstance).inv (comparisonUpperStar D U))
        (StrictTower.C A U A (RingHom.id A)) ≫ q ≫
      Functor.whiskerRight
        (Functor.whiskerLeft (comparisonUpperStar D T)
          (upperStarIsoLocalizationRestriction D e inferInstance).hom)
        (StrictTower.C A U A (RingHom.id A))) htransport
    exact h.trans (by
      simp [chi, Functor.whiskerRight_comp, Category.assoc])

end AlgebraicGeometry.ProEtale.LocalizedPullback
