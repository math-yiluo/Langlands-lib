/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.LocallyClosedCoefficientImmersion.LocallyClosedModuleExtensionModel
import WeilConjectures.AlgebraicGeometry.Clopen.ClopenScalarRestrictionReverseAdjunction

/-!
# Open and closed normalizations of the fixed locally closed model

## References

* Stacks Project, Tags 09AH, 09AA, 09BN, 03DI, 03DJ and 02V0
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme

-- Transport the existing clopen reverse adjunction to the actual tensor pullback.
private theorem clopen_reverse {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] [IsClosedImmersion j]
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (S : Sheaf (ProEt.topology U) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage j CommRingCat.{u + 1}).obj R ≅ S)
    (O : proEtaleRingModules U S ⥤ proEtaleRingModules X R)
    (adj : O ⊣ proEtaleRingModulePullback j R S c) :
    Nonempty (proEtaleRingModulePullback j R S c ⊣ O) := by
  let G := proEtaleOpenComposition j
  let F := proEtaleBaseChange j
  have : G.IsContinuous (ProEt.topology U) (ProEt.topology X) :=
    ProEt.isContinuous_overMap (inferInstance : WeaklyEtale j)
  let a := MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ j
    (inferInstance : WeaklyEtale j) trivial
  let b := a.sheafPushforwardContinuous (E := CommRingCat.{u + 1})
    (ProEt.topology U) (ProEt.topology X)
  let e := ((proEtaleSheafAdjunction j CommRingCat.{u + 1}).leftAdjointUniq b).app R
  let d := c.symm ≪≫ e
  let ψ := proEtaleRingDirectImageMap j R S c
  have H₁ : Functor.whiskerRight (NatTrans.op a.counit) R.obj =
      ψ.hom ≫ F.op.whiskerLeft d.hom.hom := by
    have h : (proEtaleSheafAdjunction j CommRingCat.{u + 1}).homEquiv _ _
        (c.hom ≫ d.hom) = b.unit.app R := by
      simp only [d, Iso.trans_hom, Iso.symm_hom, Iso.hom_inv_id_assoc]
      exact Adjunction.homEquiv_leftAdjointUniq_hom_app
        (proEtaleSheafAdjunction j CommRingCat.{u + 1}) b R
    rw [Adjunction.homEquiv_naturality_right] at h
    exact (congrArg (fun z ↦ z.hom) h).symm
  have H₂ : d.hom.hom ≫ G.op.whiskerLeft ψ.hom ≫
      Functor.whiskerRight (NatTrans.op a.unit) S.obj = 𝟙 S.obj := by
    apply NatTrans.ext
    funext V
    apply (cancel_mono (d.hom.hom.app V)).mp
    dsimp
    rw [Category.id_comp]
    have hn := d.hom.hom.naturality (a.unit.app V.unop).op
    dsimp at hn
    rw [Category.assoc, Category.assoc, hn]
    have hh := congrArg (fun z ↦ z.app (G.op.obj V)) H₁
    dsimp at hh
    erw [← Category.assoc (ψ.hom.app (G.op.obj V))
      (d.hom.hom.app (F.op.obj (G.op.obj V)))
      (R.obj.map (G.map (a.unit.app V.unop)).op), ← hh]
    rw [← Functor.map_comp, ← op_comp]
    erw [a.left_triangle_components]
    change d.hom.hom.app V ≫ R.obj.map (𝟙 (G.op.obj V)) = d.hom.hom.app V
    exact (congrArg (fun f ↦ d.hom.hom.app V ≫ f)
      (R.obj.map_id (G.op.obj V))).trans (Category.comp_id _)
  let Rr := (sheafCompose (ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R
  let Sr := (sheafCompose (ProEt.topology U)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S
  let φr : Sr ⟶ (G.sheafPushforwardContinuous RingCat.{u + 1}
      (ProEt.topology U) (ProEt.topology X)).obj Rr :=
    (sheafCompose (ProEt.topology U) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map d.hom
  let ψr : Rr ⟶ (F.sheafPushforwardContinuous RingCat.{u + 1}
      (ProEt.topology X) (ProEt.topology U)).obj Sr :=
    ⟨Functor.whiskerRight ψ.hom (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩
  have H₁r : Functor.whiskerRight (NatTrans.op a.counit) Rr.obj =
      ψr.hom ≫ F.op.whiskerLeft φr.hom := by
    apply NatTrans.ext
    funext V
    exact congrArg (fun z ↦ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}).map
      (z.app V)) H₁
  have H₂r : φr.hom ≫ G.op.whiskerLeft ψr.hom ≫
      Functor.whiskerRight (NatTrans.op a.unit) Sr.obj = 𝟙 Sr.obj := by
    apply NatTrans.ext
    funext V
    exact congrArg (fun z ↦ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}).map
      (z.app V)) H₂
  let ar := SheafOfModules.pushforwardPushforwardAdj a φr ψr H₁r H₂r
  let p := (proEtaleRingModuleAdjunction j R S c).leftAdjointUniq ar
  let ao := adj.ofNatIsoRight p
  obtain ⟨rev⟩ := clopenScalarRestrictionReverseAdjunction j R S d
    O ao
  exact ⟨rev.ofNatIsoLeft p.symm⟩


private theorem normalize_open
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D) (L : D ⥤ C)
    [F.Full] [F.Faithful] (r : F ⋙ L ≅ 𝟭 C) (adj : F ⊣ L) :
    ∃ adj' : F ⊣ L, LocallyClosedOpenNormalization F L r adj' := by
  have : IsIso adj.unit := adj.unit_isIso_of_L_fully_faithful
  let τ : 𝟭 C ≅ 𝟭 C := asIso adj.unit ≪≫ r
  let θ : F ≅ F := (Functor.leftUnitor F).symm ≪≫
    Functor.isoWhiskerRight τ.symm F ≪≫ Functor.leftUnitor F
  refine ⟨adj.ofNatIsoLeft θ, ?_⟩
  intro M
  rw [Adjunction.ofNatIsoLeft_unit]
  simp only [NatTrans.comp_app, Functor.whiskerRight_app]
  have hθ : θ.hom.app M = F.map (τ.inv.app M) := by simp [θ]
  have hη : adj.unit.app M ≫ L.map (F.map (τ.inv.app M)) =
      τ.inv.app M ≫ adj.unit.app M := by
    simpa only [Functor.id_obj, Functor.comp_obj, Functor.id_map, Functor.comp_map] using
      (adj.unit.naturality (τ.inv.app M)).symm
  rw [hθ, hη]
  simp [τ, Category.assoc]

private theorem normalize_closed
    {C D : Type*} [Category C] [Category D] (F P : C ⥤ D) (L : D ⥤ C)
    (r : F ⋙ L ≅ 𝟭 C) (d : P ⋙ L ⟶ 𝟭 C) [IsIso d] (e₀ : F ≅ P) :
    ∃ e : F ≅ P, LocallyClosedClosedNormalization F P L r d e := by
  let γ := Functor.isoWhiskerRight e₀ L ≪≫ asIso d
  let τ := γ.symm ≪≫ r
  let θ := (Functor.leftUnitor F).symm ≪≫
    Functor.isoWhiskerRight τ F ≪≫ Functor.leftUnitor F
  refine ⟨θ ≪≫ e₀, ?_⟩
  intro M
  change r.hom.app M = L.map (θ.hom.app M ≫ e₀.hom.app M) ≫ d.app M
  rw [L.map_comp, Category.assoc]
  have hθ : θ.hom.app M = F.map (τ.hom.app M) := by simp [θ]
  rw [hθ]
  change r.hom.app M = (F ⋙ L).map (τ.hom.app M) ≫ γ.hom.app M
  have hγ : (F ⋙ L).map (τ.hom.app M) ≫ γ.hom.app M =
      γ.hom.app M ≫ τ.hom.app M := by
    simpa only [Functor.id_obj, Functor.comp_obj, Functor.id_map] using
      γ.hom.naturality (τ.hom.app M)
  rw [hγ]
  simp [τ]

namespace LocallyClosedCoefficientImmersion

private instance modelExtension_full {S X : LocallyClosedCoefficients.{u}}
    (a : LocallyClosedCoefficientImmersion S X) : a.modelExtension.Full := by
  rw [modelExtension_eq]
  let c := a.extensionFactorization.closed
  let v := a.extensionFactorization.openMap
  have : c.push.Full :=
    (proEtaleRingModuleAdjunction c.hom _ _ c.coefficient).fullyFaithfulROfIsIsoCounit.full
  have : (modelOpenExtension v a.extensionFactorization.isOpen).Full :=
    (modelOpenAdjunction v _).fullyFaithfulLOfIsIsoUnit.full
  exact inferInstanceAs (c.push ⋙ modelOpenExtension v a.extensionFactorization.isOpen).Full

private instance modelExtension_faithful {S X : LocallyClosedCoefficients.{u}}
    (a : LocallyClosedCoefficientImmersion S X) : a.modelExtension.Faithful := by
  rw [modelExtension_eq]
  let c := a.extensionFactorization.closed
  let v := a.extensionFactorization.openMap
  have : c.push.Faithful :=
    (proEtaleRingModuleAdjunction c.hom _ _ c.coefficient).fullyFaithfulROfIsIsoCounit.faithful
  have : (modelOpenExtension v a.extensionFactorization.isOpen).Faithful :=
    (modelOpenAdjunction v _).fullyFaithfulLOfIsIsoUnit.faithful
  exact inferInstanceAs
    (c.push ⋙ modelOpenExtension v a.extensionFactorization.isOpen).Faithful

end LocallyClosedCoefficientImmersion

set_option linter.unusedVariables false in
/-- For a single immersion, the fixed closed-then-open model has the normalized open
adjunction and the normalized comparison with actual closed direct image. -/
theorem locallyClosedModel_boundary {S X : LocallyClosedCoefficients.{u}}
    (a : LocallyClosedCoefficientImmersion S X) :
    (∀ ha : IsOpenImmersion a.hom, ∃ adj : a.modelExtension ⊣ a.pull,
      LocallyClosedOpenNormalization a.modelExtension a.pull a.modelRestriction adj) ∧
    (∀ ha : IsClosedImmersion a.hom, ∃ e : a.modelExtension ≅ a.push,
      LocallyClosedClosedNormalization a.modelExtension a.push a.pull a.modelRestriction
        (proEtaleRingModuleAdjunction a.hom X.ring S.ring a.coefficient).counit e) := by
  let c := a.extensionFactorization.closed
  let v := a.extensionFactorization.openMap
  let O := LocallyClosedCoefficientImmersion.modelOpenExtension v
    a.extensionFactorization.isOpen
  let av := LocallyClosedCoefficientImmersion.modelOpenAdjunction v
    a.extensionFactorization.isOpen
  let ac := proEtaleRingModuleAdjunction c.hom _ _ c.coefficient
  let p : a.pull ≅ v.pull ⋙ c.pull :=
    eqToIso (congrArg LocallyClosedCoefficientImmersion.pull
      a.extensionFactorization.composite.symm) ≪≫ v.pullComp c
  let e : a.modelExtension ≅ c.push ⋙ O :=
    eqToIso (LocallyClosedCoefficientImmersion.modelExtension_eq a)
  constructor
  · intro ha
    have : IsOpenImmersion c.hom := a.extensionFactorization.closedIsOpen ha
    let Oc := LocallyClosedCoefficientImmersion.modelOpenExtension c inferInstance
    let aoc := LocallyClosedCoefficientImmersion.modelOpenAdjunction c inferInstance
    obtain ⟨rc⟩ := clopen_reverse c.hom _ _ c.coefficient Oc aoc
    let dc : c.push ≅ Oc := ac.rightAdjointUniq rc
    let bc : c.push ⊣ c.pull := aoc.ofNatIsoLeft dc.symm
    let adj : a.modelExtension ⊣ a.pull :=
      ((bc.comp av).ofNatIsoRight p.symm).ofNatIsoLeft e.symm
    exact normalize_open _ _ a.modelRestriction adj
  · intro ha
    have : IsClosedImmersion a.hom := ha
    have : IsClosedImmersion v.hom := a.extensionFactorization.openIsClosed ha
    obtain ⟨rv⟩ := clopen_reverse v.hom _ _ v.coefficient O av
    let b : a.pull ⊣ a.modelExtension :=
      ((rv.comp ac).ofNatIsoLeft p.symm).ofNatIsoRight e.symm
    exact normalize_closed _ _ _ a.modelRestriction
      (proEtaleRingModuleAdjunction a.hom _ _ a.coefficient).counit
      (b.rightAdjointUniq (proEtaleRingModuleAdjunction a.hom _ _ a.coefficient))

end AlgebraicGeometry.Scheme
