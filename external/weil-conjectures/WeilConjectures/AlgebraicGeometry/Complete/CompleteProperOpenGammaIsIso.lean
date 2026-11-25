/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Complete.CompleteProperOpenGamma
public import WeilConjectures.AlgebraicGeometry.Complete.CompleteStrictComparisons
public import WeilConjectures.AlgebraicGeometry.Strict.Tower.StrictTowerExchangeMateNormalization
public import WeilConjectures.AlgebraicGeometry.Completed.Koszul.CompletedKoszulQuotientComparison
public import WeilConjectures.AlgebraicGeometry.Bounded.BoundedConstructibleCompleteSupplement
public import WeilConjectures.AlgebraicGeometry.Complete.CompleteStrictReductionOrigins
public import WeilConjectures.AlgebraicGeometry.Complete.CompleteAlphaComponents
public import WeilConjectures.AlgebraicGeometry.Complete.CompleteCompletedAlphaComponents

/-!
# Invertibility of the completed proper/open gamma

The proper/open comparison `cbcProperOpenGamma` on completed-ring modules is invertible
on complete objects with compatible bounded-below etale origins. The proof passes to the
strict quotient tower after constant-coefficient restriction, where the strict proper/open
gamma is invertible by finite compact-support base change.

Source: Weil conjectures blueprint, node proposition-composition-base-change-rf-shriek--4, proof
step 8 (blueprint: proposition-composition-base-change-rf-shriek--4).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

universe t

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

variable {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A)

attribute [-instance] WeilConjectures.SemilinearSections.moduleAbelian
  WeilConjectures.SemilinearSections.hasDerived flatConstantModulesAbelian
  SheafOfModules.RingedCoefficientProjection.cachedSheafifyModules
  SheafOfModules.RingedCoefficientProjection.cachedLocalEquivalences

attribute [local instance 100000] SheafOfModules.hasSheafify_coefficientUniverse
  SheafOfModules.wEqualsLocallyBijective_coefficientUniverse

section Reflection

private theorem derivedReflectsIso
    {C D : Type*} [Category C] [Abelian C] [Category D] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [F.ReflectsIsomorphisms] {X Y : DerivedCategory C} (f : X ⟶ Y)
    (hf : IsIso (F.mapDerivedCategory.map f)) : IsIso f := by
  rw [DerivedCategory.isIso_iff]
  intro n
  have : IsIso ((DerivedCategory.homologyFunctor D n).map (F.mapDerivedCategory.map f)) :=
    inferInstance
  have : IsIso (F.map ((DerivedCategory.homologyFunctor C n).map f)) :=
    (NatIso.isIso_map_iff (F.mapDerivedCategoryHomologyFunctorIso n) f).2 (by
      dsimp only [Functor.comp_map]
      infer_instance)
  exact isIso_of_reflects_iso _ F

/-- Termwise constant-coefficient restriction of strict towers reflects isomorphisms.
Source: Stacks 03DA (blueprint: proposition-composition-base-change-rf-shriek--4). -/
theorem exchangeTowerModuleRes_reflectsIsomorphisms (T : Scheme.{t}) :
    (exchangeTowerModuleRes d T).ReflectsIsomorphisms where
  reflects {M N} f hf := by
    have hr := (proEtaleRingRestrictScalars_properties (exchangeScalar d T)).2.2
    have h2 (n : ℕᵒᵖ) : IsIso (f.app n) := by
      have : IsIso ((proEtaleRingRestrictScalars (exchangeScalar d T)).map (f.app n)) :=
        (inferInstance : IsIso (((exchangeTowerModuleRes d T).map f).app n))
      exact isIso_of_reflects_iso (f.app n) (proEtaleRingRestrictScalars (exchangeScalar d T))
    exact NatIso.isIso_of_isIso_app f

/-- Derived constant-coefficient restriction of strict towers reflects isomorphisms.
Source: Stacks 05RT, 03DA (blueprint: proposition-composition-base-change-rf-shriek--4). -/
theorem exchangeTowerRes_isIso_iff (T : Scheme.{t})
    {M N : DerivedCategory (exchangeTowers T (d.completedRing T))} (f : M ⟶ N) :
    IsIso ((exchangeTowerRes d T).map f) ↔ IsIso f := by
  refine ⟨fun h ↦ ?_, fun h ↦ inferInstance⟩
  have := exchangeTowerModuleRes_reflectsIsomorphisms d T
  exact derivedReflectsIso (exchangeTowerModuleRes d T) f h

/-- The quotient completion unit is natural.
Source: blueprint completed pullback (blueprint:
proposition-composition-base-change-rf-shriek--4). -/
theorem completionUnit_naturality (T : Scheme.{t}) {K L : d.derived T} (f : K ⟶ L) :
    f ≫ d.completionUnit T L = d.completionUnit T K ≫
      (completedRlim T (d.completedRing T)).map ((completedReductionTower T d).map f) := by
  have h := ((d.constantRlimAdjunction T).unit ≫ Functor.whiskerRight
    (completedReductionAugmentation d T) (completedRlim T (d.completedRing T))).naturality f
  simpa only [AdicCoefficientDatum.completionUnit, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.comp_map, Functor.id_map, Category.assoc] using h

/-- A map of quotient-tower complete objects is invertible if its reduction tower is.
Source: Stacks 099N; blueprint step 8 (blueprint:
proposition-composition-base-change-rf-shriek--4). -/
theorem isIso_of_reductionTower_isIso (T : Scheme.{t}) {K L : d.derived T} (f : K ⟶ L)
    (hK : d.TowerComplete T K) (hL : d.TowerComplete T L)
    (hf : IsIso ((completedReductionTower T d).map f)) : IsIso f := by
  have : IsIso (d.completionUnit T K) := hK
  have : IsIso (d.completionUnit T L) := hL
  have : IsIso (f ≫ d.completionUnit T L) := by
    rw [completionUnit_naturality]
    infer_instance
  exact IsIso.of_isIso_comp_right f (d.completionUnit T L)

end Reflection

/-- Intrinsic completeness implies quotient-tower completeness.
Source: blueprint order 1587 (blueprint: proposition-composition-base-change-rf-shriek--4). -/
theorem cbcTowerComplete_of_completeProperty (T : Scheme.{t})
    (r : ℕ) (a : Fin r → A) (ha : Ideal.span (Set.range a) = d.ideal)
    (K : d.derived T) (hK : cbcCompleteProperty d T r a ha K) :
    d.TowerComplete T K := by
  obtain ⟨c, hc⟩ := completedKoszulQuotientComparison T d r a ha K
    (DerivedCategory.Q.objPreimage K) (DerivedCategory.Q.objObjPreimageIso K)
  change IsIso (intrinsicCompletionUnit T d r a ha K
    (DerivedCategory.Q.objPreimage K) (DerivedCategory.Q.objObjPreimageIso K)) at hK
  change IsIso (d.completionUnit T K)
  change intrinsicCompletionUnit T d r a ha K
    (DerivedCategory.Q.objPreimage K) (DerivedCategory.Q.objObjPreimageIso K) ≫
      c.hom = d.completionUnit T K at hc
  rw [← hc]
  infer_instance

/-- Quotient-tower completeness implies intrinsic completeness.
Source: blueprint order 1587 (blueprint: proposition-composition-base-change-rf-shriek--4). -/
theorem cbcCompleteProperty_of_towerComplete (T : Scheme.{t})
    (r : ℕ) (a : Fin r → A) (ha : Ideal.span (Set.range a) = d.ideal)
    (K : d.derived T) (hK : d.TowerComplete T K) :
    cbcCompleteProperty d T r a ha K := by
  obtain ⟨c, hc⟩ := completedKoszulQuotientComparison T d r a ha K
    (DerivedCategory.Q.objPreimage K) (DerivedCategory.Q.objObjPreimageIso K)
  change IsIso (d.completionUnit T K) at hK
  change IsIso (intrinsicCompletionUnit T d r a ha K
    (DerivedCategory.Q.objPreimage K) (DerivedCategory.Q.objObjPreimageIso K))
  change intrinsicCompletionUnit T d r a ha K
    (DerivedCategory.Q.objPreimage K) (DerivedCategory.Q.objObjPreimageIso K) ≫
      c.hom = d.completionUnit T K at hc
  have : IsIso (intrinsicCompletionUnit T d r a ha K
      (DerivedCategory.Q.objPreimage K) (DerivedCategory.Q.objObjPreimageIso K) ≫ c.hom) := by
    rw [hc]
    exact hK
  exact IsIso.of_isIso_comp_right _ c.hom

/-- The trivial Cartesian square of an open immersion over the identity.
Source: Stacks 01JR (blueprint: proposition-composition-base-change-rf-shriek--4). -/
def cbcIdOpenImmersionSquare {U T : Scheme.{t}} (j : U ⟶ T) [IsOpenImmersion j] :
    OpenImmersionSquare (𝟙 U) j j (𝟙 T) :=
  let sq : IsPullback (𝟙 U) j j (𝟙 T) := IsPullback.of_horiz_isIso ⟨by simp⟩
  { w := by simp
    isoPullback := sq.isoPullback
    hom_fst := sq.isoPullback_hom_fst
    hom_snd := sq.isoPullback_hom_snd
    isOpenImmersion := inferInstance
    isOpenImmersion' := inferInstance }

/-- Extension by zero along a quasi-compact open immersion preserves quotient-tower
completeness. This is the completeness assertion of `completedExtensionZeroComparison`.
Source: blueprint lem-cbc-completed-extension-zero-comparison, Stacks 099N
(blueprint: proposition-composition-base-change-rf-shriek--4). -/
theorem cbcJ_towerComplete {U T : Scheme.{t}} (j : U ⟶ T) [IsOpenImmersion j]
    [QuasiCompact j] (r : ℕ) (a : Fin r → A) (ha : Ideal.span (Set.range a) = d.ideal)
    (M : d.derived U) (hM : d.TowerComplete U M) :
    d.TowerComplete T ((cbcJ d j).obj M) := by
  have hc := ((completedExtensionZeroComparison d (cbcIdOpenImmersionSquare j) r a ha).2
    ⟨M, cbcCompleteProperty_of_towerComplete d U r a ha M hM⟩).1
  exact cbcTowerComplete_of_completeProperty d T r a ha _ hc


/-- After strict reduction and constant-coefficient restriction, the completed proper/open
gamma is conjugate to the strict-tower proper/open gamma.
Source: blueprint step 8 (blueprint: proposition-composition-base-change-rf-shriek--4).
Proof sketch: strict reduction followed by restriction commutes with inverse image (the
normalized reduction/pullback comparison and `exchangeResPull`), with direct image
(`towerProjection` and `exchangeResPush`, the mates of the former) and with open
extension (`cbcRingedOpenStrictReduction`). These comparisons are compatible with the
adjunction units and counits, with the inverse-image compositors and hence with the open
compositors. Therefore they carry the open base-change comparison, the clopen projection
and alpha to their strict versions, and the proper-adjunction mate gamma to the strict
gamma. -/
theorem cbcProperOpenGamma_strictConjugate {V W S T : Scheme.{t}} (k : V ⟶ W) (r : V ⟶ S)
    (p : W ⟶ T) (i : S ⟶ T) [IsOpenImmersion k] [IsOpenImmersion i]
    [QuasiCompact k] [QuasiCompact i] [IsProper r] [IsProper p]
    (h : k ≫ p = r ≫ i) (K : d.derived V) :
    ∃ (e₁ : (cbcStrictReduction d T).obj ((cbcJ d i).obj ((d.push r).obj K)) ≅
        (ProEtale.StrictTower.J A i).obj
          ((ProEtale.StrictTower.R A r).obj ((cbcStrictReduction d V).obj K)))
      (e₂ : (cbcStrictReduction d T).obj ((d.push p).obj ((cbcJ d k).obj K)) ≅
        (ProEtale.StrictTower.R A p).obj
          ((ProEtale.StrictTower.J A k).obj ((cbcStrictReduction d V).obj K))),
      (cbcStrictReduction d T).map ((cbcProperOpenGamma d k r p i h).app K) =
        e₁.hom ≫ (ProEtale.StrictTower.gamma A k r p i h).app
          ((cbcStrictReduction d V).obj K) ≫ e₂.inv := by
  let s := ProEtale.StrictTower.squareLift k r p i h
  have hpb : IsPullback (pullback.snd p i) (pullback.fst p i) i p :=
    (IsPullback.of_hasPullback p i).flip
  have hsu := cbcOpenUnit_isIso d s
  have hsp : IsIso (ProperOpenTransport.openToPush (cbcDerivedOpenAdjunction d s)
      (cbcPullPushAdjunction d s)) := cbcOpenToPush_abstract_isIso d s
  have hsu' := ProEtale.StrictTower.jAdj_unit_isIso A s
  have hsp' : IsIso (ProperOpenTransport.openToPush (ProEtale.StrictTower.jAdj A s)
      (ProEtale.StrictTower.adj A s)) := ProEtale.StrictTower.openToPush_isIso A s
  have hb (x) : IsIso (ProperOpenTransport.betaInvApp (cbcDerivedOpenAdjunction d i)
      (cbcDerivedOpenAdjunction d (pullback.fst p i))
      (cbcSquarePull d (pullback.snd p i) (pullback.fst p i) i p pullback.condition.symm) x) := by
    have := cbcBetaInvNat_isIso d (pullback.snd p i) (pullback.fst p i) i p
      pullback.condition.symm hpb
    exact ProperOpenTransport.betaInvApp_isIso_of_betaInvNat _ _ _ x
  have hb' (x) : IsIso (ProperOpenTransport.betaInvApp (ProEtale.StrictTower.jAdj A i)
      (ProEtale.StrictTower.jAdj A (pullback.fst p i))
      (ProEtale.StrictTower.squareG A (pullback.snd p i) (pullback.fst p i) i p
        pullback.condition.symm) x) :=
    ProEtale.StrictTower.betaInvApp_isIso A _ _ _ _ pullback.condition.symm hpb x
  have hoi := cbcStrictOpen_isIso d i
  have hof := cbcStrictOpen_isIso d (pullback.fst p i)
  have hos := cbcStrictOpen_isIso d s
  have hpr := cbcStrictPush_isIso d r
  have hpp := cbcStrictPush_isIso d p
  have H := fun hα hα' hsq he ↦
    ProperOpenTransport.gammaApp_transport'
    (DS := DerivedCategory (proEtaleRingModules S (d.completedRing S)))
    (DT := DerivedCategory (proEtaleRingModules T (d.completedRing T)))
    (DW := DerivedCategory (proEtaleRingModules W (d.completedRing W)))
    (DV := DerivedCategory (proEtaleRingModules V (d.completedRing V)))
    (DP := DerivedCategory (proEtaleRingModules (pullback p i) (d.completedRing (pullback p i))))
    (iDS := instCategoryDerivedCategory _) (iDT := instCategoryDerivedCategory _)
    (iDW := instCategoryDerivedCategory _)
    (iDV := instCategoryDerivedCategory _) (iDP := instCategoryDerivedCategory _)
    (DS' := ProEtale.StrictTower.Derived A S) (DT' := ProEtale.StrictTower.Derived A T)
    (DW' := ProEtale.StrictTower.Derived A W) (DV' := ProEtale.StrictTower.Derived A V)
    (DP' := ProEtale.StrictTower.Derived A (pullback p i))
    (iDS' := instCategoryDerivedCategory _) (iDT' := instCategoryDerivedCategory _)
    (iDW' := instCategoryDerivedCategory _)
    (iDV' := instCategoryDerivedCategory _) (iDP' := instCategoryDerivedCategory _)
    (cbcDerivedOpenAdjunction d i)
    (cbcPullPushAdjunction d p) (cbcDerivedOpenAdjunction d (pullback.fst p i))
    (cbcDerivedOpenAdjunction d s) (cbcPullPushAdjunction d s) (cbcPullPushAdjunction d r)
    (cbcSquarePull d (pullback.snd p i) (pullback.fst p i) i p pullback.condition.symm)
    (cbcJComp d s (pullback.fst p i) ≪≫ cbcJCongr d (pullback.lift_fst k r h))
    ((d.pullComp s (pullback.snd p i)).symm ≪≫
      eqToIso (congrArg (fun f ↦ d.pull f) (pullback.lift_snd k r h)))
    (ProEtale.StrictTower.jAdj A i) (ProEtale.StrictTower.adj A p)
    (ProEtale.StrictTower.jAdj A (pullback.fst p i)) (ProEtale.StrictTower.jAdj A s)
    (ProEtale.StrictTower.adj A s) (ProEtale.StrictTower.adj A r)
    (ProEtale.StrictTower.squareG A (pullback.snd p i) (pullback.fst p i) i p
      pullback.condition.symm)
    (ProEtale.StrictTower.jComp A s (pullback.fst p i) ≪≫
      ProEtale.StrictTower.jCongr A (pullback.lift_fst k r h))
    ((ProEtale.StrictTower.gComp A s (pullback.snd p i)).symm ≪≫
      eqToIso (congrArg (ProEtale.StrictTower.G A) (pullback.lift_snd k r h)))
    (cbcStrictPull d i) (cbcStrictPull d p) (cbcStrictPull d (pullback.snd p i))
    (cbcStrictPull d (pullback.fst p i)) (cbcStrictPull d s) (cbcStrictPull d r)
    (cbcProperOpenAlpha d k r p i h) (ProEtale.StrictTower.alpha A k r p i h) hα hα' hsq he
    rfl rfl rfl rfl (cbcProperOpenGamma d k r p i h) (ProEtale.StrictTower.gamma A k r p i h)
    (heq_of_eq (cbcProperOpenGamma_eq_mateEquiv d k r p i h))
    (heq_of_eq (ProEtale.StrictTower.gamma_eq_mateEquiv A k r p i h)) K
  refine H ?_ ?_ ?_ ?_
  · exact cbcProperOpenAlpha_app_eq_alphaApp d k r p i h
  · exact ProEtale.StrictTower.alpha_app_eq_alphaApp A k r p i h
  · exact cbcStrictPull_square d (pullback.snd p i) (pullback.fst p i) i p
      pullback.condition.symm
  · exact cbcStrictPull_comp_hom d s (pullback.snd p i) (pullback.lift_snd k r h)

/-- Compatible etale origins of a completed object give finite constant-coefficient etale
origins of every level of its restricted strict reduction tower.
Source: blueprint step 8 (blueprint: proposition-composition-base-change-rf-shriek--4). -/
theorem cbcStrictReduction_scalarEtaleOrigin (V : Scheme.{t}) (K : d.derived V)
    (origins : PbcHasCompatibleEtaleOrigins V d K) (n : ℕ) :
    Nonempty (ProEtale.StrictTower.ScalarEtaleOrigin A V
      ((ProEtale.StrictTower.ev A V n).obj ((cbcStrictReduction d V).obj K))) :=
  cbcStrictReductionLevel_scalarEtaleOrigin d V K origins n

/-- The proper/open gamma is invertible on complete objects with compatible etale origins.
Source: blueprint proof step 8; Stacks 0F7B, 09C9 (blueprint:
proposition-composition-base-change-rf-shriek--4). Proof: both sides are quotient-tower complete, so
it suffices that the strict reduction of gamma is invertible; constant-coefficient restriction
reflects this. After restriction gamma is conjugate to the strict gamma, which is invertible
levelwise by finite compact-support base change on the retained etale origins. -/
theorem cbcProperOpenGamma_app_isIso {V W S T : Scheme.{t}} (k : V ⟶ W) (r : V ⟶ S)
    (p : W ⟶ T) (i : S ⟶ T) [IsOpenImmersion k] [IsOpenImmersion i]
    [QuasiCompact k] [QuasiCompact i] [IsProper r] [IsProper p]
    (h : k ≫ p = r ≫ i)
    (n : ℕ) (a : Fin n → A) (ha : Ideal.span (Set.range a) = d.ideal)
    (K : (cbcCompleteProperty d V n a ha).FullSubcategory)
    (origins : PbcHasCompatibleEtaleOrigins V d K.obj) :
    IsIso ((cbcProperOpenGamma d k r p i h).app K.obj) := by
  have hK : d.TowerComplete V K.obj :=
    cbcTowerComplete_of_completeProperty d V n a ha K.obj K.property
  have hs : d.TowerComplete T ((cbcJ d i).obj ((d.push r).obj K.obj)) :=
    cbcJ_towerComplete d i n a ha _ (d.push_complete r K.obj hK)
  have ht : d.TowerComplete T ((d.push p).obj ((cbcJ d k).obj K.obj)) :=
    d.push_complete p _ (cbcJ_towerComplete d k n a ha _ hK)
  refine isIso_of_reductionTower_isIso d T _ hs ht ?_
  rw [← exchangeTowerRes_isIso_iff]
  obtain ⟨e₁, e₂, he⟩ := cbcProperOpenGamma_strictConjugate d k r p i h K.obj
  have := ProEtale.StrictTower.gamma_isIso A k r p i h ((cbcStrictReduction d V).obj K.obj)
    (fun m ↦ cbcStrictReduction_scalarEtaleOrigin d V K.obj origins m)
  change IsIso ((cbcStrictReduction d T).map _)
  rw [he]
  infer_instance

end AlgebraicGeometry.Scheme
