/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Completed.CompletedExtensionZeroComparison
public import WeilConjectures.AlgebraicGeometry.AdicCoefficientDatum.CompletedPullback
public import WeilConjectures.AlgebraicGeometry.Ringed.RingedEtaleOriginWitness
import WeilConjectures.AlgebraicGeometry.Completed.CompletedFiniteExchangeCoordinates
import all WeilConjectures.AlgebraicGeometry.StrictTower.FiniteConstantCoefficientTransport
import WeilConjectures.AlgebraicGeometry.Bounded.BoundedConstructibleCompleteSupplement
import all WeilConjectures.AlgebraicGeometry.Adic.AdicCoefficientDatumSupplement

/-!
# Finite etale origins after completed-coefficient open extension

Source: blueprint proposition-composition-base-change-rf-shriek--4, proof step 2; Stacks 03DI, 09AF
and 0GL1.
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe t
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

private theorem finiteComparison_eq
    {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (T : Scheme.{t}) (n : ℕ) :
    pbcLevelConstantComparison T d n =
      finiteOriginConstantIso T (A ⧸ d.ideal ^ (n + 1)) := by
  apply (pbcLevelConstantComparison_exists T d n).unique
  · exact (pbcLevelConstantComparison_exists T d n).exists.choose_spec
  · intro V b
    exact ConcreteCategory.congr_hom
      (congr_app (toSheafify_naturality (ProEt.topology T)
        (AdicCoefficients.constants T (A ⧸ d.ideal ^ (n + 1)))) V) b |>.symm

private theorem restriction_exact
    {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    {U T : Scheme.{t}} (j : U ⟶ T) [IsOpenImmersion j] :
    PreservesFiniteLimits (cbcOpenRestriction d j inferInstance) ∧
      PreservesFiniteColimits (cbcOpenRestriction d j inferInstance) := by
  let G := cbcOpenSiteFunctor j inferInstance
  have : G.IsCocontinuous (ProEt.topology U) (ProEt.topology T) :=
    ProEt.isCocontinuous_overMap (inferInstance : WeaklyEtale j)
  let F := cbcOpenRestriction d j inferInstance
  let V := SheafOfModules.toSheaf (reductionModuleRing U (d.completedRing U))
  let H := G.sheafPushforwardContinuous AddCommGrpCat.{t + 1}
    (ProEt.topology U) (ProEt.topology T)
  have : PreservesFiniteLimits H := inferInstance
  have : PreservesColimitsOfSize.{t + 1, t + 1} H :=
    (G.sheafAdjunctionCocontinuous AddCommGrpCat.{t + 1}
      (ProEt.topology U) (ProEt.topology T)).leftAdjoint_preservesColimits
  have : PreservesFiniteLimits (F ⋙ V) :=
    inferInstanceAs (PreservesFiniteLimits
      (SheafOfModules.toSheaf (reductionModuleRing T (d.completedRing T)) ⋙ H))
  have : PreservesFiniteColimits (F ⋙ V) :=
    inferInstanceAs (PreservesFiniteColimits
      (SheafOfModules.toSheaf (reductionModuleRing T (d.completedRing T)) ⋙ H))
  exact ⟨preservesFiniteLimits_of_reflects_of_preserves F V,
    preservesFiniteColimits_of_reflects_of_preserves F V⟩

-- Localize an exact adjunction directly; no resolution choices are needed.
private def exactAdjunction
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    {F : C ⥤ D} {G : D ⥤ C} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (a : F ⊣ G) : F.mapDerivedCategory ⊣ G.mapDerivedCategory := by
  letI : CatCommSq (F.mapHomologicalComplex (.up ℤ))
      DerivedCategory.Q DerivedCategory.Q F.mapDerivedCategory :=
    ⟨(Functor.mapDerivedCategoryFactors _).symm⟩
  letI : CatCommSq (G.mapHomologicalComplex (.up ℤ))
      DerivedCategory.Q DerivedCategory.Q G.mapDerivedCategory :=
    ⟨(Functor.mapDerivedCategoryFactors _).symm⟩
  exact (a.mapHomologicalComplex (.up ℤ)).localization
    DerivedCategory.Q (HomologicalComplex.quasiIso _ (.up ℤ))
    DerivedCategory.Q (HomologicalComplex.quasiIso _ (.up ℤ))
    F.mapDerivedCategory G.mapDerivedCategory

-- Restriction along a coefficient isomorphism has identity sectionwise round trips.
section RestrictionEquivalence
variable {C : Type (t + 1)} [Category.{t} C] {J : GrothendieckTopology C}
  {R S : Sheaf J RingCat.{t + 1}}

private def restrictionRoundTrip (c : R ≅ S) :
    SheafOfModules.restrictScalars.{t + 1} c.hom ⋙
      SheafOfModules.restrictScalars c.inv ≅ 𝟭 (SheafOfModules.{t + 1} S) :=
  NatIso.ofComponents (fun M ↦ (SheafOfModules.fullyFaithfulForget S).preimageIso
    (PresheafOfModules.isoMk (fun U ↦
      (ModuleCat.restrictScalarsComp'App (c.inv.hom.app U).hom
        (c.hom.hom.app U).hom (RingHom.id _) (by
          have h := congr_app (congrArg (fun f : S ⟶ S ↦ f.hom) c.inv_hom_id) U
          exact (congrArg RingCat.Hom.hom h).symm) (M.val.obj U)).symm ≪≫
        ModuleCat.restrictScalarsId'App (RingHom.id _) rfl (M.val.obj U))
      (by intro U V f; ext x; rfl)))
    (by intro M N f; ext U x; rfl)

private theorem restrictionTriangle (c : R ≅ S) (M : SheafOfModules.{t + 1} S) :
    (SheafOfModules.restrictScalars c.hom).map ((restrictionRoundTrip c).inv.app M) ≫
      (restrictionRoundTrip c.symm).hom.app
        ((SheafOfModules.restrictScalars c.hom).obj M) = 𝟙 _ := by
  ext U x
  rfl

private def restrictionEquivalence (c : R ≅ S) :
    SheafOfModules.{t + 1} S ≌ SheafOfModules.{t + 1} R where
  functor := SheafOfModules.restrictScalars c.hom
  inverse := SheafOfModules.restrictScalars c.inv
  unitIso := (restrictionRoundTrip c).symm
  counitIso := restrictionRoundTrip c.symm
  functor_unitIso_comp := restrictionTriangle c

end RestrictionEquivalence

private theorem finiteRes_additive
    {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (T : Scheme.{t}) (n : ℕ) : (cbcFiniteRes d T n).Additive := by
  change (pbcRestrict (cbcFiniteProjection d T n)).Additive
  infer_instance

private theorem finiteRes_limits
    {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (T : Scheme.{t}) (n : ℕ) : PreservesFiniteLimits (cbcFiniteRes d T n) := by
  change PreservesFiniteLimits (pbcRestrict (cbcFiniteProjection d T n))
  infer_instance

private theorem finiteRes_colimits
    {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (T : Scheme.{t}) (n : ℕ) : PreservesFiniteColimits (cbcFiniteRes d T n) := by
  change PreservesFiniteColimits (pbcRestrict (cbcFiniteProjection d T n))
  infer_instance

attribute [local instance] finiteRes_additive finiteRes_limits finiteRes_colimits

private def finiteReductionAdjunction
    {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (T : Scheme.{t}) (n : ℕ) :
    cbcFiniteReduction d T n ⊣ (cbcFiniteRes d T n).mapDerivedCategory := by
  let c := (adicLisseForget T).mapIso (pbcLevelConstantComparison T d n)
  let E := restrictionEquivalence c
  have : E.functor.Additive := by
    change (SheafOfModules.restrictScalars c.hom).Additive
    infer_instance
  have : E.inverse.Additive := by
    change (SheafOfModules.restrictScalars c.inv).Additive
    infer_instance
  have : PreservesFiniteLimits E.functor := inferInstance
  have : PreservesFiniteColimits E.functor := inferInstance
  have : PreservesFiniteLimits E.inverse := inferInstance
  have : PreservesFiniteColimits E.inverse := inferInstance
  let b := exactAdjunction E.toAdjunction
  let a := (scalarDerivedAdjunction_exists T (d.projection T n)).some
  exact (a.comp b).ofNatIsoRight
    (pbcDerivedRestrictComp (d.projection T n)
      (pbcLevelConstantComparison T d n).inv (cbcFiniteProjection d T n) rfl)

end AlgebraicGeometry.Scheme
