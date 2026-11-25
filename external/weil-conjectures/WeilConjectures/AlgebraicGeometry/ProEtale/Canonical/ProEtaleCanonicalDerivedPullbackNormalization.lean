/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleAmbientRingedExchange
public import Mathlib.CategoryTheory.Adjunction.CompositionIso
import all WeilConjectures.AlgebraicGeometry.ProEtale.Derived.ProEtaleDerivedPullbackCoherence
import WeilConjectures.Mathlib.CategoryTheory.MorphismProperty.OverAdjunction
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate

/-!
# Localization of the normalized pro-etale composition comparison

## References

* Stacks Project, Tags 0D6D and 0E47, coefficient inverse-image comparisons
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
attribute [local irreducible] proEtaleRingModuleAdjunctionNormalized
  proEtaleRingModuleUnitSection proEtaleRingCompositeCoefficients proEtaleRingDerivedPullbackFactors
  CochainComplex.IsAcyclicTensorKFlat SheafOfModules.IsFlatOnSite
  proEtaleRingModulePullback proEtaleRingDirectImageMap
  proEtaleCanonicalPullbackComposition

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem moduleAdjunction_normalized
    {T V : Scheme.{u}} (a : T ⟶ V)
    (R : Sheaf (ProEt.topology V) CommRingCat.{u + 1})
    (S : Sheaf (ProEt.topology T) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage a CommRingCat.{u + 1}).obj R ≅ S) :
    proEtaleRingModuleAdjunctionNormalized a R S c
      (proEtaleRingModuleAdjunction a R S c) := by
  unfold proEtaleRingModuleAdjunctionNormalized
  intro M U m
  rw [← (proEtaleRingModuleAdjunction a R S c).homEquiv_id]
  obtain ⟨z, hz, he⟩ := (Classical.choose_spec
    (proEtaleRingModuleAdjunction_existsUnique a R S c)).1 M _ (𝟙 _)
  dsimp only [proEtaleRingModuleAdjunction]
  erw [he]
  rw [Adjunction.homEquiv_unit]
  change z.val.app _
    (((SheafOfModules.pullbackPushforwardAdjunction
      (proEtaleModelRingUnit a R)).unit.app ((proEtaleModuleToModel _).obj M)).val.app
        (AsSmall.up.op.obj (Opposite.op U)) m) = _
  erw [hz]
  unfold proEtaleRingModuleUnitSection
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem ambientData_exists
    {V W Z : Scheme.{u}} (h : Z ⟶ W) (k : W ⟶ V)
    (RV : Sheaf (ProEt.topology V) CommRingCat.{u + 1})
    (RW : Sheaf (ProEt.topology W) CommRingCat.{u + 1})
    (RZ : Sheaf (ProEt.topology Z) CommRingCat.{u + 1})
    (ck : (proEtaleSheafInverseImage k CommRingCat.{u + 1}).obj RV ≅ RW)
    (ch : (proEtaleSheafInverseImage h CommRingCat.{u + 1}).obj RW ≅ RZ) :
    Nonempty (PullbackData h k RV RW RZ ck ch
      (proEtaleRingCompositeCoefficients h k RV RW RZ ck ch) rfl
      (proEtaleCanonicalDerivedPullbackComparison h k RV RW RZ ck ch)) := by
  unfold proEtaleCanonicalDerivedPullbackComparison
  extract_lets chk hex
  exact ComparisonWitnesses.nonempty _ _ _ _ _ _ _ (Classical.choose_spec hex)

private theorem normalizedAdj_eq_actual
    {T V : Scheme.{u}} (f : T ⟶ V)
    (R : Sheaf (ProEt.topology V) CommRingCat.{u + 1})
    (S : Sheaf (ProEt.topology T) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R ≅ S)
    (a : proEtaleRingModulePullback f R S c ⊣ proEtaleRingModuleDirectImage f R S c)
    (ha : proEtaleRingModuleAdjunctionNormalized f R S c a) :
    a = proEtaleRingModuleAdjunction f R S c := by
  have hb := moduleAdjunction_normalized f R S c
  unfold proEtaleRingModuleAdjunctionNormalized at ha hb
  apply Adjunction.ext
  apply NatTrans.ext
  funext M
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  ext m
  exact (ha M U.unop m).trans (hb M U.unop m).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem ambientData_transport
    {V W Z : Scheme.{u}} (h : Z ⟶ W) (k : W ⟶ V)
    (RV : Sheaf (ProEt.topology V) CommRingCat.{u + 1})
    (RW : Sheaf (ProEt.topology W) CommRingCat.{u + 1})
    (RZ : Sheaf (ProEt.topology Z) CommRingCat.{u + 1})
    (ck : (proEtaleSheafInverseImage k CommRingCat.{u + 1}).obj RV ≅ RW)
    (ch : (proEtaleSheafInverseImage h CommRingCat.{u + 1}).obj RW ≅ RZ)
    (c : (proEtaleSheafInverseImage (h ≫ k) CommRingCat.{u + 1}).obj RV ≅ RZ)
    (hc : proEtaleRingCompositeCoefficients h k RV RW RZ ck ch = c) :
    Nonempty (PullbackData h k RV RW RZ ck ch c hc
      (eqToIso (congrArg (proEtaleRingDerivedPullback (h ≫ k) RV RZ) hc.symm) ≪≫
        proEtaleCanonicalDerivedPullbackComparison h k RV RW RZ ck ch)) := by
  subst c
  simpa only [eqToIso_refl, Iso.refl_trans] using
    ambientData_exists h k RV RW RZ ck ch

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The specified derived composition is the localization of the conjugate
of a section-normalized ordinary direct-image compositor. -/
theorem proEtaleCanonicalDerivedPullback_normalization
    {V W Z : Scheme.{u}} (h : Z ⟶ W) (k : W ⟶ V)
    (RV : Sheaf (ProEt.topology V) CommRingCat.{u + 1})
    (RW : Sheaf (ProEt.topology W) CommRingCat.{u + 1})
    (RZ : Sheaf (ProEt.topology Z) CommRingCat.{u + 1})
    (ck : (proEtaleSheafInverseImage k CommRingCat.{u + 1}).obj RV ≅ RW)
    (ch : (proEtaleSheafInverseImage h CommRingCat.{u + 1}).obj RW ≅ RZ)
    (c : (proEtaleSheafInverseImage (h ≫ k) CommRingCat.{u + 1}).obj RV ≅ RZ)
    (hc : proEtaleRingCompositeCoefficients h k RV RW RZ ck ch = c)
    (d : proEtaleRingModuleDirectImage h RW RZ ch ⋙
      proEtaleRingModuleDirectImage k RV RW ck ≅
        proEtaleRingModuleDirectImage (h ≫ k) RV RZ c)
    (hd : ∀ (N : proEtaleRingModules Z RZ) (U : V.ProEt)
      (m : ((proEtaleRingModuleDirectImage h RW RZ ch ⋙
        proEtaleRingModuleDirectImage k RV RW ck).obj N).val.obj (Opposite.op U)),
      (d.hom.app N).val.app (Opposite.op U) m =
        N.val.map ((MorphismProperty.Over.pullbackComp
          (P := @WeaklyEtale) (Q := ⊤) h k).hom.app U).op m) :
    eqToIso (congrArg (proEtaleRingDerivedPullback (h ≫ k) RV RZ) hc.symm) ≪≫
        proEtaleCanonicalDerivedPullbackComparison h k RV RW RZ ck ch =
      Functor.mapDerivedCategoryNatIso
        (Adjunction.leftAdjointCompIso (proEtaleRingModuleAdjunction k RV RW ck)
          (proEtaleRingModuleAdjunction h RW RZ ch)
          (proEtaleRingModuleAdjunction (h ≫ k) RV RZ c) d).symm ≪≫
        (Functor.mapDerivedCategoryCompIso (proEtaleRingModulePullback k RV RW ck)
          (proEtaleRingModulePullback h RW RZ ch)).symm := by
  let D := Classical.choice (ambientData_transport h k RV RW RZ ck ch c hc)
  have hk := normalizedAdj_eq_actual k RV RW ck D.adjk D.nk
  have hh := normalizedAdj_eq_actual h RW RZ ch D.adjh D.nh
  have hcomp := normalizedAdj_eq_actual (h ≫ k) RV RZ c D.adjc D.nc
  have hD : D.d = d := by
    apply Iso.ext
    apply NatTrans.ext
    funext N
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    ext m
    exact (D.hd N U.unop m).trans (hd N U.unop m).symm
  have heq := congrArg₂ conjugateIsoEquiv
    (congrArg₂ Adjunction.comp hk hh) hcomp
  have ha := (congrArg (fun e ↦ e D.a) heq).symm.trans (D.ha.trans hD)
  have hleft : D.a = (Adjunction.leftAdjointCompIso
      (proEtaleRingModuleAdjunction k RV RW ck)
      (proEtaleRingModuleAdjunction h RW RZ ch)
      (proEtaleRingModuleAdjunction (h ≫ k) RV RZ c) d).symm := by
    apply (conjugateIsoEquiv
      ((proEtaleRingModuleAdjunction k RV RW ck).comp
        (proEtaleRingModuleAdjunction h RW RZ ch))
      (proEtaleRingModuleAdjunction (h ≫ k) RV RZ c)).injective
    rw [ha]
    exact ((conjugateIsoEquiv
      ((proEtaleRingModuleAdjunction k RV RW ck).comp
        (proEtaleRingModuleAdjunction h RW RZ ch))
      (proEtaleRingModuleAdjunction (h ≫ k) RV RZ c)).apply_symm_apply d).symm
  have e := pullbackData_comparison h k RV RW RZ ck ch c hc _ D
  exact e.trans (congrArg (fun a ↦ Functor.mapDerivedCategoryNatIso a ≪≫
    (Functor.mapDerivedCategoryCompIso (proEtaleRingModulePullback k RV RW ck)
      (proEtaleRingModulePullback h RW RZ ch)).symm) hleft)

end AlgebraicGeometry.Scheme
