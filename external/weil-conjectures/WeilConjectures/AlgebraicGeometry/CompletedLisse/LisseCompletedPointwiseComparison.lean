/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CompletedLisse.LisseCompletedSystemData
import WeilConjectures.AlgebraicGeometry.CompletedLisse.LisseCompletedSystemData
import all WeilConjectures.AlgebraicGeometry.Completed.Adic.CompletedAdicCoefficientDatumSupplement
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import WeilConjectures.Algebra.Homology.SmoothPurity.PullbackExistsOfUniverses
import WeilConjectures.AlgebraicGeometry.Integral.Lisse.IntegralLisseReductionConstruction
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous

/-! # The comparison at one coefficient field and one scheme. -/

@[expose] public noncomputable section

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.ProEtale.CompletedLisse
variable (l : ℕ) [Fact l.Prime]

private def restrictionRoundTrip
    {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
    {R S : Sheaf J RingCat.{u + 1}} (c : R ≅ S) :
    SheafOfModules.restrictScalars.{u + 1} c.hom ⋙
      SheafOfModules.restrictScalars c.inv ≅ 𝟭 (SheafOfModules.{u + 1} S) :=
  NatIso.ofComponents (fun M ↦ (SheafOfModules.fullyFaithfulForget S).preimageIso
    (PresheafOfModules.isoMk (fun U ↦
      (ModuleCat.restrictScalarsComp'App (c.inv.hom.app U).hom
        (c.hom.hom.app U).hom (RingHom.id _) (by
          have h := congr_app (congrArg (fun f : S ⟶ S ↦ f.hom) c.inv_hom_id) U
          exact (congrArg RingCat.Hom.hom h).symm) (M.val.obj U)).symm ≪≫
        ModuleCat.restrictScalarsId'App (RingHom.id _) rfl (M.val.obj U))
      (by intro U V f; ext x; rfl)))
    (by intro M N f; ext U x; rfl)

private def restrictionEquivalence
    {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
    {R S : Sheaf J RingCat.{u + 1}} (c : R ≅ S) :
    SheafOfModules.{u + 1} S ≌ SheafOfModules.{u + 1} R where
  functor := SheafOfModules.restrictScalars c.hom
  inverse := SheafOfModules.restrictScalars c.inv
  unitIso := (restrictionRoundTrip c).symm
  counitIso := restrictionRoundTrip c.symm
  functor_unitIso_comp M := by ext U x; rfl

private def restrictionUnitIso
    {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
    {R S : Sheaf J RingCat.{u + 1}} (c : R ≅ S) :
    SheafOfModules.unit R ≅ (SheafOfModules.restrictScalars c.hom).obj
      (SheafOfModules.unit S) where
  hom := ⟨PresheafOfModules.homMk
    (Functor.whiskerRight c.hom.hom (forget₂ RingCat AddCommGrpCat))
    (fun U r x ↦ (c.hom.hom.app U).hom.map_mul r x)⟩
  inv := ⟨PresheafOfModules.homMk
    (Functor.whiskerRight c.inv.hom (forget₂ RingCat AddCommGrpCat)) (by
      intro U r x
      change S.obj.obj U at x
      change c.inv.hom.app U (c.hom.hom.app U r * x) = r * c.inv.hom.app U x
      rw [map_mul]
      have h := ConcreteCategory.congr_hom
        (congr_app (congrArg (fun f : R ⟶ R ↦ f.hom) c.hom_inv_id) U) r
      change c.inv.hom.app U (c.hom.hom.app U r) = r at h
      rw [h])⟩
  hom_inv_id := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact ConcreteCategory.congr_hom
      (congr_app (congrArg (fun f : R ⟶ R ↦ f.hom) c.hom_inv_id) U) x
  inv_hom_id := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact ConcreteCategory.congr_hom
      (congr_app (congrArg (fun f : S ⟶ S ↦ f.hom) c.inv_hom_id) U) x

private theorem restriction_finiteLocallyFree
    {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
    [∀ U, HasSheafify (J.over U) AddCommGrpCat.{u + 1}]
    [∀ U, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
    {R S : Sheaf J RingCat.{u + 1}} (c : R ≅ S)
    (M : SheafOfModules.{u + 1} S) [hM : M.IsFiniteLocallyFree] :
    ((SheafOfModules.restrictScalars c.hom).obj M).IsFiniteLocallyFree := by
  obtain ⟨q, hq, hf⟩ := hM.exists_localGeneratorsData
  let := hq
  let := hf
  let κ (i : q.I) := (q.generators i).I
  let (i : q.I) : Finite (κ i) := by
    have := hf.isFiniteType i
    infer_instance
  apply SheafOfModules.isFiniteLocallyFree_of_exists_over_iso_free q.X q.coversTop κ
  intro i
  let ci : R.over (q.X i) ≅ S.over (q.X i) :=
    (J.overPullback RingCat (q.X i)).mapIso c
  let E := restrictionEquivalence ci
  exact ⟨E.functor.mapIso (asIso (q.generators i).π).symm ≪≫
    (SheafOfModules.mapFreeIso E.functor (κ i) (restrictionUnitIso ci)).symm⟩

end AlgebraicGeometry.ProEtale.CompletedLisse
