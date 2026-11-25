/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.AlgebraicGeometry.TorsionEtaleSheaf
public import Mathlib.Algebra.Category.Grp.ZModuleEquivalence
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Ring.ULift
import all WeilConjectures.AlgebraicGeometry.ConstructibleModuleUnderlyingSets
import WeilConjectures.AlgebraicGeometry.EtalePullbackForgetModules
import WeilConjectures.AlgebraicGeometry.TorsionSheafCharacterizations
import WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteStalksComparison
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk
import Mathlib.GroupTheory.FiniteAbelian.Basic

/-! # Constructibility with integral coefficients: forward implication

Source: Stacks Project Tags 03RW and 095E.
(blueprint: q1-constructible-integral-coefficients-forward).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- The counit of the equivalence between integral modules and abelian groups identifies
an abelian sheaf with the underlying abelian sheaf of its integral coefficient transport.
The change to the universe-lifted ring leaves the underlying group unchanged.
Source: the coefficient comparison in Stacks Project Tag 03RW.
(blueprint: q1-constructible-integral-coefficients-forward) -/
private theorem integralAbIso {X : Scheme.{u}}
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    let E := (forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1}).inv ⋙
      ModuleCat.restrictScalars (ULift.ringEquiv : ULift.{u + 1} ℤ ≃+* ℤ).toRingHom
    Nonempty ((sheafCompose X.smallEtaleTopology
      (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) AddCommGrpCat.{u + 1})).obj
        ((sheafCompose X.smallEtaleTopology E).obj F) ≅ F) := by
  dsimp only
  let U := forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1}
  let e := U.asEquivalence.counitIso
  exact ⟨(fullyFaithfulSheafToPresheaf _ _).preimageIso
    (Functor.isoWhiskerLeft F.obj e ≪≫ Functor.rightUnitor F.obj)⟩

/-- Forward direction of `isConstructibleSheaf_integral_iff`.
The proof follows the constructible stratification comparison: a finitely generated
integral stalk is torsion by the torsion filtration, hence finite, and forgetting
module structure preserves local constancy and inverse-image stalks.
Source: Stacks Project Tags 03RW and 095E; blueprint q1-constructible-integral-coefficients.
(blueprint: q1-constructible-integral-coefficients-forward) -/
theorem isConstructibleSheaf_integral_forward {X : Scheme.{u}}
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : X.IsTorsionAbelianSheaf F) :
    let E := (forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1}).inv ⋙
      ModuleCat.restrictScalars (ULift.ringEquiv : ULift.{u + 1} ℤ ≃+* ℤ).toRingHom
    IsConstructibleSheaf ((sheafCompose X.smallEtaleTopology E).obj F) →
      IsConstructibleEtaleSheafOfSets
        ((sheafCompose X.smallEtaleTopology
          (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj F) := by
  classical
  dsimp only
  let E := (forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1}).inv ⋙
    ModuleCat.restrictScalars (ULift.ringEquiv : ULift.{u + 1} ℤ ≃+* ℤ).toRingHom
  let N := (sheafCompose X.smallEtaleTopology E).obj F
  intro hN
  let := hN
  obtain ⟨S, hS⟩ := hN.exists_stratification
  obtain ⟨eAb⟩ := integralAbIso F
  let eUF := (sheafCompose X.smallEtaleTopology
    (CategoryTheory.forget AddCommGrpCat.{u + 1})).mapIso eAb
  refine ⟨S, fun k ↦ ?_⟩
  let f := S.immersion k
  let Y := S.domain k
  let G := (Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) f).obj N
  let := hS k
  obtain ⟨ep⟩ := underlyingSetPullbackIso f N
  let es := (etaleSetPullback f).mapIso eUF.symm ≪≫ ep
  constructor
  · obtain ⟨d⟩ := IsLocallyConstantSheaf.nonempty_locallyConstantDatum (F := G)
    refine ⟨d.cover, fun i ↦ ?_⟩
    let := d.isConstant i
    have hc : ((sheafCompose Y.smallEtaleTopology
        (CategoryTheory.forget (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)))).obj G).over
          (d.cover.etalePrecoverageToEtale i) |>.IsConstant
            (Y.smallEtaleTopology.over (d.cover.etalePrecoverageToEtale i)) := by
      change ((sheafCompose (Y.smallEtaleTopology.over (d.cover.etalePrecoverageToEtale i))
        (CategoryTheory.forget (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)))).obj
          (G.over (d.cover.etalePrecoverageToEtale i))).IsConstant _
      infer_instance
    let := hc
    exact Sheaf.isConstant_congr _
      ((Y.smallEtaleTopology.overPullback (Type (u + 1))
        (d.cover.etalePrecoverageToEtale i)).mapIso es.symm)
  · refine isFiniteSheaf_of_finite_algClosed_stalks _ fun Ω _ _ t ↦ ?_
    let P := pointSmallEtale t
    let M := (P.sheafFiber (A := ModuleCat.{u + 1} (ULift.{u + 1} ℤ))).obj G
    let : Module.Finite (ULift.{u + 1} ℤ) M := (ModuleCat.isFinitelyGenerated_iff M).mp
      (IsFiniteSheaf.isFinitelyGenerated_sheafFiber Ω t)
    let : Module.Finite ℤ (ULift.{u + 1} ℤ) := Module.Finite.of_surjective
      (Algebra.linearMap ℤ (ULift.{u + 1} ℤ)) (by intro x; exact ⟨x.down, rfl⟩)
    let : Module.Finite ℤ M := Module.Finite.trans (ULift.{u + 1} ℤ) M
    let : AddGroup.FG M := Module.Finite.iff_addGroup_fg.mp inferInstance
    let U := forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) AddCommGrpCat.{u + 1}
    let : Limits.PreservesFilteredColimitsOfSize.{u, u} U :=
      Limits.preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} U
    obtain ⟨ea⟩ := Etale.pullback_forget_modules_iso (ULift.{u + 1} ℤ) f N
    let e₁ := (P.sheafFiberCompIso U).app G
    let e₂ := (P.sheafFiber (A := AddCommGrpCat.{u + 1})).mapIso ea
    let e₃ := (P.sheafFiber (A := AddCommGrpCat.{u + 1})).mapIso
      ((Etale.upperStar AddCommGrpCat.{u + 1} f).mapIso eAb)
    let e₄ := (Etale.upperStarCompSheafFiberIso AddCommGrpCat.{u + 1} f t).app F
    let e := e₁.symm ≪≫ e₂ ≪≫ e₃ ≪≫ e₄
    have ht := (isTorsionAbelianSheaf_characterizations F).2.mp hF Ω (t ≫ f)
    have hM : IsAddTorsion M := IsAddTorsion.of_surjective
      (f := e.addCommGroupIsoToAddEquiv.symm.toAddMonoidHom)
      e.addCommGroupIsoToAddEquiv.symm.surjective ht
    let : Finite M := AddCommGroup.finite_of_fg_isAddTorsion M hM
    let : Limits.PreservesFilteredColimitsOfSize.{u, u}
        (CategoryTheory.forget (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))) :=
      Limits.preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
    let ef := (P.sheafFiberCompIso
      (CategoryTheory.forget (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)))).app G
    let ee := (P.sheafFiber (A := Type (u + 1))).mapIso es ≪≫ ef
    exact Finite.of_equiv M ee.toEquiv.symm

end AlgebraicGeometry.Scheme
