/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Integral.IntegralStratifiedPerfectModelsSupplement
public import WeilConjectures.AlgebraicGeometry.AdicCoefficientDatum.CompletedPullback
import all WeilConjectures.AlgebraicGeometry.Integral.IntegralPullbackScalarComparison
import WeilConjectures.AlgebraicGeometry.AdicCoefficientDatum.CompletedOrdinaryComparisons
import all WeilConjectures.AlgebraicGeometry.Perfect.PerfectChartTensorComparison
import WeilConjectures.CategoryTheory.LocalizedModuleExactForSystems
import WeilConjectures.Algebra.Homology.SmoothPurity.LocalizedModuleExactIndependent
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import all WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement

/-! # Comparison of integral chart and ordinary datum pullbacks

## References

* Bhatt--Scholze, Proposition 6.6.11, slice comparison
* Stacks Tag 03D8
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

attribute [local irreducible] derivedPullbackScalarIso

private def sliceDerivedIso {X : Scheme.{u}}
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) (V : X.ProEt)
    (K : DerivedCategory (pbcModules X R)) :
    (SheafOfModules.localizedSystemRestriction.{u + 1, u, u + 1}
      R V).mapDerivedCategory.obj K ≅
      ringedSiteDerivedRestrictionOfUniverses
        ((adicLisseForget X).obj R) V K :=
  ((SheafOfModules.localizedSystemRestriction.{u + 1, u, u + 1}
    R V).mapDerivedCategory.mapIso (DerivedCategory.Q.objObjPreimageIso K)).symm ≪≫
    (SheafOfModules.localizedSystemRestriction.{u + 1, u, u + 1}
      R V).mapDerivedCategoryFactors.app (DerivedCategory.Q.objPreimage K)

attribute [local irreducible] sliceDerivedIso

private def normalizedLocalIso {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) {X Y : Scheme.{u}} (g : X ⟶ Y) (V : X.ProEt)
    (K : DerivedCategory (pbcModules Y (pbcAdicCompletion Y d))) :
    integralLocalDerived g (pbcAdicCompletion Y d) V K ≅
      (localScalar d g V).functor.mapDerivedCategory.obj
        ((SheafOfModules.localizedSystemRestriction.{u + 1, u, u + 1}
          (pbcAdicCompletion X d) V).mapDerivedCategory.obj ((d.pull g).obj K)) := by
  let c := (sheafCompose (ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso (d.integralRingIso g)
  let E := proEtaleScalarEquivalence X c
  let e := scalarEquivalence ((ProEt.topology X).over V)
    (((ProEt.topology X).overPullback RingCat.{u + 1} V).mapIso c)
  let F := SheafOfModules.localizedSystemRestriction.{u + 1, u, u + 1}
    ((adicTowerInverseImage g).obj (pbcAdicCompletion Y d)) V
  let H := SheafOfModules.localizedSystemRestriction.{u + 1, u, u + 1}
    (pbcAdicCompletion X d) V
  have : E.functor.Additive := inferInstanceAs
    (SheafOfModules.restrictScalars c.hom).Additive
  have : e.functor.Additive := inferInstanceAs
    (SheafOfModules.restrictScalars
      (((ProEt.topology X).overPullback RingCat.{u + 1} V).mapIso c).hom).Additive
  let s : E.functor ⋙ F ≅ H ⋙ e.functor := scalarOverIso c V
  let ds := Functor.mapDerivedCategoryCompIso E.functor F ≪≫
    Functor.mapDerivedCategoryNatIso s ≪≫
    (Functor.mapDerivedCategoryCompIso H e.functor).symm
  let p : proEtaleRingDerivedPullback g (pbcAdicCompletion Y d)
      (pbcAdicCompletion X d) (d.integralRingIso g) ⋙ E.functor.mapDerivedCategory ≅
        adicTowerPullback g (pbcAdicCompletion Y d) :=
    derivedPullbackScalarIso g (pbcAdicCompletion Y d)
    (pbcAdicCompletion X d) (d.integralRingIso g)
  let L := (proEtaleRingDerivedPullback g (pbcAdicCompletion Y d)
    (pbcAdicCompletion X d) (d.integralRingIso g)).obj K
  let t : F.mapDerivedCategory.obj (E.functor.mapDerivedCategory.obj L) ≅
      e.functor.mapDerivedCategory.obj (H.mapDerivedCategory.obj L) := ds.app L
  let r : F.mapDerivedCategory.obj ((adicTowerPullback g (pbcAdicCompletion Y d)).obj K) ≅
      F.mapDerivedCategory.obj (E.functor.mapDerivedCategory.obj L) :=
    F.mapDerivedCategory.mapIso (p.app K).symm
  exact (sliceDerivedIso _ V _).symm ≪≫ r ≪≫ t

attribute [local irreducible] normalizedLocalIso localScalar
attribute [local irreducible] AdicCoefficientDatum.pullComp

private theorem datumChartEquivalence {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) {S : Scheme.{u}} (U : S.ProEt) :
    ∃ e : DerivedCategory (pbcModules U.left (pbcAdicCompletion U.left d)) ≌
        DerivedCategory (SheafOfModules.{u + 1}
          (((adicLisseForget S).obj (pbcAdicCompletion S d)).over U)),
      Nonempty (d.pull U.hom ⋙ e.functor ≅
        (SheafOfModules.localizedSystemRestriction.{u + 1, u, u + 1}
          (pbcAdicCompletion S d) U).mapDerivedCategory) := by
  obtain ⟨q, ⟨hq⟩⟩ := chartDerivedEquivalence U (pbcAdicCompletion S d)
  let c := (adicLisseForget U.left).mapIso (d.integralRingIso U.hom)
  let r := proEtaleScalarEquivalence U.left c
  have : r.functor.Additive := inferInstanceAs
    (SheafOfModules.restrictScalars c.hom).Additive
  let e := r.mapDerivedCategory.trans q
  refine ⟨e, ⟨?_⟩⟩
  exact (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (derivedPullbackScalarIso U.hom (pbcAdicCompletion S d)
        (pbcAdicCompletion U.left d) (d.integralRingIso U.hom)) q.functor ≪≫ hq

/-- An isomorphism on the integral pro-etale chart gives an ordinary pullback isomorphism. -/
theorem integralLocalDerived_pullbackIso {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) {T S : Scheme.{u}} (g : S ⟶ T) (U : S.ProEt)
    (K L : d.derived T)
    (h : integralLocalDerived g (pbcAdicCompletion T d) U K ≅
      integralLocalDerived g (pbcAdicCompletion T d) U L) :
    Nonempty ((d.pull (U.hom ≫ g)).obj K ≅ (d.pull (U.hom ≫ g)).obj L) := by
  let F := (localScalar d g U).functor.mapDerivedCategory
  obtain ⟨e, ⟨he⟩⟩ := datumChartEquivalence d U
  let h' := F.preimageIso ((normalizedLocalIso d g U K).symm ≪≫ h ≪≫
    normalizedLocalIso d g U L)
  let h'' := e.functor.preimageIso
    (he.app ((d.pull g).obj K) ≪≫ h' ≪≫ (he.app ((d.pull g).obj L)).symm)
  exact ⟨(d.pullComp U.hom g).app K ≪≫ h'' ≪≫ ((d.pullComp U.hom g).app L).symm⟩

end AlgebraicGeometry.Scheme
