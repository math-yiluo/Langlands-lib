/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Pur.PurCompletedReindexingData
import WeilConjectures.AlgebraicGeometry.AdicCoefficientDatum.CompletedOrdinaryComparisons

/-! # PurCompletedModuleReindexing
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option linter.privateModule false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
universe t
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
attribute [local irreducible] completedAdicChangeData completedReductionCoefficient
attribute [local irreducible] proEtaleRingModulePullback
attribute [local irreducible] Functor.mapDerivedCategory Functor.rightDerivedFunctor
attribute [local irreducible] CochainComplex.IsKFlatIndependentCoefficients
attribute [local instance 2000] reductionModulesHasDerivedCategory reductionTowerHasDerivedCategory
variable {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A)

private def modulePullComp {U V W : Scheme.{t}} (h : U ⟶ V) (g : V ⟶ W) :
    proEtaleRingModulePullback (h ≫ g) (d.completedRing W) (d.completedRing U)
        (d.integralRingIso (h ≫ g)) ≅
      proEtaleRingModulePullback g (d.completedRing W) (d.completedRing V)
        (d.integralRingIso g) ⋙
      proEtaleRingModulePullback h (d.completedRing V) (d.completedRing U)
        (d.integralRingIso h) :=
  eqToIso (congrArg
    (proEtaleRingModulePullback (h ≫ g) (d.completedRing W) (d.completedRing U))
      (d.integralRingIso_comp h g)) ≪≫
    exchangeModuleComposition h g (d.completedRing W) (d.completedRing V)
      (d.completedRing U) (d.integralRingIso g) (d.integralRingIso h)

private def modulePullId (T : Scheme.{t}) :
    proEtaleRingModulePullback (𝟙 T) (d.completedRing T) (d.completedRing T)
      (d.integralRingIso (𝟙 T)) ≅ 𝟭 _ :=
  (proEtaleRingModuleAdjunction (𝟙 T) (d.completedRing T) (d.completedRing T)
    (d.integralRingIso (𝟙 T))).leftAdjointIdIso (d.modulePushId T)

private def moduleEquivalence {T' T : Scheme.{t}} (u : T' ⟶ T) [IsIso u] :
    reductionModules T (d.completedRing T) ≌ reductionModules T' (d.completedRing T') :=
  CategoryTheory.Equivalence.mk
    (proEtaleRingModulePullback u (d.completedRing T) (d.completedRing T')
      (d.integralRingIso u))
    (proEtaleRingModulePullback (inv u) (d.completedRing T') (d.completedRing T)
      (d.integralRingIso (inv u)))
    ((modulePullId d T).symm ≪≫
      eqToIso (congrArg (fun f : T ⟶ T ↦
        proEtaleRingModulePullback f (d.completedRing T) (d.completedRing T)
          (d.integralRingIso f)) (IsIso.inv_hom_id u).symm) ≪≫
      modulePullComp d (inv u) u)
    ((modulePullComp d u (inv u)).symm ≪≫
      eqToIso (congrArg (fun f : T' ⟶ T' ↦
        proEtaleRingModulePullback f (d.completedRing T') (d.completedRing T')
          (d.integralRingIso f)) (IsIso.hom_inv_id u)) ≪≫
      modulePullId d T')

end AlgebraicGeometry.Scheme
