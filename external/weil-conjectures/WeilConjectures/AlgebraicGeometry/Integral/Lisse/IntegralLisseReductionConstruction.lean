/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Integral.Lisse.IntegralLisseReductionData
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits

/-!
# Canonical scalar quotient towers

The objects are actual sheaf cokernels, and the completion is an actual sheaf limit.

## References

* Bhatt--Scholze, Proposition 6.8.4(1), pp. 58--59
* Bhatt--Scholze, Proposition 6.8.4(1), normalization of reductions
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale

variable (l : ℕ) [Fact l.Prime] (E : Type (u + 1)) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : Scheme.{u})

theorem integralLisseScalar_natural
    {M N : ringedSiteModules.{u + 1} (integralLisseRing l E X)} (f : M ⟶ N)
    (a : Padic.coefficientExtensionIntegers l E) :
    integralLisseScalar l E X M a ≫ f = f ≫ integralLisseScalar l E X N a := by
  ext U x
  exact (f.val.app U).hom.map_smul _ x

theorem integralLisseScalar_mul
    (M : ringedSiteModules.{u + 1} (integralLisseRing l E X))
    (a b : Padic.coefficientExtensionIntegers l E) :
    integralLisseScalar l E X M (a * b) =
      integralLisseScalar l E X M b ≫ integralLisseScalar l E X M a := by
  ext U x
  change (lisseIntegerConstantSized l E X U a * lisseIntegerConstantSized l E X U b) • x =
    lisseIntegerConstantSized l E X U a • (lisseIntegerConstantSized l E X U b • x)
  exact mul_smul _ _ x

/-- The positive scalar quotient at level `n` is a categorical cokernel. -/
def integralLisseCokernel
    (M : ringedSiteModules.{u + 1} (integralLisseRing l E X)) (n : ℕ) :=
  cokernel (integralLisseScalar l E X M (Padic.coefficientExtensionUniformizer l E ^ (n + 1)))

/-- The adjacent transition induced by the identity on the original module. -/
def integralLisseCokernelTransition
    (M : ringedSiteModules.{u + 1} (integralLisseRing l E X)) (n : ℕ) :
    integralLisseCokernel l E X M (n + 1) ⟶ integralLisseCokernel l E X M n :=
  cokernel.desc _ (cokernel.π _) (by
    rw [pow_succ, integralLisseScalar_mul, Category.assoc, cokernel.condition, comp_zero])

/-- All positive quotients of a module, with their canonical transition maps. -/
def integralLisseCokernelTower
    (M : ringedSiteModules.{u + 1} (integralLisseRing l E X)) :
    ℕᵒᵖ ⥤ ringedSiteModules.{u + 1} (integralLisseRing l E X) :=
  Functor.ofOpSequence (integralLisseCokernelTransition l E X M)

/-- The transition between two successive scalar quotients is itself the smaller scalar
quotient. This is purely a cokernel calculation and needs no local freeness. -/
theorem integralLisseCokernelTransition_quotient
    (M : ringedSiteModules.{u + 1} (integralLisseRing l E X)) (n : ℕ) :
    IsIntegralLisseQuotient l E X
      (Padic.coefficientExtensionUniformizer l E ^ (n + 1))
      (integralLisseCokernelTransition l E X M n) := by
  let a := Padic.coefficientExtensionUniformizer l E ^ (n + 1)
  let b := Padic.coefficientExtensionUniformizer l E ^ (n + 1 + 1)
  let p := cokernel.π (integralLisseScalar l E X M b)
  let t := integralLisseCokernelTransition l E X M n
  have hpt : p ≫ t = cokernel.π (integralLisseScalar l E X M a) := by
    exact cokernel.π_desc _ _ _
  have hnat : integralLisseScalar l E X M a ≫ p =
      p ≫ integralLisseScalar l E X (integralLisseCokernel l E X M (n + 1)) a :=
    integralLisseScalar_natural l E X p a
  have ht : Epi t := by
    have : Epi (p ≫ t) := by rw [hpt]; infer_instance
    exact epi_of_epi_fac (rfl : p ≫ t = p ≫ t)
  have hz : integralLisseScalar l E X (integralLisseCokernel l E X M (n + 1)) a ≫
      t = 0 := by
    apply (cancel_epi p).1
    rw [comp_zero, ← Category.assoc, ← hnat,
      Category.assoc, hpt, cokernel.condition]
  refine ⟨hz, ⟨CokernelCofork.IsColimit.ofπ' t hz ?_⟩⟩
  intro N k hk
  have hpk : integralLisseScalar l E X M a ≫ (p ≫ k) = 0 := by
    rw [← Category.assoc, hnat, Category.assoc,
      hk, comp_zero]
  refine ⟨cokernel.desc _ (p ≫ k) hpk, ?_⟩
  apply (cancel_epi p).1
  rw [← Category.assoc, hpt, cokernel.π_desc]

/-- The compatible family of quotient maps. -/
def integralLisseCokernelCone
    (M : ringedSiteModules.{u + 1} (integralLisseRing l E X)) :
    (Functor.const ℕᵒᵖ).obj M ⟶ integralLisseCokernelTower l E X M :=
  NatTrans.ofOpSequence (fun n ↦ cokernel.π _) (fun n ↦ by
    simp [integralLisseCokernelTower, integralLisseCokernelTransition])

/-- Maps of modules induce maps of the actual quotient towers. -/
def integralLisseCokernelMap
    {M N : ringedSiteModules.{u + 1} (integralLisseRing l E X)} (f : M ⟶ N) :
    integralLisseCokernelTower l E X M ⟶ integralLisseCokernelTower l E X N :=
  NatTrans.ofOpSequence
    (fun n ↦ cokernel.map _ _ f f (integralLisseScalar_natural l E X f _)) (fun n ↦ by
      apply (cancel_epi (cokernel.π _)).1
      simp [integralLisseCokernelTower, integralLisseCokernelTransition,
        cokernel.map, Category.assoc])

/-- The quotient-tower functor on the ambient module category. -/
def integralLisseCokernelFunctor :
    ringedSiteModules.{u + 1} (integralLisseRing l E X) ⥤
      (ℕᵒᵖ ⥤ ringedSiteModules.{u + 1} (integralLisseRing l E X)) where
  obj := integralLisseCokernelTower l E X
  map := integralLisseCokernelMap l E X
  map_id M := by
    apply NatTrans.ext
    funext n
    apply (cancel_epi (cokernel.π _)).1
    simp only [integralLisseCokernelMap, NatTrans.ofOpSequence_app, cokernel.map,
      cokernel.π_desc, Category.id_comp, NatTrans.id_app]
    exact (Category.comp_id _).symm
  map_comp f g := by
    apply NatTrans.ext
    funext n
    apply (cancel_epi (cokernel.π _)).1
    simp [integralLisseCokernelMap, cokernel.map, Category.assoc]

/-- The map induced between two cokernels of the same scalar is invertible. -/
theorem isIso_integralLisseQuotient_desc
    {M N : ringedSiteModules.{u + 1} (integralLisseRing l E X)}
    (a : Padic.coefficientExtensionIntegers l E) (p : M ⟶ N)
    (h : IsIntegralLisseQuotient l E X a p) :
    IsIso (cokernel.desc (integralLisseScalar l E X M a) p h.choose) := by
  let e := (cokernelIsCokernel (integralLisseScalar l E X M a)).coconePointUniqueUpToIso
    h.choose_spec.some
  have he : cokernel.desc (integralLisseScalar l E X M a) p h.choose = e.hom := by
    apply (cancel_epi (cokernel.π _)).1
    exact (cokernel.π_desc _ _ _).trans
      ((IsColimit.comp_coconePointUniqueUpToIso_hom
        (cokernelIsCokernel (integralLisseScalar l E X M a)) h.choose_spec.some
        WalkingParallelPair.one).symm)
  rw [he]
  infer_instance

end AlgebraicGeometry.ProEtale
