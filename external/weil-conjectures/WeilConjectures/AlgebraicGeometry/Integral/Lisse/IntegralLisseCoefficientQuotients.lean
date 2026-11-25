/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Integral.Lisse.IntegralLisseReductionData
import WeilConjectures.NumberTheory.Padics.IntegersProfiniteTower
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
import Mathlib.RingTheory.Ideal.Quotient.Index
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Algebra.Ring.Pi
import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Topology.Compactness.Compact
import WeilConjectures.NumberTheory.Padics.IntegersCosetBasis
import Mathlib.Topology.Bases
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.NumberTheory.Padics.ProperSpace
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvr
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Localization.FractionRing
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrCore
import Mathlib.Analysis.Normed.Algebra.Ultra
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Algebra.Valued.LocallyCompact
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorization
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorizationUnique
import WeilConjectures.Mathlib.RingTheory.OrderOfVanishing.Noetherian
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits
import Mathlib.Algebra.Category.ModuleCat.Kernels
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-!
# IntegralLisseCoefficientQuotients

## References

* Bhatt--Scholze, Lemma 6.8.2 and Proposition 6.8.4(1)
* Bhatt--Scholze, Lemma 6.8.2(1)
* Bhatt--Scholze, Lemma 6.8.2(1), pp. 58--59
* Stacks Tag 03EK
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale

variable (l : ℕ) [Fact l.Prime] (E : Type (u + 1)) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : Scheme.{u})

/-- Reduction on continuous coefficient sections is surjective and has the scalar image
as its kernel. -/
theorem integralLisseCoefficient_sectionwise (n : ℕ) :
    let M := SheafOfModules.unit (integralLisseRing l E X)
    let q := integralLisseRingMap l E X
      ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
        (integralLisseReduction l E X n))
    let f := integralLisseScalar l E X M
      (Padic.coefficientExtensionUniformizer l E ^ (n + 1))
    ∀ U : X.ProEtᵒᵖ, Function.Surjective (q.val.app U).hom ∧
      Function.Exact (f.val.app U).hom (q.val.app U).hom := by
  classical
  let := spectralNorm.normedField ℚ_[l] E
  let A := Padic.coefficientExtensionIntegers l E
  let I := Padic.coefficientExtensionIdeal l E (n + 1)
  let a : A := Padic.coefficientExtensionUniformizer l E ^ (n + 1)
  have hI : I = Ideal.span {a} := Ideal.span_singleton_pow _ _
  obtain ⟨e, he, heHome⟩ :=
    (Padic.coefficientExtension_integers_profinite_tower.{u + 1, u + 1} l E).1
  have hq : @Continuous _ _ (inferInstance : TopologicalSpace A) ⊥
      (Ideal.Quotient.mk I) := by
    let : ∀ k : ℕ, TopologicalSpace (Padic.coefficientExtensionRing l E (k + 1)) :=
      fun _ ↦ ⊥
    have hc := (continuous_apply n).comp (continuous_subtype_val.comp heHome.continuous)
    exact hc.congr (fun x ↦ he x n)
  have hd : @Continuous _ _
      (inferInstance : TopologicalSpace (Padic.coefficientExtensionRing l E (n + 1))) ⊥
      id := by
    exact (@Topology.IsQuotientMap.continuous_iff A
      (Padic.coefficientExtensionRing l E (n + 1))
      (Padic.coefficientExtensionRing l E (n + 1))
      (Ideal.Quotient.mk I) id _ _ ⊥
      (QuotientRing.isOpenQuotientMap_mk I).isQuotientMap).mpr hq
  let M := SheafOfModules.unit (integralLisseRing l E X)
  let q := integralLisseRingMap l E X
    ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
      (integralLisseReduction l E X n))
  let f := integralLisseScalar l E X M a
  have hqapp (U : X.ProEtᵒᵖ) (s : M.val.obj U) (x : U.unop.left) :
      ((q.val.app U) s).down x = Ideal.Quotient.mk I (s.down x) := by
    change Ideal.Quotient.mk I (s.down x) * 1 = _
    exact mul_one _
  have hfapp (U : X.ProEtᵒᵖ) (s : M.val.obj U) (x : U.unop.left) :
      ((f.val.app U) s).down x = a * s.down x := rfl
  have hs (U : X.ProEtᵒᵖ) : Function.Surjective (q.val.app U).hom := by
    intro s
    let lift := Function.surjInv (Ideal.Quotient.mk_surjective (I := I))
    have hscont : @Continuous _ _ _ ⊥ s.down := by
      apply continuous_def.mpr
      intro V hV
      exact s.down.continuous.isOpen_preimage _ (continuous_def.mp hd V hV)
    have hlift : @Continuous _ _ ⊥ _ lift := by
      apply continuous_def.mpr
      intro V hV
      trivial
    have hc : Continuous (fun x : U.unop.left ↦ lift (s.down x)) := by
      apply continuous_def.mpr
      intro V hV
      exact continuous_def.mp hscont (lift ⁻¹' V) trivial
    refine ⟨ULift.up ⟨fun x ↦ lift (s.down x), hc⟩, ?_⟩
    apply ULift.ext
    apply ContinuousMap.ext
    intro x
    rw [hqapp]
    exact Function.surjInv_eq _ _
  have hex (U : X.ProEtᵒᵖ) :
      Function.Exact (f.val.app U).hom (q.val.app U).hom := by
    intro s
    constructor
    · intro hs
      have hmem (x : U.unop.left) : s.down x ∈ I := by
        apply Ideal.Quotient.eq_zero_iff_mem.mp
        have h := congrArg (fun t ↦ t.down x) hs
        rw [hqapp] at h
        exact h
      have hdiv (x : U.unop.left) : ∃ b : A, a * b = s.down x := by
        have h := hmem x
        rw [hI, Ideal.mem_span_singleton] at h
        obtain ⟨b, hb⟩ := h
        exact ⟨b, hb.symm⟩
      by_cases ha : a = 0
      · refine ⟨0, ?_⟩
        apply ULift.ext
        apply ContinuousMap.ext
        intro x
        rw [hfapp, ha, zero_mul]
        obtain ⟨b, hb⟩ := hdiv x
        rw [ha, zero_mul] at hb
        exact hb
      · have haE : (a : E) ≠ 0 := by
          intro h
          apply ha
          exact Subtype.ext h
        have hval (x : U.unop.left) : (s.down x : E) / (a : E) ∈ A := by
          obtain ⟨b, hb⟩ := hdiv x
          have hbE := congrArg (fun z : A ↦ (z : E)) hb
          change (a : E) * (b : E) = (s.down x : E) at hbE
          rw [← hbE, mul_div_cancel_left₀ _ haE]
          exact b.property
        let g : C(U.unop.left, A) :=
          ⟨fun x ↦ ⟨(s.down x : E) / (a : E), hval x⟩,
            ((continuous_subtype_val.comp s.down.continuous).div_const _).subtype_mk _⟩
        refine ⟨ULift.up g, ?_⟩
        apply ULift.ext
        apply ContinuousMap.ext
        intro x
        rw [hfapp]
        apply Subtype.ext
        change (a : E) * ((s.down x : E) / (a : E)) = (s.down x : E)
        exact mul_div_cancel₀ _ haE
    · rintro ⟨t, rfl⟩
      apply ULift.ext
      apply ContinuousMap.ext
      intro x
      rw [hqapp, hfapp, map_mul]
      have hz : Ideal.Quotient.mk I a = 0 := by
        apply Ideal.Quotient.eq_zero_iff_mem.mpr
        rw [hI]
        exact Ideal.subset_span (Set.mem_singleton a)
      rw [hz, zero_mul]
      rfl
  exact fun U ↦ ⟨hs U, hex U⟩

/-- Pointwise reduction of the coefficient unit is the sheaf scalar cokernel. -/
theorem integralLisseCoefficient_quotients (n : ℕ) :
    IsIntegralLisseQuotient l E X
      (Padic.coefficientExtensionUniformizer l E ^ (n + 1))
      (integralLisseRingMap l E X
        ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
          (integralLisseReduction l E X n))) := by
  let M := SheafOfModules.unit (integralLisseRing l E X)
  let q := integralLisseRingMap l E X
    ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
      (integralLisseReduction l E X n))
  let f := integralLisseScalar l E X M
    (Padic.coefficientExtensionUniformizer l E ^ (n + 1))
  have hs (U : X.ProEtᵒᵖ) : Function.Surjective (q.val.app U).hom :=
    (integralLisseCoefficient_sectionwise l E X n U).1
  have hex (U : X.ProEtᵒᵖ) :
      Function.Exact (f.val.app U).hom (q.val.app U).hom :=
    (integralLisseCoefficient_sectionwise l E X n U).2
  have hzero : f ≫ q = 0 := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.hom_ext
    exact LinearMap.ext (fun s ↦ (hex U).apply_apply_eq_zero s)
  refine ⟨hzero, ⟨isColimitOfReflects (SheafOfModules.forget _) ?_⟩⟩
  apply PresheafOfModules.evaluationJointlyReflectsColimits
  intro U
  let ev := SheafOfModules.forget (integralLisseRing l E X) ⋙
    PresheafOfModules.evaluation _ U
  exact (isColimitMapCoconeCoforkEquiv' ev hzero).symm
    (ModuleCat.isColimitCokernelCofork _ _ (hex U) (hs U))

end AlgebraicGeometry.ProEtale
