/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IntegralQuotient.IntegralQuotientCoefficients
public import WeilConjectures.CategoryTheory.Integral.IntegralStratumHomFormula
public import WeilConjectures.AlgebraicGeometry.Cohomological.CohomologicalDimension
import all WeilConjectures.CategoryTheory.Integral.IntegralDualTorsionHeartSections
import all WeilConjectures.AlgebraicGeometry.DerivedNakayamaResolution

/-! Finite-local dual data for the continuous integral coefficient.
(blueprint: lem-sfb-integral-stratum-finite-cd-reductions).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj
attribute [local instance 20000] HasDerivedCategory.ofIsGrothendieckAbelian

namespace CategoryTheory

private theorem continuous_ring_eq_of_topology
    (B : Type u) [Ring B] (t₁ t₂ : TopologicalSpace B) (ht : t₁ = t₂)
    (h₁ : @IsTopologicalRing B t₁ _) (h₂ : @IsTopologicalRing B t₂ _) :
    @Profinite.continuousCoefficientRingSheaf.{u} B t₁ _ h₁ =
      @Profinite.continuousMapRingSheafOfUniverse.{u, u} B t₂ _ h₂ := by
  subst t₂
  rfl

private theorem integral_ring_sheaf_eq
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] :
    DerivedNakayama.integerRingSheaf l E =
      letI := spectralNorm.normedField (Padic l) E
      Profinite.continuousMapRingSheafOfUniverse.{u, u}
        (Padic.coefficientExtensionIntegers l E) := by
  apply continuous_ring_eq_of_topology
  exact congrArg (fun t : TopologicalSpace E ↦ TopologicalSpace.induced
    (fun x : Padic.coefficientExtensionIntegers l E ↦ (x : E)) t)
    (DerivedNakayama.coefficientTopology l E).symm

private theorem integral_bundle_eq
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] :
    Mon.mk (integralCoefficientRing l E) = sfbCondensedIntegers l E := by
  exact congrArg
    (fun R : Sheaf (coherentTopology Profinite.{u}) RingCat.{u + 1} ↦
      Mon.mk ((sheafCompose (coherentTopology Profinite.{u})
        (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj R))
    (integral_ring_sheaf_eq l E)

/-- The finite-local dual has Tor amplitude `[0,1]`, and its tensor with a classical
locally ell-power-torsion heart object has classical locally ell-power-torsion cohomology.
Source: blueprint latest, `part-six-operations/sec-constructibility-upper-shriek/
sec-ladic-summary/sec-i-heart/sk-prop-int-compactness/sk-lem-int-ext-bound.proof.md`,
dual-tensor and derived-sections bullets.
Proof: equality of the two coefficient topologies identifies their continuous-ring
presheaves and hence their bundled monoids. Transport the entire data predicate along
this equality. For the normalized presentation, the local two-term resolution and dual
pairing give Tor amplitude [0,1]. The finite-level classicality theorem and exact filtered
kernel colimits give classical torsion tensor cohomology. Finally use the equivalence of
the kernel-colimit and local formulations of ell-power torsion.
(blueprint: lem-sfb-integral-stratum-finite-cd-reductions). -/
theorem integralStratumFiniteCdReductions_heart_data
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (S : Scheme.{u}) [IsNoetherian S]
    (L : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
      (condensedRingObj (IntegralQuotient.integral l E) S))
    (hL : HasFiniteConstantLocalModel (IntegralQuotient.integral l E) S L)
    (F : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
      (condensedRingObj (IntegralQuotient.integral l E) S))
    (hF : IsClassicalAbelian F.X ∧
      IsEllPowerTorsionLocal l (Fact.out : l.Prime) F.X) :
    DerivedCategory.torAmplitudeIn _ 0 1
        (stratumModuleDual (IntegralQuotient.integral l E) S L) ∧
      ∀ r : ℤ,
        IsClassicalAbelian
          ((DerivedCategory.homologyFunctor _ r).obj
            (((derivedTensor (IntegralQuotient.integral l E) S).obj
              (stratumModuleDual (IntegralQuotient.integral l E) S L)).obj
              ((DerivedCategory.singleFunctor _ 0).obj F))).X ∧
        IsEllPowerTorsionLocal l (Fact.out : l.Prime)
          ((DerivedCategory.homologyFunctor _ r).obj
            (((derivedTensor (IntegralQuotient.integral l E) S).obj
              (stratumModuleDual (IntegralQuotient.integral l E) S L)).obj
              ((DerivedCategory.singleFunctor _ 0).obj F))).X := by
  let P (R : Mon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})) : Prop :=
    ∀ [IsCommMonObj R.X]
      (L : supportModules R.X S), HasFiniteConstantLocalModel R.X S L →
      ∀ (F : supportModules R.X S),
        IsClassicalAbelian F.X ∧ IsEllPowerTorsionLocal l (Fact.out : l.Prime) F.X →
        DerivedCategory.torAmplitudeIn _ 0 1 (stratumModuleDual R.X S L) ∧
        ∀ r : ℤ,
          IsClassicalAbelian
            ((DerivedCategory.homologyFunctor _ r).obj
              (((derivedTensor R.X S).obj (stratumModuleDual R.X S L)).obj
                ((DerivedCategory.singleFunctor _ 0).obj F))).X ∧
          IsEllPowerTorsionLocal l (Fact.out : l.Prime)
            ((DerivedCategory.homologyFunctor _ r).obj
              (((derivedTensor R.X S).obj (stratumModuleDual R.X S L)).obj
                ((DerivedCategory.singleFunctor _ 0).obj F))).X
  have hP : P (Mon.mk (integralCoefficientRing l E)) := by
    intro _ M hM G hG
    refine ⟨dual_data (integralCoefficientRing l E) S M
      (integral_constantModel_localResolution l E S M hM), ?_⟩
    intro r
    have h := tensor_cohomology_classical_torsion l (Fact.out : l.Prime)
      (integralCoefficientRing l E) S
      (stratumModuleDual (integralCoefficientRing l E) S M)
      (fun N hN n hn hk q ↦
        (integral_finite_level_dual_classical l E S M hM N hN n hn hk q).1)
      G hG.1 ((isEllPowerTorsion_iff_local l (Fact.out : l.Prime) _).mpr hG.2) r
    exact ⟨h.1, (isEllPowerTorsion_iff_local l (Fact.out : l.Prime) _).mp h.2⟩
  rw [integral_bundle_eq l E] at hP
  exact hP L hL F hF

end CategoryTheory
