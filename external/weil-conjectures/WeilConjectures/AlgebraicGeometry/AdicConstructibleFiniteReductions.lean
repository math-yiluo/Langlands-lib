/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.AdicFiniteReductionData
import WeilConjectures.AlgebraicGeometry.AdicFiniteCompletionBounds
import WeilConjectures.AlgebraicGeometry.AdicFiniteEtaleOrigins
import WeilConjectures.AlgebraicGeometry.AdicFiniteEtaleTransitions
import WeilConjectures.AlgebraicGeometry.AdicFiniteReductionTor

/-! # Finite reductions with prescribed residue marking
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe u v
open CategoryTheory CategoryTheory.Limits
open CategoryTheory.ConstantCompletion
namespace AlgebraicGeometry.Scheme

attribute [local instance] HasDerivedCategory.standard

/-- Finite reductions with the given Tor interval and the prescribed residue marking.
Source: Stacks Project, proetale.tex, Tag 09C2 (1)-(4), and Tag 09AL.
(auxiliary; not a blueprint node).

Proof: The residue Tor filtration supplies all reduction bounds. Completeness
and the Milnor endpoint argument give the derived limit and bounds on N.
Choose etale origins separately at each level, then replace the zero origin
and its comparison by the prescribed C and e using a dependent case split.
The normalized full-faithful quotient transport supplies beta and its cocycle
for this family. At zero the marking equation reduces to the identity law. -/
theorem adic_constructible_finite_reductions (X : Scheme.{u}) [IsNoetherian X]
    (A : Type (max v (u + 1))) [CommRing A] [IsNoetherianRing A] (J : Ideal A)
    (N : adicFiniteAmbient.{u, v} X A) (hcomplete : adicFiniteComplete.{u, v} X A J N)
    (C : adicFiniteEtale.{u, v} X J 0)
    (hC : IsCoefficientBoundedConstructibleEtale.{u, v} X (adicFiniteCoeff J 0) C)
    (e : (adicFinitePullback.{u, v} X (adicFiniteCoeff J 0)).obj C ≅
      adicFiniteReduction.{u, v} X J N 0)
    (a b : ℤ) (hab : a ≤ b)
    (hTor : HasCoefficientModelTorAmplitude
      (constant (smallModelComparisonEtaleTopology.{u, v} X) (adicFiniteCoeff J 0)) C a b) :
    (∃ hp : HasProduct (adicFiniteUnderlying.{u, v} X J N),
      @IsDerivedLimit _ _ _ _ _ _ _ _ hp (adicFiniteTransition.{u, v} X J N) N) ∧
    (∀ q : ℤ, (q < a ∨ b < q) → IsZero ((coefficientModelCohomology
      (constant (coefficientProEtaleModelTopology.{u, v} X) A) q).obj N)) ∧
    (∀ n : ℕ, HasCoefficientProEtaleTorAmplitude.{u, v} X (adicFiniteCoeff J n)
      (adicFiniteReduction.{u, v} X J N n) a b) ∧
    ∃ (Cn : ∀ n : ℕ, adicFiniteEtale.{u, v} X J n)
      (alpha : ∀ n : ℕ, (adicFinitePullback.{u, v} X (adicFiniteCoeff J n)).obj (Cn n) ≅
        adicFiniteReduction.{u, v} X J N n)
      (beta : ∀ {m n : ℕ} (h : n ≤ m),
        (adicFiniteExtension (smallModelComparisonEtaleTopology.{u, v} X)
          (adicFiniteFactor J h)).obj (Cn m) ≅ Cn n),
      (∀ n : ℕ, IsCoefficientBoundedConstructibleEtale.{u, v} X (adicFiniteCoeff J n) (Cn n)) ∧
      (∀ n : ℕ, HasCoefficientModelTorAmplitude
        (constant (smallModelComparisonEtaleTopology.{u, v} X) (adicFiniteCoeff J n))
          (Cn n) a b) ∧
      (∃ hzero : Cn 0 = C,
        (adicFinitePullback.{u, v} X (adicFiniteCoeff J 0)).map (eqToIso hzero).hom ≫ e.hom =
          (alpha 0).hom) ∧
      (∀ (r m n : ℕ) (hnm : n ≤ m) (hmr : m ≤ r),
        (adicFiniteExtensionComp (smallModelComparisonEtaleTopology.{u, v} X)
          (adicFiniteFactor J hmr) (adicFiniteFactor J hnm)
          (adicFiniteFactor J (hnm.trans hmr)) (adicFiniteFactorComp J hnm hmr)).hom.app
            (Cn r) ≫ (beta (hnm.trans hmr)).hom =
        (adicFiniteExtension (smallModelComparisonEtaleTopology.{u, v} X)
          (adicFiniteFactor J hnm)).map (beta hmr).hom ≫ (beta hnm).hom) ∧
      (∀ (m n : ℕ) (h : n ≤ m),
        (adicFinitePullback.{u, v} X (adicFiniteCoeff J n)).map (beta h).hom ≫ (alpha n).hom =
        (adicFiniteComparison.{u, v} X (adicFiniteFactor J h)).inv.app (Cn m) ≫
          (adicFiniteExtension (coefficientProEtaleModelTopology.{u, v} X)
            (adicFiniteFactor J h)).map (alpha m).hom ≫ (adicFiniteRho.{u, v} X J N h).hom) := by
  classical
  have hred := adicFiniteReduction_tor X A J N C hC e a b hab hTor
  obtain ⟨hlim, hbound⟩ := adicFiniteCompletion_bounds X A J N hcomplete a b hred
  have horigin := adicFiniteEtale_origins X A J N C hC e a b hred
  choose K hK htK heK using horigin
  let Cn : ∀ n : ℕ, adicFiniteEtale.{u, v} X J n
    | 0 => C
    | n + 1 => K (n + 1)
  have hCn : ∀ n : ℕ,
      IsCoefficientBoundedConstructibleEtale.{u, v} X (adicFiniteCoeff J n) (Cn n) := by
    intro n
    cases n with
    | zero => exact hC
    | succ n => exact hK (n + 1)
  have htCn : ∀ n : ℕ, HasCoefficientModelTorAmplitude
      (constant (smallModelComparisonEtaleTopology.{u, v} X) (adicFiniteCoeff J n))
        (Cn n) a b := by
    intro n
    cases n with
    | zero => exact hTor
    | succ n => exact htK (n + 1)
  let alpha : ∀ n : ℕ, (adicFinitePullback.{u, v} X (adicFiniteCoeff J n)).obj (Cn n) ≅
      adicFiniteReduction.{u, v} X J N n
    | 0 => e
    | n + 1 => Classical.choice (heK (n + 1))
  obtain ⟨beta, hcocycle, hcompat⟩ :=
    adicFiniteEtale_transitions X A J N a b Cn hCn htCn alpha
  refine ⟨hlim, hbound, hred, Cn, alpha, beta, hCn, htCn, ?_, hcocycle, hcompat⟩
  exact ⟨rfl, by
    change (adicFinitePullback.{u, v} X _).map (eqToIso (rfl : C = C)).hom ≫
      e.hom = e.hom
    change (adicFinitePullback.{u, v} X _).map (𝟙 C) ≫ e.hom = e.hom
    exact (congrArg (fun k ↦ k ≫ e.hom)
      ((adicFinitePullback.{u, v} X _).map_id C)).trans (Category.id_comp e.hom)⟩

end AlgebraicGeometry.Scheme
