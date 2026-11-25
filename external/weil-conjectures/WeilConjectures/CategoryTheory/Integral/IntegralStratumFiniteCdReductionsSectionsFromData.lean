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

/-! Generic heart-to-sections amplitude for the continuous integral coefficient.
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

/-- Derived sections of a Tor-amplitude `[0,1]` dual tensor a classical locally
ell-power-torsion heart object vanish outside `[0,s+1]` when `cd_ell(S) ≤ s`.
Source: blueprint latest, `part-six-operations/sec-constructibility-upper-shriek/
sec-ladic-summary/sec-i-heart/sk-prop-int-compactness/sk-lem-int-ext-bound.proof.md`,
dual-tensor and derived-sections bullets.
Proof: write the finite cohomological dimension as a natural number t≤s. Convert
local torsion of each tensor homology sheaf to the kernel-colimit formulation. Apply the
existing generic sections estimate: Tor amplitude gives tensor cohomology only in [0,1],
and the classical torsion heart estimate bounds its sections in [0,t]. Bounded-heart
amplitude therefore gives [0,t+1]. Widen this interval to [0,s+1].
(blueprint: lem-sfb-integral-stratum-finite-cd-reductions). -/
theorem integralStratumFiniteCdReductions_sections_from_data
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (S : Scheme.{u}) [IsNoetherian S]
    (D : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
      (condensedRingObj (IntegralQuotient.integral l E) S)))
    (s : ℕ) (hs : cohomologicalDimension l (Fact.out : l.Prime) S ≤ s)
    (F : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
      (condensedRingObj (IntegralQuotient.integral l E) S))
    (hD : DerivedCategory.torAmplitudeIn _ 0 1 D)
    (hcoh : ∀ r : ℤ,
      IsClassicalAbelian
        ((DerivedCategory.homologyFunctor _ r).obj
          (((derivedTensor (IntegralQuotient.integral l E) S).obj D).obj
            ((DerivedCategory.singleFunctor _ 0).obj F))).X ∧
      IsEllPowerTorsionLocal l (Fact.out : l.Prime)
        ((DerivedCategory.homologyFunctor _ r).obj
          (((derivedTensor (IntegralQuotient.integral l E) S).obj D).obj
            ((DerivedCategory.singleFunctor _ 0).obj F))).X) :
    ∀ i : ℤ, i < 0 ∨ (s : ℤ) + 1 < i →
      IsZero ((DerivedCategory.homologyFunctor Ab.{u + 1} i).obj
        ((stratumModuleDerivedSections (IntegralQuotient.integral l E) S).obj
          (((derivedTensor (IntegralQuotient.integral l E) S).obj D).obj
            ((DerivedCategory.singleFunctor _ 0).obj F)))) := by
  obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.mp
    (hs.trans_lt (WithTop.coe_lt_top s)).ne
  have hts : t ≤ s := WithTop.coe_le_coe.mp (ht ▸ hs)
  have hc : ∀ r : ℤ,
      IsClassicalAbelian
        ((DerivedCategory.homologyFunctor _ r).obj
          (((derivedTensor (IntegralQuotient.integral l E) S).obj D).obj
            ((DerivedCategory.singleFunctor _ 0).obj F))).X ∧
      IsEllPowerTorsion l (Fact.out : l.Prime)
      ((DerivedCategory.homologyFunctor _ r).obj
        (((derivedTensor (IntegralQuotient.integral l E) S).obj D).obj
          ((DerivedCategory.singleFunctor _ 0).obj F))).X := by
    intro r
    exact ⟨(hcoh r).1,
      (isEllPowerTorsion_iff_local l (Fact.out : l.Prime) _).mpr (hcoh r).2⟩
  have h := sections_bound_of_tor_and_classical_cohomology l (Fact.out : l.Prime)
    (IntegralQuotient.integral l E) S t ht D F hD hc
  intro i hi
  exact h i (by rcases hi with hi | hi <;> omega)

end CategoryTheory
