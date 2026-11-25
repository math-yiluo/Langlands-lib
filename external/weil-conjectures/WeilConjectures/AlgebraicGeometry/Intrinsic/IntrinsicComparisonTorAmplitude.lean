/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.Finite.Coefficient.FiniteCoefficientFlatModel
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleTorAmplitude
public import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModuleIntrinsicComparison
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicComparisonConstructibility
import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicRealizationFlat
import WeilConjectures.SixFunctors.ProEtale.Comparison.Flat
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
/-! The Tor-amplitude component of finite-coefficient comparison.

## Implementation details

Choose the bounded étale flat model, apply exact comparison termwise,
use preservation of flatness, and compare the resulting K-flat tensor complexes.
The support interval is unchanged, giving the displayed pro-étale predicate. -/
@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry
namespace AlgebraicGeometry
/-- Exact comparison preserves the specified Tor interval. -/
theorem intrinsicComparison_torAmplitude
    (D : WeilConjectures.FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (_hlp : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (n : ℕ) (hn : 1 ≤ n) (T : Scheme.{u})
    [∀ x : T, Invertible (l : T.residueField x)] (a b : ℤ) (_hab : a ≤ b)
    (K' : Etale.DerivedCategoryModule
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)) T)
    (_hK' : @Etale.DerivedCategory.isBoundedConstructible.{u}
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)) inferInstance
      ((Equiv.ulift : ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n) ≃
        Padic.coefficientExtensionRing l E n).finite_iff.mpr
          (Padic.finite_coefficientExtensionRing l E n hn)) T K')
    (_hTor' : Etale.DerivedCategory.hasTorAmplitudeIn
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)) T a b K') :
    Scheme.HasProEtaleTorAmplitude T (Padic.coefficientExtensionRing l E n)
      ((@ProEtale.finiteCoefficientIntrinsicDerivedComparison.{u} T
        (Padic.coefficientExtensionRing l E n) inferInstance
        (Padic.finite_coefficientExtensionRing l E n hn)).obj K') a b := by
  let B := Padic.coefficientExtensionRing l E n
  have : Finite B := Padic.finite_coefficientExtensionRing l E n hn
  have : Finite (ULift.{u + 1, u} B) := Finite.of_equiv B Equiv.ulift.symm
  let F := ProEtale.finiteCoefficientIntrinsicComparison T B
  have hc := intrinsicComparison_boundedConstructible D l _hlp E n hn T K' _hK'
  apply (Scheme.finiteCoefficient_torAmplitude_iff_flatModel
    D l _hlp E n hn T _ hc a b _hab).mpr
  obtain ⟨P, hP, ⟨eP⟩⟩ :=
    (Etale.finiteCoefficient_hasTorAmplitude_iff_flatModel
      D l _hlp E n hn T K' _hK' a b _hab).mp _hTor'
  refine ⟨(F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P, ?_, ?_, ?_⟩
  · intro q
    exact ProEtale.intrinsicRealization_flat T B _
      (ProEtale.flat_comparisonUpperStar_obj (hP.2 q))
  · intro q hq
    exact F.map_isZero (hP.1 q hq)
  · exact ⟨F.mapDerivedCategory.mapIso eP ≪≫ F.mapDerivedCategoryFactors.app P⟩
end AlgebraicGeometry
