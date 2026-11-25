/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModuleIntrinsicComparison
public import WeilConjectures.AlgebraicGeometry.SmoothPurity.CompactifiableOverField
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.SixFunctors.ProEtale.Comparison.Defs
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriek
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # The finite constructible exceptional inverse image

Source: blueprint sec-smooth-purity/sk-def-sf-operations,
theorem-f-shriek-finite-coefficients, order 1489
(blueprint: theorem-f-shriek-finite-coefficients).

The finite-level operation is the published ordinary etale right adjoint transported
by the canonical comparison. The intrinsic constant-ring realization changes only the
presentation of module sheaves. No ambient pro-etale adjunction is assumed.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- The finite exceptional inverse image on intrinsic constant-ring modules:
`nu_X^* f^times Rnu_Y,*`. The first functor undoes the canonical constant-ring
realization, and the last performs comparison and that realization. The ordinary
etale right adjoint is supplied by Brown representability, and compactifiability
by Nagata over the field; neither is an additional hypothesis. Restricting this
formula to bounded constructible complexes is the operation of the blueprint.
Source: blueprint order 1489, finite-level displayed definition
(blueprint: theorem-f-shriek-finite-coefficients). -/
noncomputable def finiteExceptionalInverseImage
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) (hn : 1 ≤ n)
    (k : Type u) [Field k] (X Y : Scheme.{u})
    [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] :
    proEtaleDerivedCategory Y (Padic.coefficientExtensionRing l E n) ⥤
      proEtaleDerivedCategory X (Padic.coefficientExtensionRing l E n) :=
  letI := Padic.finite_coefficientExtensionRing l E n hn
  letI := hasCompactification_of_finiteType_over_field k X Y f
  letI := (ProEtale.finiteCoefficientIntrinsicRealization_exact Y
    (Padic.coefficientExtensionRing l E n)).1
  letI : (ProEtale.finiteCoefficientIntrinsicRealization Y
    (Padic.coefficientExtensionRing l E n)).asEquivalence.functor.Additive :=
      ProEtale.finiteCoefficientIntrinsicRealization_additive Y _
  (ProEtale.finiteCoefficientIntrinsicRealization Y
      (Padic.coefficientExtensionRing l E n)).asEquivalence.inverse.mapDerivedCategory ⋙
    (ProEtale.comparisonLowerStar
      (ModuleCat.{u + 1} (ULift.{u + 1}
        (Padic.coefficientExtensionRing l E n))) Y).rightDerivedFunctor ⋙
    Etale.rightDerivedUpperShriek (ULift.{u + 1} (Padic.coefficientExtensionRing l E n)) f ⋙
    ProEtale.finiteCoefficientIntrinsicDerivedComparison X (Padic.coefficientExtensionRing l E n)

end AlgebraicGeometry.Scheme
