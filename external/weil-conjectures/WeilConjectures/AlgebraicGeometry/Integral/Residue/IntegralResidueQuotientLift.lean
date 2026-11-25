/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Integral.IntegralCompletedCoefficientTransportSupplement
public import WeilConjectures.AlgebraicGeometry.ProperBaseChange.WitnessCompatibility
public import Mathlib.Algebra.Category.ModuleCat.Ulift

/-! # The normalized finite quotient lift

## References

* Bhatt--Scholze, Section 6.5, coefficient conventions
* Bhatt--Scholze, Section 6.5
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry.ProEtale
namespace AlgebraicGeometry.Scheme

/-- The finite quotient ring equivalence induced by the recorded uniformizer. -/
def integralResidueQuotientEquiv
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E]
    (d : AdicCoefficientDatum (Padic.coefficientExtensionIntegers l E))
    (hd : d.ideal = Ideal.span {Padic.coefficientExtensionUniformizer l E}) (n : ℕ) :
    PbcQuotient (pbcIntegralDatum l E) n ≃+*
      (Padic.coefficientExtensionIntegers l E ⧸ d.ideal ^ (n + 1)) :=
  (integralCoefficientULift l E n).trans
    (ULift.ringEquiv.trans (Ideal.quotEquivOfEq (by
      rw [hd]; rfl)))

/-- On residue representatives the normalized equivalence is exactly ULift.down. -/
theorem integralResidueQuotientEquiv_mk
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E]
    (d : AdicCoefficientDatum (Padic.coefficientExtensionIntegers l E))
    (hd : d.ideal = Ideal.span {Padic.coefficientExtensionUniformizer l E}) (n : ℕ)
    (x : PbcIntegralRing l E) :
    integralResidueQuotientEquiv l E d hd n (Ideal.Quotient.mk _ x) =
      Ideal.Quotient.mk (d.ideal ^ (n + 1)) x.down := by
  have hq : integralCoefficientULift l E n (Ideal.Quotient.mk _ x) =
      ULift.up (Ideal.Quotient.mk _ x.down) :=
    (integralCoefficientULift_exists l E n).exists.choose_spec x
  change (Ideal.quotEquivOfEq (show
    Padic.coefficientExtensionIdeal l E (n + 1) = d.ideal ^ (n + 1) from by
      rw [hd]; rfl)) ((integralCoefficientULift l E n (Ideal.Quotient.mk _ x)).down) = _
  rw [hq]
  rfl

/-- Lift a small quotient module and transport its scalars to the large quotient. -/
abbrev integralResidueQuotientLift
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E]
    (d : AdicCoefficientDatum (Padic.coefficientExtensionIntegers l E))
    (hd : d.ideal = Ideal.span {Padic.coefficientExtensionUniformizer l E}) (n : ℕ) :
    ModuleCat.{u} (Padic.coefficientExtensionIntegers l E ⧸ d.ideal ^ (n + 1)) ⥤
      ModuleCat.{u + 1} (PbcQuotient (pbcIntegralDatum l E) n) :=
  ModuleCat.uliftFunctor.{u + 1, u} _ ⋙
    ModuleCat.restrictScalars (integralResidueQuotientEquiv l E d hd n).toRingHom

end AlgebraicGeometry.Scheme
