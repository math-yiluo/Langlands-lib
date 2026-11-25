/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Bounded.BoundedConstructibleCompleteSupplement
public import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructible
public import WeilConjectures.AlgebraicGeometry.IntegralCompletedCoefficientTransport

/-! # Canonical completed integral coefficient transport

The projection-normalized coefficient constructions are independent of the
stratified-perfect theorem and its geometric hypotheses.

## References

* Bhatt--Scholze, Section 6.5
* Bhatt--Scholze, Definition 6.5.1
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

/-- Transport the detailed category along the canonical coefficient isomorphism.
The valuation ring is lifted to the small site's coefficient universe u+1. The
finite extension E itself retains the recorded coefficient convention E: Type u. -/
def integralDetailedTransport
    (T : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :
    DerivedCategory (WeilConjectures.scalarReductionSource.{u, u} l E T) ⥤
      DerivedCategory (pbcModules T
        (pbcAdicCompletion T (pbcIntegralDatum l E))) :=
  letI := HasDerivedCategory.standard
    (WeilConjectures.scalarReductionSource.{u, u} l E T)
  letI := (integralDetailedCoefficientRestriction_exact T l E).1
  letI := (integralDetailedCoefficientRestriction_exact T l E).2
  (SheafOfModules.restrictScalars.{u + 1}
    (integralDetailedCoefficientComparison T l E).hom).mapDerivedCategory

end AlgebraicGeometry.Scheme
