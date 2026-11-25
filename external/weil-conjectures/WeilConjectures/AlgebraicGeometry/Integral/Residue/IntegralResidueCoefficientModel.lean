/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientsSupplement
public import WeilConjectures.AlgebraicGeometry.Completed.Adic.CompletedAdicCoefficientDatumSupplement
public import WeilConjectures.AlgebraicGeometry.Adic.AdicCoefficientDatumSupplement
import all WeilConjectures.SixFunctors.Open.OpenQuotientKoszulCompleteness

/-! # Normalized DVR coefficient comparison without open-completeness data

## References

* Bhatt--Scholze, Definition 6.5.1 and Lemma 6.5.8(1)
* Bhatt--Scholze, Definition 6.5.1, Lemma 6.5.8(1)
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.ProEtale WeilConjectures
namespace AlgebraicGeometry.Scheme

/-- Only the finite coefficient comparisons and their completed limit are retained.
No quotient-completeness criterion or open-operation model is part of this structure. -/
structure IntegralResidueCoefficientModel
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (d : AdicCoefficientDatum (Padic.coefficientExtensionIntegers l E))
    (T : Scheme.{u}) where
  /-- At each level the constant sheaf is identified with continuous component functions. -/
  finite : ∀ n : ℕ, integralCoefficientSheaf.{u, u} l E T n ≅ completedAdicFiniteRing T d n
  /-- The comparison sends each local constant scalar to that same constant function. -/
  finite_constants : ∀ (n : ℕ) (V : T.ProEtᵒᵖ)
      (a : Padic.coefficientExtensionIntegers l E),
    (finite n).hom.hom.app V ((adicLisseConstantUnit T
      (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))).app V
      (ULift.up (Ideal.Quotient.mk
        (Padic.coefficientExtensionIdeal l E (n + 1)) a))) =
        (ProEtale.finiteCoefficientScalarMap T (completedAdicQuotient d n)).app V
          (ULift.up (Ideal.Quotient.mk (d.ideal ^ (n + 1)) a))
  /-- All quotient maps are respected, before taking the limit. -/
  finite_transition : ∀ n : ℕ,
    integralCoefficientSheafTransition.{u, u} l E T n ≫ (finite n).hom =
      (finite (n + 1)).hom ≫ completedAdicFiniteStep T d n
  /-- The completed comparison is an isomorphism of commutative ring sheaves. -/
  completed : completedAdicCommRing T d ≅ completedIntegralCommRingSheafUnrestricted.{u, u} l E T
  /-- It is precisely the comparison induced by the entire finite quotient diagram. -/
  completed_projection : ∀ n : ℕ,
    (sheafCompose (ProEt.topology T) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
      completed.hom ≫
        limit.π (integralCoefficientSheafSystem.{u, u} l E T) (op n) ≫ (finite n).hom =
      completedAdicProjection T d n

/-- Existence of the coefficient comparison uses only finite constants and limits. -/
theorem integralResidueCoefficientModel_exists
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (d : AdicCoefficientDatum (Padic.coefficientExtensionIntegers l E))
    (hd : d.ideal = Ideal.span {Padic.coefficientExtensionUniformizer l E})
    (T : Scheme.{u}) : Nonempty (IntegralResidueCoefficientModel l E d T) := by
  obtain ⟨c⟩ := WeilConjectures.dvrCoefficientModel_exists l E d hd T
  exact ⟨{ finite := c.finite
           finite_constants := c.finite_constants
           finite_transition := c.finite_transition
           completed := c.completed
           completed_projection := c.completed_projection }⟩

end AlgebraicGeometry.Scheme
