/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Integral.Strict.IntegralStrictAugmentation
public import WeilConjectures.CategoryTheory.Triangulated.HomotopyLimit.Tower
public import WeilConjectures.CategoryTheory.DerivedCategory.Complete.Defs

import WeilConjectures.AlgebraicGeometry.Regular.RegularQuotientPresentationTower

/-! # Regular ordinary quotients as the positive principal derived quotient tower

The comparison is natural in the tower index and preserves the specified augmentation.

## References

* Stacks Project, Tag 099M, the two-term free resolution of the principal coefficients
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
namespace AlgebraicGeometry.ProEtale

/-- Regular ordinary quotients agree with the positive tail of the principal derived
quotient tower, compatibly with the specified quotient projections. This statement
contains no inverse limit, derived-limit comparison, or Milnor triangle. -/
theorem integral_regular_quotient_tower (ℓ : ℕ) [Fact ℓ.Prime] (W : Scheme.{u})
    [HasDerivedCategory.{u + 1} (DiagonalAb W)]
    [HasDerivedCategory.{u + 1} (ℕᵒᵖ ⥤ DiagonalAb W)]
    (O : DiagonalReductionPresentation ℓ (𝟭 (DiagonalAb W)))
    (e : DiagonalAb W ≌
      Sheaf (Scheme.ProEt.topology W) (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)))
    [e.functor.Additive] [e.inverse.Additive]
    (P : CochainComplex (DiagonalAb W) ℤ)
    (hP : ∀ (n : ℕ) (i : ℤ), Mono (ℓ ^ (n + 1) • 𝟙 (P.X i))) :
    let K := e.mapDerivedCategory.functor.obj (DerivedCategory.Q.obj P)
    let X := (O.E.mapHomologicalComplex (.up ℤ)).obj P
    let G := DerivedCategory.derivedCompletionDiagram (Scheme.ProEt.topology W)
      (Ideal.span {(ℓ : ULift.{u + 1} ℤ)}) K
    ∃ α : X.asFunctor ⋙ DerivedCategory.Q ⋙ e.mapDerivedCategory.functor ≅
        addOpFunctor 1 ⋙ G,
      ∀ n : ℕ,
        e.mapDerivedCategory.functor.map
            (DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex (O.π n) (.up ℤ)).app P)) ≫
          α.hom.app (op n) =
        (DerivedCategory.derivedCompletionCone (Scheme.ProEt.topology W)
          (Ideal.span {(ℓ : ULift.{u + 1} ℤ)}) K).π.app (op (n + 1)) := by
  have hr : (ℓ : ULift.{u + 1} ℤ) ∈ nonZeroDivisors (ULift.{u + 1} ℤ) := by
    apply mem_nonZeroDivisors_of_injective
      (f := (ULift.ringEquiv : ULift.{u + 1} ℤ ≃+* ℤ)) ULift.ringEquiv.injective
    apply mem_nonZeroDivisors_of_ne_zero
    change (ℓ : ℤ) ≠ 0
    exact_mod_cast (Fact.out : ℓ.Prime).ne_zero
  exact regular_quotient_presentation_tower ℓ hr (Scheme.ProEt.topology W) O e P hP

end AlgebraicGeometry.ProEtale
