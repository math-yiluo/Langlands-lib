/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Integral.Strict.IntegralStrictAugmentation
public import WeilConjectures.CategoryTheory.DerivedCategory.Complete.Reduction

import WeilConjectures.AlgebraicGeometry.Integral.IntegralOrdinaryAugmentationMilnor
import WeilConjectures.CategoryTheory.DerivedCategory.SixFunctors.PrincipalMilnorAugmentationReduction

/-! # Reduction of the ordinary strict quotient augmentation

## References

* Stacks Project, Tag 099M, the principal Koszul proof of derived completion
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
  CategoryTheory.MonoidalCategory Opposite
namespace AlgebraicGeometry.ProEtale

private theorem integral_prime_regular (ℓ : ℕ) [Fact ℓ.Prime] :
    (ℓ : ULift.{u + 1} ℤ) ∈ nonZeroDivisors (ULift.{u + 1} ℤ) := by
  rw [mem_nonZeroDivisors_iff]
  have hleft : ∀ x : ULift.{u + 1} ℤ, (ℓ : ULift.{u + 1} ℤ) * x = 0 → x = 0 := by
    intro x hx
    apply ULift.ext
    have h : (ℓ : ℤ) * x.down = 0 := congrArg ULift.down hx
    exact (mul_eq_zero.mp h).resolve_left
      (by exact_mod_cast (Fact.out : ℓ.Prime).ne_zero)
  exact ⟨hleft, fun x hx ↦ hleft x ((mul_comm _ _).trans hx)⟩

/-- On a complex with injective positive prime-power multiplications, the ordinary
strict quotient augmentation is invertible after derived reduction modulo the prime.
There is no left-derived reduction functor in this statement, and no natural
transformation on the derived category has to be constructed. -/
theorem integral_ordinary_augmentation_reduction (ℓ : ℕ) [Fact ℓ.Prime] (W : Scheme.{u})
    [HasDerivedCategory.{u + 1} (DiagonalAb W)]
    [HasDerivedCategory.{u + 1} (ℕᵒᵖ ⥤ DiagonalAb W)]
    (O : DiagonalReductionPresentation ℓ (𝟭 (DiagonalAb W)))
    (RZ : DerivedCategory (ℕᵒᵖ ⥤ DiagonalAb W) ⥤ DerivedCategory (DiagonalAb W))
    (ηZ : (lim : (ℕᵒᵖ ⥤ DiagonalAb W) ⥤ DiagonalAb W).mapHomologicalComplex (.up ℤ) ⋙
      DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ RZ)
    (hRZ : RZ.IsRightDerivedFunctor ηZ
      (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ DiagonalAb W) (.up ℤ)))
    (e : DiagonalAb W ≌
      Sheaf (Scheme.ProEt.topology W) (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)))
    [e.functor.Additive] [e.inverse.Additive]
    (P : CochainComplex (DiagonalAb W) ℤ)
    (hP : ∀ (n : ℕ) (i : ℤ), Mono (ℓ ^ (n + 1) • 𝟙 (P.X i))) :
    IsIso ((DerivedCategory.reductionModIdeal (Scheme.ProEt.topology W)
      (Ideal.span {(ℓ : ULift.{u + 1} ℤ)})).map
        (e.mapDerivedCategory.functor.map
          (integralStrictOrdinaryAugmentation ℓ RZ ηZ O P))) := by
  obtain ⟨PK, hPK, PG, hPG, δK, cY, δY, hTK, hTY, hu₁, hu₃⟩ :=
    integral_ordinary_augmentation_milnor ℓ W O RZ ηZ hRZ e P hP
  exact DerivedCategory.isIso_reductionModIdeal_of_principalMilnorMorphism
    (Scheme.ProEt.topology W) (integral_prime_regular ℓ)
    rfl _ _ _ PK hPK PG hPG δK cY δY hTK hTY hu₁ hu₃

end AlgebraicGeometry.ProEtale
