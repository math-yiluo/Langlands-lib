import Langlands.Algebra.NonUnitalModuleDualFunctor
import Langlands.Algebra.RenardRightHomFunctors
import Langlands.Algebra.NondegenerateTensorFunctor

/-!
# Duality intertwines forgetful and pseudo-forgetful functors (Renard I.4.2, Theorem)

For complex algebras with idempotents `A`, `B` and a nondegenerate `A`-bimodule structure on
`B` commuting with the regular `B`-actions, `ˇF_AB(Ñ) ≅ F_AB(N)~` naturally in `N ∈ M(B)` and
`I_AB(M̃) ≅ P_AB(M)~` naturally in `M ∈ M(A)`. The `A`-actions on `B` are assumed compatible
with the complex scalars of `A` and `B`.
-/

set_option autoImplicit false

open CategoryTheory

namespace Langlands.Algebra

universe uA uB v

/-- Renard I.4.2, Theorem, first identity: `ˇF_AB(Ñ) ≅ F_AB(N)~`, naturally in the
nondegenerate left `B`-module `N`. Here `A` and `B` are complex algebras with idempotents, `B`
carries a nondegenerate left `A`-action commuting with right multiplication of `B` and
compatible with the complex scalars (`(c a) · b = c (a · b)`). `F_AB(N) = B ⊗_B N` is the
forgetful functor, `ˇF_AB` the right-module pseudo-forgetful functor `Hom_{B°}(B, •)_A`, and
`~` the nondegenerate dual. -/
def DualityForgetfulStatement : Prop :=
  ∀ (A : Type uA) (B : Type uB) [NonUnitalRing A] [Module ℂ A] [IsScalarTower ℂ A A]
    [SMulCommClass ℂ A A] [NonUnitalRing B] [Module ℂ B] [IsScalarTower ℂ B B]
    [SMulCommClass ℂ B B] [NonUnitalModule A B] [IsScalarTower ℂ A B]
    (hA : IsIdempotented A) (hB : IsIdempotented B) (hLeft : IsNondegenerate A B),
    letI : NonUnitalModule Bᵐᵒᵖ B := NonUnitalModule.rightRegular B
    ∀ hAB : ActionsCommute A B B,
      Nonempty
        (NonUnitalModuleDual.leftToRightFunctor.{uB, v} hB ⋙
            RenardRightHomFunctors.rightPseudoF.{uA, uB, v} hAB hA ≅
          (NondegenerateTensorFunctor.regularF.{uA, uB, v} hA hB hAB hLeft).op ⋙
            NonUnitalModuleDual.leftToRightFunctor.{uA, max uB v} hA)

/-- Renard I.4.2, Theorem, second identity: `I_AB(M̃) ≅ P_AB(M)~`, naturally in the
nondegenerate left `A`-module `M`. Here `B` carries a nondegenerate right `A`-action commuting
with left multiplication of `B` and compatible with the complex scalars
(`b · (c a) = c (b · a)`). `P_AB(M) = B ⊗_A M`, `I_AB` is the right-module induction
`Hom_{A°}(B, •)_B`, and `~` is the nondegenerate dual. -/
def DualityInductionStatement : Prop :=
  ∀ (A : Type uA) (B : Type uB) [NonUnitalRing A] [Module ℂ A] [IsScalarTower ℂ A A]
    [SMulCommClass ℂ A A] [NonUnitalRing B] [Module ℂ B] [IsScalarTower ℂ B B]
    [SMulCommClass ℂ B B] [NonUnitalModule Aᵐᵒᵖ B] [IsScalarTower ℂ Aᵐᵒᵖ B]
    (hA : IsIdempotented A) (hB : IsIdempotented B) (hRight : IsRightNondegenerate A B),
    letI : NonUnitalModule B B := NonUnitalModule.regular B
    ∀ hBA : ActionsCommute B A B,
      Nonempty
        (NonUnitalModuleDual.leftToRightFunctor.{uA, v} hA ⋙
            RenardRightHomFunctors.rightI.{uA, uB, v} hBA hB ≅
          (NondegenerateTensorFunctor.regularP.{uA, uB, v} hB hBA hRight).op ⋙
            NonUnitalModuleDual.leftToRightFunctor.{uB, max uB v} hB)

end Langlands.Algebra
