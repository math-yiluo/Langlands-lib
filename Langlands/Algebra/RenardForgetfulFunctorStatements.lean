import Langlands.Algebra.NondegenerateTensorFunctor
import Langlands.Algebra.RenardHomFunctors
import Langlands.Algebra.NonUnitalModuleRestrictScalars
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Ring.Opposite

/-!
# Renard I.2.3: the unital right adjoint and the closing Remark

Renard 2026, I.2.3 (printed pp.16–18 / PDF pp.22–24). For unital rings, restriction of
scalars `φ_*` along `φ : A → B` has the right adjoint `M ↦ Hom_A(B, M)`. For rings with
idempotents and `φ : A → B` making `B` a nondegenerate `A`-bimodule, `B` is idempotented,
`{φ(e)}` is a filtering system of idempotents of `B`, the nondegenerate parts of a `B`-module for `B` and for `A`
coincide, and the forgetful functor `F_{AB}` and the pseudo-forgetful functor `ˇF_{AB}` are
both naturally isomorphic to restriction along `φ`.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory MulOpposite

namespace Langlands.Algebra.RenardForgetfulFunctor

universe uA uB uM

/-- Renard I.2.3, unital case: for a unital ring homomorphism `φ : A → B`, restriction of
scalars `φ_*` is left adjoint to `M ↦ Hom_A(B, M)` (Mathlib's coextension of scalars), by
the adjunction sending `g : φ_* N → M` to `n ↦ (b ↦ g (b • n))`. -/
def UnitalCoextensionAdjunctionStatement : Prop :=
  ∀ (A : Type uA) (B : Type uB) [Ring A] [Ring B] (φ : A →+* B),
    ∃ adj : ModuleCat.restrictScalars.{max uB uM} φ ⊣ ModuleCat.coextendScalars φ,
      ∀ (N : ModuleCat.{max uB uM} B) (M : ModuleCat.{max uB uM} A)
        (g : (ModuleCat.restrictScalars.{max uB uM} φ).obj N ⟶ M) (n : N) (b : B),
        (adj.homEquiv N M g).hom n b = g.hom (b • n)

/-- Renard I.2.3, closing Remark, for the forgetful functor: with the left `A`-action
`a • b = φ a * b` and the right regular action of `B` on `B`, the two actions commute and are
nondegenerate, and `F_{AB}` is naturally isomorphic to restriction along `φ`. -/
def TensorForgetfulRemark (A : Type uA) (B : Type uB) [NonUnitalRing A] [NonUnitalRing B]
    (hA : IsIdempotented A) (φ : A →ₙ+* B)
    (hφ : NonUnitalModuleRestrictScalars.HasTwoSidedLocalUnits φ) : Prop :=
  letI : NonUnitalModule A B :=
    NonUnitalModuleRestrictScalars.module φ (NonUnitalModule.regular B)
  letI : NonUnitalModule Bᵐᵒᵖ B := NonUnitalModule.rightRegular B
  ActionsCommute A B B ∧ IsNondegenerateBimodule A B B ∧
    ∀ (hAB : ActionsCommute A B B) (hnd : IsNondegenerateBimodule A B B),
      Nonempty (NondegenerateTensorFunctor.F.{uA, uB, max uB uM} hA hAB hnd ≅
        NonUnitalModuleRestrictScalars.nondegenerateFunctor.{uA, uB, max uB uM} φ
          (NonUnitalModuleRestrictScalars.HasTwoSidedLocalUnits.hasLeftLocalUnits φ hφ))

/-- Renard I.2.3, closing Remark, for the pseudo-forgetful functor: with the left regular
action of `B` on `B` and the right `A`-action `op a • b = b * φ a`, the two actions commute
and are nondegenerate, and `ˇF_{AB}` is naturally isomorphic to restriction along `φ`. -/
def PseudoForgetfulRemark (A : Type uA) (B : Type uB) [NonUnitalRing A] [NonUnitalRing B]
    (hA : IsIdempotented A) (φ : A →ₙ+* B)
    (hφ : NonUnitalModuleRestrictScalars.HasTwoSidedLocalUnits φ) : Prop :=
  letI : NonUnitalModule Aᵐᵒᵖ B :=
    NonUnitalModuleRestrictScalars.module (NonUnitalRingHom.op φ)
      (NonUnitalModule.rightRegular B)
  letI : NonUnitalModule B B := NonUnitalModule.regular B
  ActionsCommute B A B ∧ IsNondegenerateBimodule B A B ∧
    ∀ hBA : ActionsCommute B A B,
      Nonempty (RenardHomFunctors.pseudoF.{uA, uB, max uB uM} hBA hA ≅
        NonUnitalModuleRestrictScalars.nondegenerateFunctor.{uA, uB, max uB uM} φ
          (NonUnitalModuleRestrictScalars.HasTwoSidedLocalUnits.hasLeftLocalUnits φ hφ))

/-- Renard I.2.3, closing Remark: let `A` be idempotented and `φ : A → B` a nonunital ring
homomorphism making `B` a nondegenerate `A`-bimodule. Then `B` is idempotented and the
`φ(e)`, `e` an idempotent of `A`, form a filtering system of idempotents of `B` (every finite
family of idempotents of `B` lies below some `φ(e)`); a vector of a `B`-module is fixed by
an idempotent of `B` iff it is fixed by `φ(e)` for an idempotent `e` of `A`; and the forgetful and pseudo-forgetful functors are naturally isomorphic to
restriction along `φ` (`TensorForgetfulRemark`, `PseudoForgetfulRemark`). -/
def ForgetfulFunctorRemarkStatement : Prop :=
  ∀ (A : Type uA) (B : Type uB) [NonUnitalRing A] [NonUnitalRing B]
    (hA : IsIdempotented A) (φ : A →ₙ+* B)
    (hφ : NonUnitalModuleRestrictScalars.HasTwoSidedLocalUnits φ),
    IsIdempotented B ∧
    (∀ s : Finset (Idempotent B), ∃ e : Idempotent A,
      ∀ f ∈ s, φ (e : A) * (f : B) = f ∧ (f : B) * φ (e : A) = f) ∧
    (∀ (M : Type uM) [AddCommGroup M] [NonUnitalModule B M] (m : M),
      (∃ e : Idempotent B, (e : B) • m = m) ↔ ∃ e : Idempotent A, φ (e : A) • m = m) ∧
    TensorForgetfulRemark.{uA, uB, uM} A B hA φ hφ ∧
    PseudoForgetfulRemark.{uA, uB, uM} A B hA φ hφ

/-- The unital right adjoint and the closing Remark of Renard I.2.3. -/
def RenardForgetfulFunctorStatements : Prop :=
  UnitalCoextensionAdjunctionStatement.{uA, uB, uM} ∧
    ForgetfulFunctorRemarkStatement.{uA, uB, uM}

end Langlands.Algebra.RenardForgetfulFunctor
