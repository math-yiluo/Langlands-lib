import Langlands.Representation.Geometric.ParabolicOrbitStagesCoefficient
import Langlands.AllField.Representation.Geometric.ParabolicOrbitCoefficientComparison
/-! Actual nested coefficient quotients for the parabolic orbit stages. -/

noncomputable section

namespace Langlands.AllField.Geometric
open Langlands.Geometric hiding GeometricLemmaTheorem PadicGeometricLemmaTheorem PadicStandardIntersectionsTheorem geometricPieceFunctor jacquetInductionFunctor padicStandardIntersectionsTheorem
open Langlands.AllField.Geometric

open Langlands.GeneralLinear
open Langlands.Induction hiding SmoothRep

universe uF uV uW



end Langlands.AllField.Geometric

namespace Langlands.LocalFieldData
open Langlands.LocalFieldData

open Langlands.GeneralLinear hiding SupercuspidalClass
open Langlands.Geometric hiding GeometricLemmaTheorem PadicGeometricLemmaTheorem PadicStandardIntersectionsTheorem geometricPieceFunctor jacquetInductionFunctor padicStandardIntersectionsTheorem
open Langlands.AllField.Geometric
open Langlands.Induction hiding SmoothRep

universe uF uV uW

variable {F : Type uF} [Field F]
  (T : LocalFieldData F) {n : ℕ} (B C : BlockShape n)
  (w : Equiv.Perm (Fin n)) (S : BlockRefinement B)
  (hS : IsIntersectionRefinement (F := F) B C w S)
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]

/-- The actual nested positive-half coefficient quotient is the refined Jacquet carrier. -/
def parabolicOrbitNestedRefinedCoefficientEquiv
    (ρ : Representation ℂ (B.Levi F) V) :
    Representation.Coinvariants
        (parabolicOrbitNestedCoefficient F B C w (T.leviHalfModulus B) ρ) ≃ₗ[ℂ]
      RefinedJacquetModule B S ρ :=
  (splitStagesCoefficientEquiv (C.leviProjection F) (C.leviInParabolic F)
    (C.leviProjection_section F) (parabolicOrbitStages F B C w)
    (parabolicOrbitStabilizer F B C w) (parabolicOrbitStages_kernel_le F B C w)
    (parabolicOrbitStabilizer_le_stages F B C w)
    (parabolicOrbitCoefficient F B C w (T.leviHalfModulus B) ρ)).trans
      (T.parabolicOrbitRefinedCoefficientEquiv B C w S hS ρ)

@[simp] theorem parabolicOrbitNestedRefinedCoefficientEquiv_mk
    (ρ : Representation ℂ (B.Levi F) V) (v : V) :
    T.parabolicOrbitNestedRefinedCoefficientEquiv B C w S hS ρ
        (Representation.Coinvariants.mk
          (parabolicOrbitNestedCoefficient F B C w (T.leviHalfModulus B) ρ) v) =
      refinedJacquetMk B S ρ v :=
  T.parabolicOrbitRefinedCoefficientEquiv_mk B C w S hS ρ v

/-- The nested refined quotient comparison commutes with every normalized Jacquet map. -/
theorem parabolicOrbitNestedRefinedCoefficientEquiv_natural
    {ρ : Representation ℂ (B.Levi F) V}
    {τ : Representation ℂ (B.Levi F) W}
    (f : ρ.IntertwiningMap τ)
    (z : Representation.Coinvariants
      (parabolicOrbitNestedCoefficient F B C w (T.leviHalfModulus B) ρ)) :
    T.parabolicOrbitNestedRefinedCoefficientEquiv B C w S hS τ
        (Representation.Coinvariants.map _ _
          (parabolicOrbitNestedCoefficientMap F B C w (T.leviHalfModulus B) f) z) =
      T.normalizedRefinedJacquetMap B S f
        (T.parabolicOrbitNestedRefinedCoefficientEquiv B C w S hS ρ z) := by
  induction z using Representation.Coinvariants.induction_on with
  | h v =>
    change T.parabolicOrbitNestedRefinedCoefficientEquiv B C w S hS τ
      (Representation.Coinvariants.mk _ (f v)) = _
    rw [parabolicOrbitNestedRefinedCoefficientEquiv_mk,
      parabolicOrbitNestedRefinedCoefficientEquiv_mk]
    rfl

end Langlands.LocalFieldData
