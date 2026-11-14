import Langlands.Representation.Geometric.ParabolicOrbitNestedAction
import Langlands.AllField.Representation.Geometric.ParabolicOrbitSectionComparison
import Langlands.AllField.Representation.Induction.InverseTranspose
/-! The actual nested section action and its refined coefficient comparison. -/

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
  (w : Equiv.Perm (Fin n)) (S : BlockRefinement B) (R : BlockRefinement C)
  (hS : IsIntersectionRefinement (F := F) B C w S)
  (hR : IsIntersectionRefinement (F := F) C B w⁻¹ R)
  {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- The action on the actual nested quotient is projected normalized refined
Jacquet with the two explicit positive source half moduli. -/
def parabolicOrbitNestedRefinedCoefficientActionEquiv
    (ρ : Representation ℂ (B.Levi F) V) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    (parabolicOrbitNestedCoefficientAction F B C w (T.leviHalfModulus B) ρ).Equiv
      (twist (T.parabolicOrbitSectionCharacter B C w S R hS hR)
        ((T.normalizedRefinedJacquet B S ρ).comp
          (parabolicOrbitSourceRefinedCoordinate F B C w R hR S hS))) := by
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  exact (parabolicOrbitNestedFullCoefficientActionEquiv F B C w
    (T.leviHalfModulus B) ρ).trans
      (T.parabolicOrbitFullRefinedCoefficientActionEquiv B C w S R hS hR ρ)

/-- The normalized action equivalence is natural for all original coefficient maps. -/
theorem parabolicOrbitNestedRefinedCoefficientActionEquiv_natural
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ (B.Levi F) V}
    {τ : Representation ℂ (B.Levi F) W}
    (f : ρ.IntertwiningMap τ) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    ∀ z : Representation.Coinvariants
      (parabolicOrbitNestedCoefficient F B C w (T.leviHalfModulus B) ρ),
    T.parabolicOrbitNestedRefinedCoefficientActionEquiv B C w S R hS hR τ
        (Representation.Coinvariants.map _ _
          (parabolicOrbitNestedCoefficientMap F B C w (T.leviHalfModulus B) f) z) =
      T.normalizedRefinedJacquetMap B S f
        (T.parabolicOrbitNestedRefinedCoefficientActionEquiv B C w S R hS hR ρ z) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  exact T.parabolicOrbitNestedRefinedCoefficientEquiv_natural B C w S hS f

end Langlands.LocalFieldData
