import Langlands.Representation.CuspidalSupport.ProperInductionMaps
import Langlands.AllField.Representation.Geometric.RefinementFunctorsSupplement
noncomputable section

open CategoryTheory

namespace Langlands.AllField.Induction
open Langlands.Induction
open Langlands.AllField.Induction

universe uG uV uW


end Langlands.AllField.Induction

namespace Langlands.AllField.CuspidalSupport
open Langlands.CuspidalSupport hiding induced_quasicuspidal_subrepresentation_subsingleton
open Langlands.AllField.CuspidalSupport

open Langlands.GeneralLinear
open Langlands.Geometric

universe uF uV uW


end Langlands.AllField.CuspidalSupport

namespace Langlands.AllField.CuspidalSupport
open Langlands.CuspidalSupport hiding induced_quasicuspidal_subrepresentation_subsingleton
open Langlands.AllField.CuspidalSupport

open Langlands.GeneralLinear
open Langlands.Geometric

universe uF uV

variable {F : Type uF} [Field F]
  (T : LocalFieldData F) {n : ℕ} (B : BlockShape n)

/-- The quasicuspidal subrepresentation of an actual proper normalized
refined induction is zero, without any admissibility restriction. -/
theorem induced_quasicuspidal_subrepresentation_subsingleton :
    letI := T.topology
    ∀ (S : BlockRefinement B), refinedParabolic F B S ≠ ⊤ →
    ∀ (A : SmoothRep.{0, uF, uV} ℂ (refinedLevi F B S))
      (U : Subrepresentation ((T.normalizedRefinedInductionFunctor B S).obj A).representation),
      IsLeviQuasicuspidal B (SmoothRep.subrepresentation _ U).representation →
      Subsingleton (SmoothRep.subrepresentation _ U) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  intro S hS A U hU
  let I := (T.normalizedRefinedInductionFunctor B S).obj A
  let f := SmoothRep.hom (SmoothRep.subtype I U)
  have hf : f = 0 := refinedInduced_intertwiner_eq_zero B S hS
    (SmoothRep.subrepresentation I U).representation A.representation
    (T.refinedLeviHalfModulus B S) hU f
  refine ⟨fun x y => SmoothRep.subtype_injective I U ?_⟩
  change f x = f y
  rw [hf]
  rfl

end Langlands.AllField.CuspidalSupport
