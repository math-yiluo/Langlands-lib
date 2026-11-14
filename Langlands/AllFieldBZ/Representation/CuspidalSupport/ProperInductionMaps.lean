import Langlands.AllFieldBZ.Representation.Geometric.RefinementFunctors
import Langlands.Representation.CuspidalSupport.ProperInductionMaps

/-!
# All-field port of `Langlands.Representation.CuspidalSupport.ProperInductionMaps`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.CuspidalSupport.ProperInductionMaps` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
noncomputable section
open CategoryTheory
namespace Langlands.AllFieldBZ.Induction
open Langlands.Induction
universe uG uV uW

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {V : Type uV} {W : Type uW} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W]

end Langlands.AllFieldBZ.Induction
namespace Langlands.AllFieldBZ.CuspidalSupport
open Langlands.CuspidalSupport hiding induced_quasicuspidal_subrepresentation_subsingleton
open Langlands.GeneralLinear
open Langlands.Geometric
universe uF uV uW

variable {F : Type uF} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
  {n : ℕ} (B : BlockShape n) (S : BlockRefinement B)

end Langlands.AllFieldBZ.CuspidalSupport
namespace Langlands.AllFieldBZ.CuspidalSupport
open Langlands.CuspidalSupport hiding induced_quasicuspidal_subrepresentation_subsingleton
open Langlands.GeneralLinear
open Langlands.Geometric
universe uF uV

variable {F : LocalFieldPackage.{uF}}
  (T : F.TopologicalData) {n : ℕ} (B : BlockShape n)

/-- The quasicuspidal subrepresentation of an actual proper normalized
refined induction is zero, without any admissibility restriction. -/
theorem induced_quasicuspidal_subrepresentation_subsingleton :
    letI := T.topology
    ∀ (S : BlockRefinement B), refinedParabolic F.Carrier B S ≠ ⊤ →
    ∀ (A : SmoothRep.{0, uF, uV} ℂ (refinedLevi F.Carrier B S))
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

end Langlands.AllFieldBZ.CuspidalSupport
