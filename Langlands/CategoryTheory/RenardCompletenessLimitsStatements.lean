import Langlands.CategoryTheory.RenardGrothendieckAxioms

/-!
# Renard A.VI.2(10): complete abelian categories have limits

Statements of Renard (9 July 2026), Appendix A.VI.2(10), printed page 263 /
PDF page 269: if the abelian category is complete (resp. cocomplete), then
every diagram in it has a limit (resp. colimit).

Completeness is the source convention `IsSourceComplete.{w} C`, existence of
all `w`-indexed products, and cocompleteness is `IsSourceCocomplete.{w} C`.
Diagrams are Mathlib functors `J ⥤ C` with `J : Type w` and `Category.{w} J`,
so the conclusions are Mathlib's `HasLimitsOfSize.{w, w} C` and
`HasColimitsOfSize.{w, w} C`. The family size `w`, the Hom universe `v` and the
object universe `u` are independent. These are statements only.
-/

universe w v u

open CategoryTheory Limits

namespace Langlands.Renard

variable (C : Type u) [Category.{v} C] [Abelian C]

/-- Renard A.VI.2(10), limits: if the abelian category `C` is complete at size
`w` (every `w`-indexed family has a product), then every diagram `J ⥤ C` with
`J : Type w` and `Category.{w} J` has a limit. -/
@[pp_with_univ]
def SourceCompleteHasLimitsStatement : Prop :=
  IsSourceComplete.{w} C → HasLimitsOfSize.{w, w} C

/-- Renard A.VI.2(10), colimits: if the abelian category `C` is cocomplete at
size `w` (every `w`-indexed family has a coproduct), then every diagram
`J ⥤ C` with `J : Type w` and `Category.{w} J` has a colimit. -/
@[pp_with_univ]
def SourceCocompleteHasColimitsStatement : Prop :=
  IsSourceCocomplete.{w} C → HasColimitsOfSize.{w, w} C

/-- Renard A.VI.2(10): both the limit and the colimit implications, at the same
size `w`. -/
@[pp_with_univ]
def SourceCompletenessLimitsStatement : Prop :=
  SourceCompleteHasLimitsStatement.{w} C ∧ SourceCocompleteHasColimitsStatement.{w} C

end Langlands.Renard
