import Langlands.CategoryTheory.RenardCompletenessLimitsStatements
import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers

/-!
# Renard A.VI.2(10): proof that complete abelian categories have all limits

Proof of `Langlands.Renard.SourceCompletenessLimitsStatement` from
`Langlands.CategoryTheory.RenardCompletenessLimitsStatements`, for an arbitrary abelian
category `C : Type u` with `[Category.{v} C]` and an independent size `w`.

An abelian category has equalizers and coequalizers (`Abelian.hasEqualizers`,
`Abelian.hasCoequalizers`). Together with the source hypothesis, `w`-indexed products
(resp. coproducts), Mathlib's construction of a limit as an equalizer of two maps between
products (`has_limits_of_hasEqualizers_and_products`), and dually of a colimit as a
coequalizer of two maps between coproducts (`has_colimits_of_hasCoequalizers_and_coproducts`),
gives every limit (resp. colimit) of a diagram `J ⥤ C` with `J : Type w` and
`Category.{w} J`.
-/

universe w v u

open CategoryTheory Limits

namespace Langlands.Renard

variable (C : Type u) [Category.{v} C] [Abelian C]

/-- Renard A.VI.2(10), limits: an abelian category with all `w`-indexed products has all
limits of diagrams `J ⥤ C` with `J : Type w` and `Category.{w} J`. -/
theorem sourceCompleteHasLimits : SourceCompleteHasLimitsStatement.{w} C := fun h => by
  have : HasProducts.{w} C := h
  exact has_limits_of_hasEqualizers_and_products

/-- Renard A.VI.2(10), colimits: an abelian category with all `w`-indexed coproducts has
all colimits of diagrams `J ⥤ C` with `J : Type w` and `Category.{w} J`. -/
theorem sourceCocompleteHasColimits : SourceCocompleteHasColimitsStatement.{w} C :=
  fun h => by
    have : HasCoproducts.{w} C := h
    exact has_colimits_of_hasCoequalizers_and_coproducts

/-- Renard A.VI.2(10): the combined statement. -/
theorem sourceCompletenessLimits : SourceCompletenessLimitsStatement.{w} C :=
  ⟨sourceCompleteHasLimits.{w} C, sourceCocompleteHasColimits.{w} C⟩

end Langlands.Renard
