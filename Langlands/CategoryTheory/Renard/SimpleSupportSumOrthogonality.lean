import Langlands.CategoryTheory.Renard.SimpleSupportSumOrthogonalityStatements
import Langlands.CategoryTheory.Renard.SimpleSupportSumProof
import Langlands.CategoryTheory.Renard.SimpleSupportOrthogonality

/-!
# Renard A.IX: disjointness of the actual full supported sums

Apply the published full-sum support theorem separately to both sums,
then specialize the published intersection and binary-inclusion results.
The source-family, Hom and object universes remain independent.
-/

universe w v u

open CategoryTheory CategoryTheory.Limits

namespace Langlands.Renard

noncomputable section

/-- Renard A.IX, printed page 268 / PDF274: actual full sums with
disjoint simple supports have zero intersection, and their canonical
binary-biproduct inclusion in the ambient object is monic. -/
theorem simpleSupportSumOrthogonality
    (C : Type u) [Category.{v} C] [Abelian C] :
    SimpleSupportSumOrthogonalityStatement.{w} C := by
  intro hG
  let : HasCoproducts.{w} C := hG.1
  intro hAB6 S T hS hT hST X _ _
  let : HasCoproductsOfShape (simpleSupportSubobjects S X) C :=
    hasCoproductsOfShape_of_small.{w} C (simpleSupportSubobjects S X)
  let : HasCoproductsOfShape (simpleSupportSubobjects T X) C :=
    hasCoproductsOfShape_of_small.{w} C (simpleSupportSubobjects T X)
  have hES := (simpleSupportSumSupport C : SimpleSupportSumSupportStatement.{w} C)
    hG hAB6 S hS X
  have hET := (simpleSupportSumSupport C : SimpleSupportSumSupportStatement.{w} C)
    hG hAB6 T hT X
  have h := inf_eq_bot_of_hasSimpleSupport_of_disjoint hG hAB6 hST hES hET
  exact ⟨h, mono_biprod_desc_arrow_of_inf_eq_bot h⟩

end

end Langlands.Renard
