import Langlands.GroupScheme.Absolute.SolvableTorusCentralizerProductStatement
import Langlands.GroupScheme.Absolute.SolvableMaximalTorusSemidirectProof
import Langlands.GroupScheme.Rational.MaximalSplitTorusCentralizer
import Langlands.GroupScheme.Rational.MaximalTorusFiniteType

/-! # The unipotent subgroup times a torus centralizer (Milne 16.41) -/

universe u

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- A smooth connected affine solvable group over an algebraically closed field is the product
of a closed unipotent subgroup and the centralizer of any given torus. -/
theorem solvableTorusCentralizerProduct : SolvableTorusCentralizerProductStatement.{u} := by
  intro k _ _ G _ _ _ hG T j hj hT C c hc
  obtain ⟨M, m, hm, f, hf⟩ := exists_maximalTorus_extension_of_finiteType G j hT hj
  obtain ⟨U, i, hi, -, -, hU, -, -, hmul⟩ := solvableMaximalTorusSemidirect k G hG M m hm
  let factor : M.toGrp ⟶ C := hc.factorHom m (range_le_torusCentralizer_of_factor j m f hf)
  have hfactor : factor ≫ c = m := hc.factorHom_comp _ _
  have hfactorOver : factor.hom.hom ≫ c.hom.hom = m.hom.hom :=
    congrArg (fun g => g.hom.hom) hfactor
  let productMap := U.X ◁ factor.hom.hom
  have hproduct : productMap ≫ subgroupMultiplication i c = subgroupMultiplication i m := by
    simp only [productMap, subgroupMultiplication, MonObj.comp_mul, whiskerLeft_fst_assoc,
      whiskerLeft_snd_assoc, hfactorOver]
  have : IsIso (subgroupMultiplication i m).left :=
    inferInstanceAs (IsIso ((Over.forget _).map (subgroupMultiplication i m)))
  have : Surjective (productMap.left ≫ (subgroupMultiplication i c).left) := by
    rw [← Over.comp_left, hproduct]
    infer_instance
  exact ⟨U, i, hi, hU, Surjective.of_comp productMap.left _⟩

end Langlands.GroupScheme
