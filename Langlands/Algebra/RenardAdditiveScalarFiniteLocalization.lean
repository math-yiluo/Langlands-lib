import Langlands.Algebra.RenardAdditiveScalarFiniteLocalizationStatements
import Langlands.Algebra.RenardStableIdealFiniteLocalizationProof

/-!
# Additive stable generation implies scalar-linear finite localization

The generic comparisons forget scalar closure through `Submodule.toAddSubgroup`.
The complex localization consequence applies these comparisons to the regular
left action, the source action and the actual localized action, then uses the
published scalar-linear finite-localization theorem.
-/

set_option autoImplicit false

namespace Langlands.Algebra.AdditiveScalarStableGeneration

universe uR uB uV

/-- The same finite additive stable generating set generates among stable
scalar-linear submodules. -/
theorem moduleGenerationComparison : ModuleGenerationComparisonStatement.{uR, uB, uV} := by
  intro R B V _ _ _ _ _ _ _ ρ h
  obtain ⟨S, hS⟩ := h
  refine ⟨S, ?_⟩
  intro P hP hSP
  exact Submodule.toAddSubgroup_eq_top.mp (hS P.toAddSubgroup hP hSP)

/-- Every stable scalar-linear submodule inherits finite stable generation
from its actual underlying additive subgroup. -/
theorem submoduleGenerationComparison :
    SubmoduleGenerationComparisonStatement.{uR, uB, uV} := by
  intro R B V _ _ _ _ _ _ _ ρ h P hP
  obtain ⟨S, hSP, hS⟩ := h P.toAddSubgroup hP
  refine ⟨S, hSP, ?_⟩
  intro Q hQ hSQ
  exact hS Q.toAddSubgroup hQ hSQ

end Langlands.Algebra.AdditiveScalarStableGeneration

namespace Langlands.Renard.AlgebraActionLocalization

open Langlands.Algebra EndomorphismLocalization
open Langlands.Algebra.AdditiveScalarStableGeneration

universe uB uV

/-- The three written additive generation assumptions imply the existing
actual compatible localization and stable-image conclusions. -/
theorem additiveIdealFiniteLocalization : AdditiveIdealFiniteLocalizationStatement.{uB, uV} := by
  intro B _ _ _ _ V _ _ ρ f hB hV hL
  let σ := localizedAction f.toLinearMap ρ fun b v => f.map_action' b v
  exact stableIdealFiniteLocalization B V ρ f
    (submoduleGenerationComparison ℂ B B (NonUnitalAlgHom.lmul ℂ B) hB)
    (moduleGenerationComparison ℂ B V ρ hV)
    (moduleGenerationComparison ℂ B (Localized f.toLinearMap) σ hL)

end Langlands.Renard.AlgebraActionLocalization

namespace Langlands.Renard

universe uR uB uV

/-- Additive stable generation supplies both scalar-linear comparisons and
actual finite localization, with independent universes in the stated order. -/
theorem additiveScalarFiniteLocalization : AdditiveScalarFiniteLocalizationStatement.{uR, uB, uV} :=
  ⟨Langlands.Algebra.AdditiveScalarStableGeneration.moduleGenerationComparison,
    Langlands.Algebra.AdditiveScalarStableGeneration.submoduleGenerationComparison,
    AlgebraActionLocalization.additiveIdealFiniteLocalization⟩

end Langlands.Renard

/- The complete closed interface retains unequal coefficient, algebra and
carrier universe assignments, in both orders. -/
example : Langlands.Renard.AdditiveScalarFiniteLocalizationStatement.{0, 1, 2} :=
  Langlands.Renard.additiveScalarFiniteLocalization.{0, 1, 2}

example : Langlands.Renard.AdditiveScalarFiniteLocalizationStatement.{2, 1, 0} :=
  Langlands.Renard.additiveScalarFiniteLocalization.{2, 1, 0}
