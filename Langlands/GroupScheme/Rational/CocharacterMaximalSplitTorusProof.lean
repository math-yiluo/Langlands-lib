import Langlands.GroupScheme.Rational.MaximalSplitTorusStatement
import Langlands.GroupScheme.Rational.SplitTorusImage
import Langlands.GroupScheme.Rational.MaximalSplitTorusExtension

/-! # Every cocharacter factors through a maximal split torus -/

universe u
open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Every cocharacter of an affine locally finite-type group scheme over a field factors
through an actual maximal split torus, with no further hypotheses on the field or group. -/
theorem cocharacterMaximalSplitTorus : CocharacterMaximalSplitTorusStatement.{u} := by
  intro k _ G _ _ χ
  obtain ⟨D, π, i, hi, hπ, _⟩ :=
    isSplitTorus_gm.exists_factor_isSplitSubtorus χ
  obtain ⟨T, j, hj, f, hf⟩ := exists_maximalSplitTorus_extension G i hi
  refine ⟨T, j, Additive.ofMul (π ≫ f), hj, ?_⟩
  change (π ≫ f) ≫ j = χ
  rw [Category.assoc, hf, hπ]

end Langlands.GroupScheme
