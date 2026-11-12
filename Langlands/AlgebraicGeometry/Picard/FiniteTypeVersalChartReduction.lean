import Langlands.AlgebraicGeometry.Picard.FiniteTypeFormalVersalBundleStatement
import Langlands.AlgebraicGeometry.Picard.VersalAlgebraizationStatement
import Langlands.AlgebraicGeometry.Picard.FiniteTypePicardStackAtlasAssembly
import Langlands.AlgebraicGeometry.Picard.FiniteTypePointSmoothChartReduction
import Langlands.AlgebraicGeometry.Picard.VersalSmoothNeighbourhoodOfOpenness

/-! # Versal Picard charts from formal versality and algebraization -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Picard.PicardGroupoid

/-- A formally versal line bundle over a complete local base, followed by its
algebraization, gives a versal chart locally of finite type through every
finite-type field point. -/
theorem finiteTypeVersalChart_of_formalVersal
    (hF : FiniteTypeFormalVersalBundleStatement.{u})
    (hA : VersalAlgebraizationStatement.{u}) :
    FiniteTypeVersalChartStatement.{u} := by
  intro R _ _ X hp hf K _ _ _ L₀
  obtain ⟨A, _, _, _, _, _, ε, L, p, hε, hpε, hv, ⟨c⟩⟩ := hF R X hp hf K L₀
  obtain ⟨U, L', u₀, e, p', hp', hU, hv', ⟨c'⟩⟩ := hA R X hp hf K A ε hε L p hpε hv
  exact ⟨U, L', u₀, e, p', hp', hU, hv', ⟨c' ≪≫ c⟩⟩

/-- The smooth scheme atlas of the Picard stack over a finite-type `ℤ`-algebra,
from formal versality, algebraization and openness of versality. -/
theorem finiteTypePicardStackAtlas_of_versalInputs
    (hF : FiniteTypeFormalVersalBundleStatement.{u})
    (hA : VersalAlgebraizationStatement.{u})
    (hO : PicardOpennessOfVersalityStatement.{u}) :
    FiniteTypePicardStackAtlasStatement.{u} :=
  finiteTypePicardStackAtlas_of_pointSmoothCharts
    (finiteTypePointSmoothChart_of_versal
      (finiteTypeVersalChart_of_formalVersal hF hA)
      (versalSmoothNeighbourhood_of_openness hO))

set_option linter.defProp false in
/-- The implication proved by `finiteTypePicardStackAtlas_of_versalInputs`, as a
single term from the three versality inputs to the atlas statement. -/
def finiteTypePicardStackAtlasOfVersalInputs :
    FiniteTypeFormalVersalBundleStatement.{u} → VersalAlgebraizationStatement.{u} →
      PicardOpennessOfVersalityStatement.{u} → FiniteTypePicardStackAtlasStatement.{u} :=
  finiteTypePicardStackAtlas_of_versalInputs

end Langlands.AlgebraicGeometry.Picard.PicardGroupoid
