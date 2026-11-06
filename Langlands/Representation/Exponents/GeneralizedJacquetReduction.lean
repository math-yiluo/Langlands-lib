import Langlands.Representation.Exponents.UniformCompressionStabilizationStatement
import Langlands.Representation.Jacquet.StationaryRangeLift

/-! # The generalized Jacquet lemma follows from uniform compression stabilization -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme

/-- A reduction between the two published VI.9.1 propositions. Uniform
stabilization remains an explicit premise of this helper theorem. -/
theorem generalizedJacquetLemma_of_uniformCompressionStabilization
    (hstable : UniformCompressionStabilizationStatement.{u, v}) :
    GeneralizedJacquetLemmaStatement.{u, v} := by
  intro k _ _ _ _ _ G hG
  have := hG.isAffineHom
  let : TopologicalSpace (rationalPoints G) := pointTopology
  intro _ _ χ K hK g hg hcontract V _ _ ρ hρ
  obtain ⟨b, hb⟩ := hstable k G hG χ K hK g hg hcontract
  have hranges := (hb V ρ hρ).1
  apply Jacquet.fixedJacquetMap_surjective_of_stationaryRanges ρ hρ hK hcontract
    (GroupScheme.Dynamic.centralizer_le_normalizer_unipotent χ (Over.mk (𝟙 _)))
  refine ⟨b, fun s hs => ?_⟩
  exact (hranges s hs).1.symm.trans (hranges b le_rfl).1

end Langlands.Aubert.General.RationalPointFamily
