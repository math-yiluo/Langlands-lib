import Langlands.GroupScheme.Rational.SemistandardProperLeviRank
import Langlands.GroupScheme.Rational.SemistandardSpectralDynamicCoverageProof
import Langlands.GroupScheme.Rational.CentralizerRootSupport
import Langlands.GroupScheme.Rational.SplitTorusRationalRank
import Langlands.GroupScheme.Rational.RootFiniteness
import Langlands.GroupScheme.Dynamic.ImproperParabolic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! # Relative rank drops in every proper semistandard Levi -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.LinearAlgebra.RationalSpan

namespace Langlands.GroupScheme

theorem semistandardProperLeviRank : SemistandardProperLeviRankStatement.{u} := by
  intro k _ G hG T i hi p hp M j hj _hjc hM
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : IsAffineHom M.X.hom := hM.isAffineHom
  let : Smooth G.X.hom := hG.smooth
  let : Smooth M.X.hom := hM.smooth
  let : ConnectedSpace G.X.left := hG.connectedSpace
  let a := semistandardLeviSplitTorus p hj
  have ha : a ≫ j = i := semistandardLeviSplitTorus_comp p hj
  have hT := hi.isSplitSubtorus.1
  let : Module.Finite ℚ (relativeRootSpan i) := hT.finite_relativeRootSpan i
  obtain ⟨ν, hν⟩ := semistandardSpectralDynamicCoverage k G hG T i hi p
  have hP : Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i) = p.parabolic :=
    congrArg SemistandardSpectralIndex.parabolic hν
  have hL : Dynamic.centralizer (CommGroupScheme.groupHom ν ≫ i) = p.levi :=
    congrArg SemistandardSpectralIndex.levi hν
  have hcentral : IsCentral (CommGroupScheme.groupHom ν ≫ a) :=
    (isCentral_comp_iff_le_dynamicCentralizer hj a ha ν).mpr hL.ge
  have hker := relativeRootSpan_le_centralRestrictionKer a ν isSplitTorus_gm hcentral
  change Module.finrank ℚ (relativeRootSpan a) < Module.finrank ℚ (relativeRootSpan i)
  apply Submodule.finrank_lt_finrank_of_lt
  refine lt_of_le_not_ge (Submodule.span_mono (Set.image_mono
    (relativeRoots_subset_of_factor hj a ha))) ?_
  intro hreverse
  apply hp
  rw [← hP]
  apply Dynamic.parabolic_eq_top_of_centralizer
  apply (isCentral_iff_dynamicCentralizer_eq_top _).mp
  apply rootAnnihilatorCentrality k G T hT i ν
  intro α hα
  have hzero := hker (hreverse (toRat_mem_ratSpan hα))
  change rationalCharacterRestrictRat (CommGroupScheme.groupHom ν) (toRat α) = 0 at hzero
  rw [rationalCharacterRestrictRat_toRat] at hzero
  have hre : ν ≫ α = 0 :=
    isSplitTorus_gm.character_toRat_injective (hzero.trans (map_zero toRat).symm)
  simp only [latticePairing_apply, hre, map_zero]

end Langlands.GroupScheme
