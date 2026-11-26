import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalOppositeModulusLevelDataStatement
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalOppositeLevelSetMeasureBoundStatement

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal ENNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.BruhatTits.SpecialCompact

namespace Langlands.HarishChandraSchwartz

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace

/-- A nonnegative weight with an integrable real negative height power also
has an integrable natural negative height power. -/
theorem UnipotentWeightIntegrable.exists_nat_exponent
    {H : Type*} [Group H] [MeasurableSpace H] {U : Subgroup H}
    {muU : Measure U} {w : U → ℝ} {σ : H → ℝ}
    (h : UnipotentWeightIntegrable muU w σ)
    (hw : ∀ u, 0 ≤ w u) (hσ : ∀ g, 0 ≤ σ g) :
    ∃ d : ℕ, ∫⁻ u, ENNReal.ofReal (w u * (1 + σ u) ^ (-(d : ℝ))) ∂muU < ⊤ := by
  obtain ⟨d, hd⟩ := h
  obtain ⟨n, hn⟩ := exists_nat_ge d
  refine ⟨n, lt_of_le_of_lt (lintegral_mono fun u => ?_) hd⟩
  apply ENNReal.ofReal_le_ofReal
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le (by linarith [hσ u]) (neg_le_neg hn)) (hw u)

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]

omit [LocallyOfFiniteType G.X.hom] in
/-- The actual logarithmic-height sublevels on a closed subgroup have finite
Haar measure, by properness of a closed matrix representation. -/
theorem measure_rationalHeight_sublevel_lt_top
    {U : Subgroup (rationalPoints G)} (hU : IsClosed (U : Set (rationalPoints G)))
    {N : ℕ} [Nonempty (Fin N)] (ρ : MatrixRepresentation G (Fin N))
    (hρ : IsClosedSubgroup ρ) (muU : Measure U) [muU.IsHaarMeasure] (R : ℝ) :
    muU {u : U | rationalHeight (F := F) ρ (u : rationalPoints G) ≤ R} < ⊤ := by
  have hcompact := hU.isClosedEmbedding_subtypeVal.isCompact_preimage
    (isCompact_rationalHeight_le ρ hρ R)
  exact hcompact.measure_lt_top

/-- The actual II.3.4 level data and actual II.4.1 volume theorem imply exactly
the natural-exponent weighted integrability statement, without further inputs. -/
theorem rationalUnipotentWeightIntegrability_of_levelStatements
    (hlevels : RationalOppositeModulusLevelDataStatement.{u})
    (hvolume : RationalOppositeLevelSetMeasureBoundStatement.{u}) :
    RationalUnipotentWeightIntegrabilityStatement.{u} := by
  intro F _ _ _ _ G _ _ hG S i hi ν hν J ζ hζ K0 hK0o hK0c hbasis hcover
    K hKo hPK hKc N _ ρ hρ muU _
  obtain ⟨L, hL, hw, hheight⟩ := hlevels F G hG S i hi ν hν J ζ hζ K hKo hPK hKc N ρ hρ
  have hq : (1 : ℝ) < (LocalField.residueCardinality F : ℝ) := by
    exact_mod_cast LocalField.residueCardinality_gt_one F
  have hvol := hvolume F G hG S i hi ν hν J ζ hζ K0 hK0o hK0c hbasis hcover
    K hKo hPK hKc muU L hL hw
  have hfin := measure_rationalHeight_sublevel_lt_top
    (Aubert.General.RationalPointFamily.isClosed_oppositeUnipotent_localField i ζ) ρ hρ muU
  exact (unipotentWeightIntegrable_of_levelSets hq hL hw
    (rationalHeight_nonneg ρ) hfin hvol hheight).exists_nat_exponent
      (fun u => iwasawaWeight_nonneg _) (rationalHeight_nonneg ρ)

end Langlands.HarishChandraSchwartz
