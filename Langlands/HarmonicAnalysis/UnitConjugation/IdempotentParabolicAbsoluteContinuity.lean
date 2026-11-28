import Langlands.Analysis.Local.PolynomialZeroSet
import Langlands.HarmonicAnalysis.SubmersionMapAbsoluteContinuity
import Langlands.HarmonicAnalysis.UnitConjugation.IdempotentParabolicSubmersion
import Mathlib.Topology.Piecewise

/-! # Absolute continuity for idempotent parabolic conjugation

The conjugation map on a clopen set of unit coordinates times the upper triangular
Lie algebra pushes product additive Haar measure forward to an absolutely continuous
measure. The strict submersion locus is conull by a determinant polynomial.
-/

noncomputable section

namespace Langlands.HarmonicAnalysis.UnitConjugation.IdempotentCentralizer

open Filter Function MeasureTheory Set _root_.Topology
open scoped ENNReal NNReal

universe u v

variable (F : Type u) [NontriviallyNormedField F]
  {A : Type v} [NormedRing A] [NormedAlgebra F A] (e : A)

local notation "Levi" => Subalgebra.centralizer F (Set.singleton e)
local notation "Upper" => offDiagonalCorner F e
local notation "Coordinates" => A × (Levi × Upper)

/-- Extend parabolic conjugation by zero outside the supplied set of unit coordinates. -/
def parabolicChartConjugation (C : Set A) : Coordinates → A := by
  classical
  exact (Prod.fst ⁻¹' C).piecewise (parabolicConjugation F e) (fun _ => 0)

theorem parabolicChartConjugation_of_mem {C : Set A} {p : Coordinates} (hp : p.1 ∈ C) :
    parabolicChartConjugation F e C p = parabolicConjugation F e p := by
  classical
  unfold parabolicChartConjugation
  exact piecewise_eq_of_mem _ _ _ hp

variable [ProperSpace F] [FiniteDimensional F A] [MeasurableSpace A] [BorelSpace A]

/-- The adjoint action of the Levi coordinate on the off-diagonal summand is surjective
on an open conull locus, for every additive Haar measure on the Levi. -/
private theorem exists_open_conull_offDiagonalAdjoint_surjective (he : IsIdempotentElem e)
    (μM : Measure Levi) [μM.IsAddHaarMeasure] :
    ∃ U : Set Levi, IsOpen U ∧ (∀ᵐ y ∂μM, y ∈ U) ∧
      ∀ y ∈ U, Surjective (offDiagonalAdjoint F e y) := by
  classical
  let : MeasurableSpace F := borel F
  have : BorelSpace F := ⟨rfl⟩
  have : ProperSpace Levi := FiniteDimensional.proper F Levi
  let b := Module.finBasis F Levi
  let coord := b.equivFun.toContinuousLinearEquiv
  let q := (LinearMap.polyCharpoly (offDiagonalAdjoint F e) b).coeff 0
  let U : Set Levi := {y | MvPolynomial.eval (coord y) q ≠ 0}
  have hEval (y : Levi) :
      MvPolynomial.eval (coord y) q = (offDiagonalAdjoint F e y).charpoly.constantCoeff := by
    change MvPolynomial.eval (b.repr y) q = _
    rw [LinearMap.polyCharpoly_coeff_eval, ← Polynomial.constantCoeff_apply]
  have heM : e ∈ Levi := (mem_centralizer_singleton_iff F).2 rfl
  have hqVal : MvPolynomial.eval (coord ⟨e, heM⟩) q ≠ 0 := by
    rw [hEval]
    exact ((LinearMap.not_hasEigenvalue_zero_tfae (offDiagonalAdjoint F e ⟨e, heM⟩)).out 3 6).2
      (offDiagonalAdjoint_injective he heM)
  have hq : q ≠ 0 := fun h => hqVal (by rw [h, map_zero])
  have hU : IsOpen U := isOpen_compl_singleton.preimage
    ((MvPolynomial.continuous_eval q).comp coord.continuous)
  let μF : Measure F := Measure.addHaar
  have : μF.IsAddHaarMeasure := inferInstanceAs (Measure.addHaar : Measure F).IsAddHaarMeasure
  let μCoord := Measure.pi fun _ : Fin (Module.finrank F Levi) => μF
  have : μCoord.IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  let μ' := μCoord.map coord.symm
  have : μ'.IsAddHaarMeasure := coord.symm.isAddHaarMeasure_map μCoord
  have hAC : μM ≪ μ' := by
    rw [Measure.isAddLeftInvariant_eq_smul μM μ']
    exact Measure.smul_absolutelyContinuous
  have hAE : ∀ᵐ y ∂μ', y ∈ U := by
    apply (ae_map_iff coord.symm.continuous.measurable.aemeasurable hU.measurableSet).2
    simpa [U] using Langlands.Analysis.ae_eval_ne_zero μF (Module.finrank F Levi) q hq
  refine ⟨U, hU, hAC.ae_le hAE, ?_⟩
  intro y hy
  have hCoeff : (offDiagonalAdjoint F e y).charpoly.constantCoeff ≠ 0 := hEval y ▸ hy
  exact LinearMap.injective_iff_surjective.mp (LinearMap.ker_eq_bot.mp
    (((LinearMap.not_hasEigenvalue_zero_tfae (offDiagonalAdjoint F e y)).out 3 5).mp hCoeff))

private theorem ultrametric_prod (X Y : Type*) [PseudoMetricSpace X] [PseudoMetricSpace Y]
    [IsUltrametricDist X] [IsUltrametricDist Y] : IsUltrametricDist (X × Y) := by
  constructor
  intro a b c
  simp only [Prod.dist_eq]
  exact max_le
    ((IsUltrametricDist.dist_triangle_max a.1 b.1 c.1).trans
      (max_le_max (le_max_left _ _) (le_max_left _ _)))
    ((IsUltrametricDist.dist_triangle_max a.2 b.2 c.2).trans
      (max_le_max (le_max_right _ _) (le_max_right _ _)))

/-- In a clopen set of additive unit coordinates, the parabolic conjugation map pushes
the product of additive Haar measures forward to a measure absolutely continuous with
respect to ambient additive Haar measure. -/
def IdempotentParabolicAbsoluteContinuityStatement [IsUltrametricDist A] : Prop :=
  IsIdempotentElem e →
    ∀ (C : Set A), IsClopen C → (∀ a ∈ C, IsUnit a) →
      ∀ (μA : Measure A) [μA.IsAddHaarMeasure]
        (μM : Measure Levi) [μM.IsAddHaarMeasure]
        (μU : Measure Upper) [μU.IsAddHaarMeasure]
        (ν : Measure A) [ν.IsAddHaarMeasure],
        Continuous (parabolicChartConjugation F e C) ∧
        Measure.map (parabolicChartConjugation F e C)
          ((μA.restrict C).prod (μM.prod μU)) ≪ ν

theorem idempotentParabolicAbsoluteContinuity [IsUltrametricDist A] :
    IdempotentParabolicAbsoluteContinuityStatement F e := by
  classical
  intro he C hC hUnits μA _ μM _ μU _ ν _
  have : ProperSpace A := FiniteDimensional.proper F A
  have : ProperSpace Levi := FiniteDimensional.proper F Levi
  have : ProperSpace Upper := FiniteDimensional.proper F Upper
  let T : Set Coordinates := Prod.fst ⁻¹' C
  have hT : IsClopen T := ⟨hC.1.preimage continuous_fst, hC.2.preimage continuous_fst⟩
  let Φ := parabolicChartConjugation F e C
  have hΦ : Continuous Φ := by
    change Continuous (T.piecewise (parabolicConjugation F e) fun _ => 0)
    apply continuous_piecewise
    · simp [hT.frontier_eq]
    · rw [hT.1.closure_eq]
      intro p hp
      obtain ⟨g, hg⟩ := hUnits p.1 hp
      have hInv : ContinuousAt (Ring.inverse : A → A) p.1 := by
        rw [← hg]
        exact (hasStrictFDerivAt_ringInverse (𝕜 := F) g).continuousAt
      have hY : Continuous (fun x : Coordinates => (x.2.1 : A)) :=
        continuous_subtype_val.comp (continuous_fst.comp continuous_snd)
      have hZ : Continuous (fun x : Coordinates => (x.2.2 : A)) :=
        continuous_subtype_val.comp (continuous_snd.comp continuous_snd)
      exact ((continuous_fst.continuousAt.mul (hY.add hZ).continuousAt).mul
        (hInv.comp continuous_fst.continuousAt)).continuousWithinAt
    · exact continuousOn_const
  obtain ⟨U, hU, hUae, hSurj⟩ := exists_open_conull_offDiagonalAdjoint_surjective F e he μM
  let μ := μA.prod (μM.prod μU)
  have : μ.IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure _ _
  let R : Set Coordinates := (fun p : Coordinates => p.2.1) ⁻¹' U
  have hR : IsOpen R := hU.preimage (continuous_fst.comp continuous_snd)
  have hRae : ∀ᵐ p ∂μ, p ∈ R := by
    apply (Measure.ae_prod_iff_ae_ae hR.measurableSet).2
    apply Eventually.of_forall
    intro _
    exact (Measure.ae_prod_iff_ae_ae (hU.measurableSet.preimage measurable_fst)).2
      (hUae.mono fun _ hy => Eventually.of_forall fun _ => hy)
  have hRestrict : μ.restrict (T ∩ R) = (μA.restrict C).prod (μM.prod μU) := by
    rw [Measure.restrict_prod_eq_prod_univ, Set.prod_univ]
    change μ.restrict (T ∩ R) = μ.restrict T
    apply Measure.restrict_congr_set
    filter_upwards [hRae] with p hp
    simp [hp]
  refine ⟨hΦ, ?_⟩
  rw [← hRestrict]
  have : IsUltrametricDist (Levi × Upper) := ultrametric_prod _ _
  have : IsUltrametricDist Coordinates := ultrametric_prod _ _
  refine submersionMapAbsoluteContinuity F Coordinates A μ ν Φ (T ∩ R) hΦ
    (hT.2.inter hR) ?_
  intro p hp
  obtain ⟨g, hg⟩ := hUnits p.1 hp.1
  obtain ⟨D, hD, hDSurj⟩ := idempotentParabolicSubmersion F e he g p.2.1 p.2.2
    (hSurj p.2.1 hp.2)
  have hPoint : ((g : A), (p.2.1, p.2.2)) = p := Prod.ext hg rfl
  rw [hPoint] at hD
  refine ⟨D, hD.congr_of_eventuallyEq ?_, hDSurj⟩
  filter_upwards [hT.2.mem_nhds hp.1] with x hx
  exact (parabolicChartConjugation_of_mem F e hx).symm

end Langlands.HarmonicAnalysis.UnitConjugation.IdempotentCentralizer
