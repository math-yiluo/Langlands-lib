import Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonCompactSynthesis
import Langlands.Representation.RankinSelberg.LastRowCompactOrbitProof
import Langlands.HarmonicAnalysis.Distribution.Subspace

/-! Actual matrix test functions realizing compact character-covariant functions. -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace Langlands.RankinSelberg.CompactWhittakerSynthesis

open MeasureTheory MeasureTheory.Measure HarmonicAnalysis Induction

universe uK

variable {K : Type uK} [Field K] [TopologicalSpace K]
  [IsTopologicalDivisionRing K] [T2Space K]

/-- A group test is extended by zero from the actual open set of invertible matrices. -/
def groupTestToMatrixTest (r : ℕ) :
    SchwartzBruhat (Langlands.GeneralLinear r K) →ₗ[ℂ]
      SchwartzBruhat (Matrix (Fin r) (Fin r) K) :=
  (SchwartzBruhat.extendZero (isOpenEmbedding_generalLinear_val (K := K) r).isOpen_range).comp
    (Hecke.TestFunction.pullback
      (isEmbedding_generalLinear_val (K := K) r).toHomeomorph.symm).toLinearMap

@[simp]
theorem groupTestToMatrixTest_apply (r : ℕ)
    (φ : SchwartzBruhat (Langlands.GeneralLinear r K)) (g : Langlands.GeneralLinear r K) :
    groupTestToMatrixTest r φ g.val = φ g := by
  unfold groupTestToMatrixTest
  change SchwartzBruhat.extendZero
    (isOpenEmbedding_generalLinear_val (K := K) r).isOpen_range
    ((Hecke.TestFunction.pullback
      (isEmbedding_generalLinear_val (K := K) r).toHomeomorph.symm) φ) g.val = _
  rw [SchwartzBruhat.extendZero_apply_of_mem
    (isOpenEmbedding_generalLinear_val (K := K) r).isOpen_range _ (Set.mem_range_self g)]
  simp only [Hecke.TestFunction.pullback_apply, Topology.IsEmbedding.toHomeomorph_symm_apply]

/-- The extension vanishes on every singular matrix. -/
theorem groupTestToMatrixTest_eq_zero (r : ℕ)
    (φ : SchwartzBruhat (Langlands.GeneralLinear r K))
    (A : Matrix (Fin r) (Fin r) K) (hA : ¬ IsUnit A) :
    groupTestToMatrixTest r φ A = 0 := by
  change SchwartzBruhat.extendZero
    (isOpenEmbedding_generalLinear_val (K := K) r).isOpen_range
    ((Hecke.TestFunction.pullback
      (isEmbedding_generalLinear_val (K := K) r).toHomeomorph.symm) φ) A = 0
  apply SchwartzBruhat.extendZero_apply_of_not_mem
    (isOpenEmbedding_generalLinear_val (K := K) r).isOpen_range
  rintro ⟨g, rfl⟩
  exact hA g.isUnit

/-- Its ambient topological support contains only invertible matrices. -/
theorem tsupport_groupTestToMatrixTest_subset (r : ℕ)
    (φ : SchwartzBruhat (Langlands.GeneralLinear r K)) :
    tsupport (groupTestToMatrixTest r φ : Matrix (Fin r) (Fin r) K → ℂ) ⊆
      Set.range (Units.val : Langlands.GeneralLinear r K → Matrix (Fin r) (Fin r) K) :=
  SchwartzBruhat.tsupport_extendZero_subset
    (isOpenEmbedding_generalLinear_val (K := K) r).isOpen_range _

/-- Compact scalar-character induction admits a single full-matrix test with
its actual supplied subgroup integral equal to the function at every group point. -/
theorem exists_matrix_characterOrbitIntegral_eq (r : ℕ)
    (hbasis : ∀ O : Set (Langlands.GeneralLinear r K), IsOpen O →
      (1 : Langlands.GeneralLinear r K) ∈ O →
      ∃ L : OpenSubgroup (Langlands.GeneralLinear r K),
        IsCompact (L : Set (Langlands.GeneralLinear r K)) ∧ (L : Set _) ⊆ O)
    (H : Subgroup (Langlands.GeneralLinear r K))
    (hH : IsClosed (H : Set (Langlands.GeneralLinear r K)))
    [MeasurableSpace H] [BorelSpace H]
    (μH : Measure H) [IsHaarMeasure μH] [IsMulRightInvariant μH]
    (χ : H →* ℂˣ) (hχ : Continuous χ)
    (f : CompactFunctions H (characterRepresentation χ)) :
    ∃ Φ : SchwartzBruhat (Matrix (Fin r) (Fin r) K),
      (∀ g : Langlands.GeneralLinear r K,
        Integrable (fun h : H => (((χ h)⁻¹ : ℂˣ) : ℂ) * Φ ((h : Langlands.GeneralLinear r K) * g).val) μH) ∧
      ∀ g : Langlands.GeneralLinear r K,
        (∫ h : H, (((χ h)⁻¹ : ℂˣ) : ℂ) * Φ ((h : Langlands.GeneralLinear r K) * g).val ∂μH) =
          eval H (characterRepresentation χ) f.1 g := by
  obtain ⟨φ, hφ⟩ := exists_characterOrbitIntegral_eq H hH μH χ hχ hbasis f
  refine ⟨groupTestToMatrixTest r φ, ?_, ?_⟩
  · intro g
    simpa only [groupTestToMatrixTest_apply] using characterOrbitIntegrable H hH μH χ hχ φ g
  · intro g
    simpa only [groupTestToMatrixTest_apply, characterOrbitIntegral] using hφ g

end Langlands.RankinSelberg.CompactWhittakerSynthesis
