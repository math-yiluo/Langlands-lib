import Langlands.BaseChange.TwistedCharacterRegularValuesReduction
import Langlands.BaseChange.TwistedCharacter.MatrixHaarChart
import Langlands.BaseChange.TwistedConjugationMatrixSubmersion
import Langlands.Group.GL.FiniteProductCartan
import Langlands.HarmonicAnalysis.CompactSubmersionPushforwardStatement

/-! # Compact pushforwards in the proof of twisted character regularity -/

noncomputable section

namespace Langlands.BaseChange

open Filter HarmonicAnalysis HarishChandraSchwartz MeasureTheory Set Topology
open scoped ENNReal NNReal Topology

universe u v uW

private theorem ultrametricDist_prod (A B : Type*) [PseudoMetricSpace A] [PseudoMetricSpace B]
    [IsUltrametricDist A] [IsUltrametricDist B] : IsUltrametricDist (A × B) :=
  ⟨fun a b c => by
    simpa only [Prod.dist_eq, max_assoc, max_comm, max_left_comm] using
      max_le_max (dist_triangle_max a.1 b.1 c.1) (dist_triangle_max a.2 b.2 c.2)⟩

section Pushforward

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] [CharZero F]
  (E : Type v) [CommRing E] [Algebra F E] [Module.Finite F E] [IsReduced E]
  [TopologicalSpace E] [IsTopologicalRing E] [IsModuleTopology F E]
  (σ : E ≃ₐ[F] E) (l n : ℕ)

local notation "G" => GeneralLinear n E
local notation "P" => GeneralLinear.upperTriangularSubgroup n E
local notation "Mat" => Matrix (Fin n) (Fin n) E
local notation "Tri" => Matrix.blockTriangularSubalgebra F E (id : Fin n → Fin n)

private theorem locallyConstantPushforward_of_compactSubmersion
    (hSub : CompactSubmersionPushforwardStatement.{u, v, v, v})
    (K : CompactOpenSubgroup G) (δ : G) (hσ : σ ^ l = 1) (hδ : IsSigmaRegular σ l δ) :
    let : CompactSpace K.toSubgroup := isCompact_iff_compactSpace.mp K.2
    HasLocallyConstantTwistedConjugationPushforward (entrywiseAut σ n) K.toSubgroup P δ := by
  classical
  let : CompactSpace K.toSubgroup := isCompact_iff_compactSpace.mp K.2
  change HasLocallyConstantTwistedConjugationPushforward (entrywiseAut σ n) K.toSubgroup P δ
  intro L
  let : CompactSpace L.toSubgroup := isCompact_iff_compactSpace.mp L.2
  let : NontriviallyNormedField F := LocalGalois.localNormedField F
  let : CompleteSpace F := LocalGalois.localNormedField_complete F
  let : IsUltrametricDist F := LocalGalois.localNormedField_ultrametric F
  let : ProperSpace F := ProperSpace.of_nontriviallyNormedField_of_weaklyLocallyCompactSpace F
  let : IsModuleTopology F Mat := inferInstanceAs (IsModuleTopology F (Fin n → Fin n → E))
  let : NormedRing Mat := finiteAlgebraNormedRing F Mat
  let : NormedAlgebra F Mat := finiteAlgebraNormedAlgebra F Mat
  let : IsUltrametricDist Mat := finiteAlgebraNormedRing_ultrametric F Mat
  let : IsUltrametricDist Tri := IsUltrametricDist.subtype (fun A : Mat => A ∈ Tri)
  let : IsUltrametricDist (Mat × Tri) := ultrametricDist_prod Mat Tri
  let : ProperSpace Mat := FiniteDimensional.proper F Mat
  let : ProperSpace Tri := FiniteDimensional.proper F Tri
  let : MeasurableSpace Mat := borel Mat
  let : BorelSpace Mat := ⟨rfl⟩
  let : MeasurableSpace Tri := borel Tri
  let : BorelSpace Tri := ⟨rfl⟩
  let : MeasurableSpace G := borel G
  let : BorelSpace G := ⟨rfl⟩
  let : MeasurableSpace K.toSubgroup := borel K.toSubgroup
  let : BorelSpace K.toSubgroup := ⟨rfl⟩
  let : MeasurableSpace L.toSubgroup := borel L.toSubgroup
  let : BorelSpace L.toSubgroup := ⟨rfl⟩
  have : SecondCountableTopology G := generalLinear_secondCountableTopology_of_finite F E n
  have : SecondCountableTopology K.toSubgroup := IsEmbedding.subtypeVal.secondCountableTopology
  have : SecondCountableTopology P := IsEmbedding.subtypeVal.secondCountableTopology
  have : SecondCountableTopology L.toSubgroup := IsEmbedding.subtypeVal.secondCountableTopology
  let μ : Measure (Mat × Tri) := Measure.addHaar
  let ν : Measure Mat := Measure.addHaar
  have hChart := isOpenEmbedding_compactMatrixHaarChart F E n K L
  let chart : K.toSubgroup × L.toSubgroup → Mat × Tri := compactMatrixHaarChart F E n K L
  obtain ⟨f, hfc, hfs, hf⟩ := exists_normalizedHaar_matrix_chartDensity F E n K L μ
  let S : Set (Mat × (Mat × Tri)) := Prod.snd ⁻¹' range chart
  have hS : IsClopen S :=
    (show IsClopen (range chart) from
      ⟨(isCompact_range hChart.continuous).isClosed, hChart.isOpen_range⟩).preimage continuous_snd
  let Φ : Mat × (Mat × Tri) → Mat := S.piecewise (twistedConjugationMatrixMap σ) (fun _ => 0)
  have hΦ : Continuous Φ := by
    apply continuous_piecewise
    · rw [isClopen_iff_frontier_eq_empty.mp hS]
      simp
    · rw [hS.1.closure_eq]
      apply (twistedConjugationMatrixMap_continuousOn σ).mono
      rintro z ⟨q, hq⟩
      exact ⟨q.1.val, congrArg Prod.fst hq⟩
    · exact continuous_const.continuousOn
  have hD (x : Mat × Tri) (hx : x ∈ tsupport (f : Mat × Tri → ℝ≥0)) :
      ∃ D : Mat × (Mat × Tri) →L[F] Mat, HasStrictFDerivAt Φ D (δ.val, x) ∧
        Function.Surjective (D.comp (ContinuousLinearMap.inr F Mat (Mat × Tri))) := by
    rw [hfs] at hx
    obtain ⟨q, rfl⟩ := hx
    obtain ⟨D, hD, hs⟩ :=
      twistedConjugationMatrixSubmersion F E σ l n δ q.1.val q.2.val.val q.2.val.property hσ hδ
    refine ⟨D, hD.congr_of_eventuallyEq ?_, hs⟩
    have hq : (δ.val, chart q) ∈ S := ⟨q, rfl⟩
    filter_upwards [hS.2.mem_nhds hq] with z hz
    exact (Set.piecewise_eq_of_mem _ _ _ hz).symm
  obtain ⟨U, hU, hδU, g, _, hmap⟩ := hSub F Mat (Mat × Tri) Mat μ ν Φ δ.val f hΦ hfc hD
  have hVal := (isOpenEmbedding_generalLinearVal F E n).measurableEmbedding
  have htransport (y : G) :
      Measure.map Units.val (twistedConjugationPushforward (entrywiseAut σ n) K.toSubgroup L y) =
        Measure.map (fun x => Φ (y.val, x)) (μ.withDensity (fun x => (f x : ℝ≥0∞))) := by
    let Pmap := twistedConjugationProductMap (entrywiseAut σ n) K.toSubgroup L y
    have hs : Measurable (fun x : Mat × Tri => Φ (y.val, x)) :=
      (hΦ.comp (continuous_const.prodMk continuous_id)).measurable
    have hPmap : Continuous Pmap := by
      have hk : Continuous fun q : K.toSubgroup × L.toSubgroup => q.1.val :=
        continuous_subtype_val.comp continuous_fst
      have hp : Continuous fun q : K.toSubgroup × L.toSubgroup => q.2.val.val :=
        continuous_subtype_val.comp (continuous_subtype_val.comp continuous_snd)
      have hσc := continuous_entrywiseAut_of_isModuleTopology σ n
      exact ((hk.mul continuous_const).mul (hσc.comp hk).inv).mul (hσc.comp hp)
    change Measure.map Units.val
      (Measure.map Pmap ((normalizedHaar K.toSubgroup).prod (normalizedHaar L.toSubgroup))) = _
    rw [← hf, Measure.map_map hVal.measurable hPmap.measurable,
      Measure.map_map hs hChart.continuous.measurable]
    congr 1
    funext q
    change (Pmap q).val = Φ (y.val, chart q)
    have hq : (y.val, chart q) ∈ S := ⟨q, rfl⟩
    rw [show Φ (y.val, chart q) = twistedConjugationMatrixMap σ (y.val, chart q) from
      Set.piecewise_eq_of_mem _ _ _ hq]
    exact (twistedConjugationMatrixMap_units σ y q.1.val q.2.val.val q.2.val.property).symm
  have hnear : {y : G | y.val ∈ U} ∈ 𝓝 δ :=
    (hU.preimage (isOpenEmbedding_generalLinearVal F E n).continuous).mem_nhds hδU
  filter_upwards [hnear] with y hy
  apply hVal.map_injective
  rw [htransport y, htransport δ, hmap _ hy, hmap _ hδU]

end Pushforward

/-- The compact additive submersion pushforward gives the geometry used by
the twisted compact averaging argument. -/
theorem twistedCharacterRegularValuesGeometry_of_compactSubmersion
    (hSub : CompactSubmersionPushforwardStatement.{u, v, v, v}) :
    TwistedCharacterRegularValuesGeometryStatement.{u, v} := by
  intro F _ _ _ _ _ E _ _ _ _ _ σ l n hE δ hδ
  let : Module.Finite F E := hE.1
  let : IsReduced E := hE.2.2.1
  obtain ⟨K, M, hCover, hContract⟩ := GeneralLinear.finiteAlgebraUpperTriangularCartan n F E
  exact ⟨K.toSubgroup, GeneralLinear.upperTriangularSubgroup n E, K.2, M, hCover, hContract,
    locallyConstantPushforward_of_compactSubmersion F E σ l n hSub K δ hE.pow_eq_one hδ⟩

/-- The compact submersion pushforward supplies the remaining premise of the
twisted character regularity reduction. -/
theorem twistedCharacterRegularValues_of_compactSubmersion
    (hSub : CompactSubmersionPushforwardStatement.{u, v, v, v}) :
    TwistedCharacterRegularValuesStatement.{u, v, uW} :=
  twistedCharacterRegularValuesReduction (twistedCharacterRegularValuesGeometry_of_compactSubmersion hSub)

end Langlands.BaseChange
