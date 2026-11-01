import Langlands.Representation.GodementJacquet.MatrixUnitValueStatement
import Langlands.Representation.GodementJacquet.CoefficientTransport
import Langlands.Representation.Smooth.Contragredient.AdmissibleDualityProof
import Langlands.Representation.Hecke.TestFunction
import Langlands.Representation.RankinSelberg.LastRowCompactOrbitProof
import Langlands.Group.GL.CompactOpen
import Langlands.Group.GL.NormalizedCharacter

/-! # Construction of a matrix integral equal to one -/

noncomputable section

namespace Langlands.GodementJacquet

open MeasureTheory HarmonicAnalysis RankinSelberg Topology
open scoped ENNReal NNReal

universe uF uV

namespace Padic

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance matrixUnitValueTopology : TopologicalSpace F.Carrier := F.canonicalTopologicalData.topology
local instance matrixUnitValueValuation : ValuativeRel F.Carrier := F.canonicalTopologicalData.valuativeRel
local instance matrixUnitValueLocalField : IsNonarchimedeanLocalField F.Carrier := F.canonicalTopologicalData.localField
local instance matrixUnitValueT2 : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2
local instance matrixUnitValueGLMeasurable (n : ℕ) : MeasurableSpace (Langlands.GeneralLinear (n + 1) F.Carrier) :=
  borel _
local instance matrixUnitValueGLBorel (n : ℕ) : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩

variable {n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V] [Nontrivial V]
  (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V)

/-- A nonzero smooth representation has a bi-smooth coefficient nonzero at one. -/
theorem exists_biSmoothCoefficient_ne_zero (hσ : IsSmooth σ) :
    ∃ (ℓ : SmoothDual σ) (v : smoothVectors σ), ℓ.val v.val ≠ 0 := by
  let G := Langlands.GeneralLinear (n + 1) F.Carrier
  have hcofinal : ∀ K : OpenSubgroup G, ∃ L : OpenSubgroup G,
      IsCompact (L : Set G) ∧ L ≤ K := by
    intro K
    obtain ⟨L, hLc, hLK⟩ := F.canonicalTopologicalData.generalLinearCompactOpen
      (n + 1) (K : Set G) (K.isOpen.mem_nhds K.one_mem)
    exact ⟨L, hLc, hLK⟩
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  have hℓ : ∃ ℓ : SmoothDual σ, ℓ.val v ≠ 0 := by
    by_contra! h
    apply hv
    apply smoothBidual_injective_of_compact_cofinal hcofinal σ hσ
    rw [map_zero]
    apply Subtype.ext
    apply LinearMap.ext
    intro ℓ
    exact h ℓ
  obtain ⟨ℓ, hℓ⟩ := hℓ
  exact ⟨ℓ, ⟨v, hσ v⟩, hℓ⟩

/-- A compact-open test gives an absolutely convergent matrix integral equal to
one for every complex parameter, without any analytic assumption. -/
theorem exists_matrixIntegral_one (hσ : IsSmooth σ) :
    ∃ (Φ : MatrixTestFunction n F.Carrier) (f : biSmoothMatrixCoefficients σ),
      ∀ s : ℂ, MatrixConverges F Φ s f.val ∧ matrixIntegral F Φ s f.val = 1 := by
  classical
  let T := F.canonicalTopologicalData
  let G := Langlands.GeneralLinear (n + 1) F.Carrier
  let X := Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier
  let μ := generalLinearHaar F.Carrier n
  obtain ⟨ℓ, v, hℓv⟩ := exists_biSmoothCoefficient_ne_zero F σ hσ
  obtain ⟨H, hHv⟩ := v.property
  obtain ⟨K, hKc, hKH⟩ := T.generalLinearCompactOpen
    (n + 1) (H : Set G) (H.isOpen.mem_nhds H.one_mem)
  have hKv (k : G) (hk : k ∈ K) : σ k v.val = v.val :=
    hHv ⟨k, hKH hk⟩
  have hdet (k : G) (hk : k ∈ K) : normalizedAbsoluteValue T k.val.det = 1 := by
    have h := T.determinantNorm_eq_one_of_mem_compact (n + 1) K.toSubgroup hKc k hk
    have h' : ((T.determinantNorm (n + 1) k : ℝ≥0) : ℝ) = 1 := by
      rw [h]
      rfl
    exact h'
  let U : Set X := Units.val '' (K : Set G)
  have hUc : IsCompact U := hKc.image Units.continuous_val
  have hUo : IsOpen U :=
    (isOpenEmbedding_generalLinear_val (n + 1)).isOpenMap _ K.isOpen
  have hmem (g : G) : g.val ∈ U ↔ g ∈ K := by
    constructor
    · rintro ⟨k, hk, he⟩
      exact Units.val_injective he ▸ hk
    · intro hg
      exact ⟨g, hg, rfl⟩
  have hKm : MeasurableSet (K : Set G) := K.isOpen.measurableSet
  have hKfin : μ (K : Set G) ≠ ∞ := hKc.measure_lt_top.ne
  have hKpos : μ (K : Set G) ≠ 0 := (K.isOpen.measure_pos μ ⟨1, K.one_mem⟩).ne'
  have hmass : (μ.real (K : Set G) : ℂ) ≠ 0 := by
    rw [Ne, Complex.ofReal_eq_zero, measureReal_def, ENNReal.toReal_eq_zero_iff]
    exact not_or.mpr ⟨hKpos, hKfin⟩
  let c : ℂ := (μ.real (K : Set G) : ℂ)⁻¹
  let Φ : MatrixTestFunction n F.Carrier :=
    c • Hecke.TestFunction.characteristic ⟨hUc.isClosed, hUo⟩ hUc
  let f : biSmoothMatrixCoefficients σ :=
    (ℓ.val v.val)⁻¹ •
      ⟨biSmoothCoefficient σ ℓ v, Submodule.subset_span ⟨ℓ, v, rfl⟩⟩
  have hf (g : G) (hg : g ∈ K) : f.val g = 1 := by
    change (ℓ.val v.val)⁻¹ * ℓ.val (σ g v.val) = 1
    rw [hKv g hg, inv_mul_cancel₀ hℓv]
  have hpt (s : ℂ) : GodementJacquet.matrixIntegrand
      (normalizedAbsoluteValue T) Φ s f.val =
        (K : Set G).indicator (fun _ => c) := by
    funext g
    by_cases hg : g ∈ K
    · have hΦ : Φ g.val = c := by
        change c * U.indicator (fun _ => (1 : ℂ)) g.val = c
        rw [Set.indicator_of_mem ((hmem g).mpr hg), mul_one]
      simp only [GodementJacquet.matrixIntegrand, hΦ, hf g hg,
        determinantWeight, hdet g hg, Complex.ofReal_one, Complex.one_cpow,
        mul_one, Set.indicator_of_mem hg]
    · have hΦ : Φ g.val = 0 := by
        change c * U.indicator (fun _ => (1 : ℂ)) g.val = 0
        rw [Set.indicator_of_notMem (fun h => hg ((hmem g).mp h)), mul_zero]
      simp only [GodementJacquet.matrixIntegrand, hΦ, zero_mul,
        Set.indicator_of_notMem hg]
  refine ⟨Φ, f, fun s => ⟨?_, ?_⟩⟩
  · change Integrable (GodementJacquet.matrixIntegrand
      (normalizedAbsoluteValue T) Φ s f.val) μ
    rw [hpt]
    exact (integrable_indicator_iff hKm).mpr (integrableOn_const (C := c) hKfin)
  · change (∫ g, GodementJacquet.matrixIntegrand
      (normalizedAbsoluteValue T) Φ s f.val g ∂μ) = 1
    rw [hpt, integral_indicator_const c hKm]
    change (μ.real (K : Set G) : ℂ) * (μ.real (K : Set G) : ℂ)⁻¹ = 1
    exact mul_inv_cancel₀ hmass

/-- The constant rational function one is attained by an actual test and
coefficient, before taking any Laurent span. -/
theorem one_mem_matrixRationalValues (hσ : IsSmooth σ) :
    (1 : RationalFunctions) ∈ matrixRationalValues F σ := by
  obtain ⟨Φ, f, h⟩ := exists_matrixIntegral_one F σ hσ
  refine ⟨Φ, f, ⟨0, fun s _ => (h (s + jpssShift n)).1⟩, 0, ?_⟩
  intro s _
  constructor
  · simp
  · simpa [matrixIntegral] using (h (s + jpssShift n)).2

/-- The inverse-transpose side is the ordinary side of the smooth pullback. -/
theorem one_mem_iotaMatrixRationalValues (hσ : IsSmooth σ) :
    (1 : RationalFunctions) ∈ iotaMatrixRationalValues F σ := by
  unfold iotaMatrixRationalValues
  rw [iotaMatrixRationalValues_eq_comp_inverseTranspose]
  exact one_mem_matrixRationalValues F
    (σ.comp (GeneralLinear.inverseTranspose (n + 1) F.Carrier).toMonoidHom)
    (isSmooth_comp _ (GeneralLinear.continuous_inverseTranspose _ _) hσ)

end Padic

/-- The unit belongs to both actual matrix rational-value families. -/
theorem matrixUnitValue : MatrixUnitValueStatement.{uF,uV} := by
  intro p _ F n V _ _ _ σ hσ
  exact ⟨Padic.one_mem_matrixRationalValues F σ hσ,
    Padic.one_mem_iotaMatrixRationalValues F σ hσ⟩

end Langlands.GodementJacquet
