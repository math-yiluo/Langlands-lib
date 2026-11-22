import Langlands.Global.RankinSelberg.RealTriangularMatched
import Langlands.Global.RankinSelberg.RealLocalEqualShiftedProducts
import Langlands.Global.RankinSelberg.RealSquareFourierMarginal
import Langlands.Global.RankinSelberg.RealGodementRectangularFourier
import Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonFourierTransport
import Langlands.Representation.CompactRepresentativeWeights
import Langlands.Representation.Archimedean.PrincipalSeriesGKModule

/-! # Real orthogonal compact weights reproducing a square test and its Fourier transform -/

noncomputable section

open MeasureTheory Set
open Langlands.Archimedean Langlands.HarmonicAnalysis Langlands.LocalFactor.Archimedean
open Langlands.CompactRepresentativeWeights
open scoped NNReal ENNReal SchwartzMap Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealGodement

open ArchimedeanLocal

variable {j : ℕ}

local notation "O" => Matrix.unitaryGroup (Fin j) ℝ
local notation "Mat" => Matrix (Fin j) (Fin j) ℝ
local notation "G" => Langlands.GeneralLinear j ℝ
local notation "F[" b "]" => rectangularFourierIntegral (realScaledCharacter b) (realSelfDualMeasure b)
local notation "μ[" b "]" => RankinSelberg.rectangularMeasure (realSelfDualMeasure b) j j

private local instance compactFourierMatLocallyCompact : LocallyCompactSpace Mat :=
  inferInstanceAs (LocallyCompactSpace (Fin j → Fin j → ℝ))
private local instance compactFourierMatSecondCountable : SecondCountableTopology Mat :=
  inferInstanceAs (SecondCountableTopology (Fin j → Fin j → ℝ))

/-! ### Orthogonal matrices -/

/-- Inverse transpose fixes an orthogonal matrix. -/
theorem inverseTranspose_toUnits (k : O) :
    GeneralLinear.inverseTranspose j ℝ (Unitary.toUnits k) = Unitary.toUnits k := by
  apply Units.ext
  ext a c
  rw [GeneralLinear.inverseTranspose_entry]
  change star (k : Mat) c a = (k : Mat) a c
  rw [Matrix.star_apply, star_trivial]

private def leftMul (k : O) (X : Mat) : Mat := (k : Mat) * X

private theorem leftMul_mul (k l : O) (X : Mat) :
    leftMul (k * l) X = leftMul k (leftMul l X) := Matrix.mul_assoc _ _ _

private theorem leftMul_one (X : Mat) : leftMul 1 X = X := Matrix.one_mul _

private def leftMulAddEquiv (k : O) : Mat ≃+ Mat where
  toFun := leftMul k
  invFun := leftMul k⁻¹
  left_inv X := by rw [← leftMul_mul, inv_mul_cancel, leftMul_one]
  right_inv X := by rw [← leftMul_mul, mul_inv_cancel, leftMul_one]
  map_add' X Y := Matrix.mul_add _ _ _

private theorem continuous_leftMul (k : O) : Continuous (leftMul k) :=
  continuous_const.matrix_mul continuous_id

/-- Left multiplication by an orthogonal matrix preserves every additive Haar
measure on the real square matrix space. -/
theorem measurePreserving_realOrthogonalMatrixLeft (μ : Measure Mat) [μ.IsAddHaarMeasure]
    (k : O) : MeasurePreserving (fun X : Mat => (k : Mat) * X) μ μ := by
  let e := leftMulAddEquiv k
  have he : Continuous e := continuous_leftMul k
  let : (μ.map e).IsAddHaarMeasure :=
    e.isAddHaarMeasure_map μ he (continuous_leftMul k⁻¹)
  obtain ⟨S, hSc, hS⟩ := exists_compact_mem_nhds (0 : Mat)
  let f (p : O × Mat) := leftMul p.1 p.2
  let C := f '' (Set.univ ×ˢ S)
  have hf : Continuous f :=
    (continuous_subtype_val.comp continuous_fst).matrix_mul continuous_snd
  have hC : IsCompact C := (isCompact_univ.prod hSc).image hf
  have hSC : S ⊆ C := fun X hX => ⟨(1, X), ⟨Set.mem_univ _, hX⟩, leftMul_one X⟩
  have hpre : e ⁻¹' C = C := by
    ext X
    change leftMul k X ∈ C ↔ X ∈ C
    constructor
    · rintro ⟨⟨l, Y⟩, ⟨_, hY⟩, hE⟩
      change leftMul l Y = leftMul k X at hE
      refine ⟨(k⁻¹ * l, Y), ⟨Set.mem_univ _, hY⟩, ?_⟩
      change leftMul (k⁻¹ * l) Y = X
      rw [leftMul_mul, hE, ← leftMul_mul, inv_mul_cancel, leftMul_one]
    · rintro ⟨⟨l, Y⟩, ⟨_, hY⟩, hE⟩
      change leftMul l Y = X at hE
      refine ⟨(k * l, Y), ⟨Set.mem_univ _, hY⟩, ?_⟩
      change leftMul (k * l) Y = leftMul k X
      rw [leftMul_mul, hE]
  have hmap : (μ.map e) C = μ C := by
    rw [Measure.map_apply he.measurable hC.measurableSet, hpre]
  have hscale := Measure.isAddLeftInvariant_eq_smul (μ.map e) μ
  have hCpos := Measure.measure_pos_of_mem_nhds μ (Filter.mem_of_superset hS hSC)
  have hc : (Measure.addHaarScalarFactor (μ.map e) μ : ℝ≥0∞) = 1 := by
    apply (ENNReal.mul_left_inj hCpos.ne' hC.measure_lt_top.ne).mp
    have h := congrArg (fun ν : Measure Mat => ν C) hscale
    change μ.map e C = (Measure.addHaarScalarFactor (μ.map e) μ : ℝ≥0∞) * μ C at h
    rw [hmap] at h
    simpa only [one_mul] using h.symm
  refine ⟨he.measurable, ?_⟩
  change μ.map e = μ
  rw [hscale, ENNReal.coe_eq_one.mp hc, one_smul]

/-- The real square Fourier integral commutes with left translation by an
orthogonal matrix, with no measure multiplier. -/
theorem realOrthogonalMatrixFourier (b : ℝˣ) (k : O) (Φ : Mat → ℂ) (X : Mat) :
    F[b] (fun Y => Φ ((k : Mat) * Y)) X = F[b] Φ ((k : Mat) * X) := by
  let ν := realSelfDualMeasure b
  let μ := μ[b]
  let : ν.measure.IsAddHaarMeasure := ν.isAddHaar
  let : μ.IsAddHaarMeasure := RankinSelberg.rectangularMeasure_isAddHaar ν j j
  have hmap : μ.map (rectangularLeftRightHomeomorph (Unitary.toUnits k) (1 : G)) =
      (1 : ℝ≥0) • μ := by
    rw [one_smul]
    change μ.map (fun Y : Mat => (k : Mat) * Y * 1) = μ
    simpa only [Matrix.mul_one] using (measurePreserving_realOrthogonalMatrixLeft μ k).map_eq
  have h := rectangularFourierIntegral_leftRight (realScaledCharacter b) ν (Unitary.toUnits k)
    (1 : G) 1 hmap Φ X
  rw [inverseTranspose_toUnits, map_one] at h
  simp only [Units.val_one, Matrix.mul_one, NNReal.coe_one, Complex.ofReal_one, one_mul] at h
  exact h

/-! ### Fourier transport of a reproducing weight -/

variable (j) in
/-- A continuous weight on the orthogonal group reproducing an integrable square test
(with the determinant character `d` and left translates by `k⁻¹`) also reproduces its
real square Fourier transform, with the same character and the same translates. -/
def RealLocalCompactFourierWeightStatement : Prop :=
  ∀ (b : ℝˣ) (ν : Measure O) [IsFiniteMeasure ν] (κ : O → ℂ), Continuous κ →
  ∀ (d : RealCharacterData) (Ψ : Mat → ℂ), Integrable Ψ μ[b] →
    (∀ A, ∫ k, κ k * realCompactMatrixTranslate d Ψ (Unitary.toUnits k) A ∂ν = Ψ A) →
  ∀ X, ∫ k, κ k * realCompactMatrixTranslate d (F[b] Ψ) (Unitary.toUnits k) X ∂ν = F[b] Ψ X

private def matrixShear : O × Mat ≃ᵐ O × Mat where
  toFun p := (p.1, (Unitary.toUnits p.1)⁻¹.val * p.2)
  invFun p := (p.1, (p.1 : Mat) * p.2)
  left_inv := by
    rintro ⟨k, Y⟩
    change (k, (k : Mat) * ((Unitary.toUnits k)⁻¹.val * Y)) = (k, Y)
    rw [← Matrix.mul_assoc]
    change (k, ((Unitary.toUnits k).val * (Unitary.toUnits k)⁻¹.val) * Y) = (k, Y)
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul]
  right_inv := by
    rintro ⟨k, Y⟩
    change (k, (Unitary.toUnits k)⁻¹.val * ((k : Mat) * Y)) = (k, Y)
    rw [← Matrix.mul_assoc]
    change (k, ((Unitary.toUnits k)⁻¹.val * (Unitary.toUnits k).val) * Y) = (k, Y)
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]
  measurable_toFun := (continuous_fst.prodMk
    (((Units.continuous_val.comp continuous_unitary_toUnits.inv).comp continuous_fst).matrix_mul
      continuous_snd)).measurable
  measurable_invFun := (continuous_fst.prodMk
    ((continuous_subtype_val.comp continuous_fst).matrix_mul continuous_snd)).measurable

private theorem toUnits_inv_val (k : O) : (Unitary.toUnits k)⁻¹.val = ((k⁻¹ : O) : Mat) := rfl

theorem realLocalCompactFourierWeight : RealLocalCompactFourierWeightStatement j := by
  intro b ν _ κ hκ d Ψ hΨ hRepro X
  let μM := μ[b]
  let ψ := realScaledCharacter b
  let νR := realSelfDualMeasure b
  let : νR.measure.IsAddHaarMeasure := νR.isAddHaar
  let : μM.IsAddHaarMeasure := RankinSelberg.rectangularMeasure_isAddHaar νR j j
  let c (k : O) : ℂ := κ k * (d.character (GeneralLinear.determinant (Unitary.toUnits k)⁻¹) : ℂ)
  have hc : Continuous c := hκ.mul (Units.continuous_val.comp (d.character.continuous.comp
    (GeneralLinear.determinantContinuous.continuous.comp continuous_unitary_toUnits.inv)))
  have hcInt : Integrable c ν :=
    hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace c)
  let H (p : O × Mat) : ℂ := c p.1 * Ψ ((Unitary.toUnits p.1)⁻¹.val * p.2)
  let e := matrixShear (j := j)
  have he : MeasurePreserving e (ν.prod μM) (ν.prod μM) :=
    (MeasurePreserving.id ν).skew_product
      (((Units.continuous_val.comp continuous_unitary_toUnits.inv).comp continuous_fst).matrix_mul
        continuous_snd).measurable
      (Filter.Eventually.of_forall fun k => by
        simpa only [toUnits_inv_val] using
          (measurePreserving_realOrthogonalMatrixLeft μM k⁻¹).map_eq)
  have hH : Integrable H (ν.prod μM) :=
    (he.integrable_comp_emb e.measurableEmbedding).mpr (hcInt.mul_prod hΨ)
  let B (p : O × Mat) := H p * ψ.complex (rectangularPairing p.2 X)
  have hB : Integrable B (ν.prod μM) := by
    refine hH.mono (hH.aestronglyMeasurable.mul ?_) (Filter.Eventually.of_forall fun p => ?_)
    · exact (ψ.continuous_complex.comp ((continuous_rectangularPairing_left X).comp
        continuous_snd)).aestronglyMeasurable
    · simp only [B, norm_mul, ψ.norm_complex, mul_one, le_refl]
  symm
  calc
    (F[b] Ψ X) = ∫ Y : Mat, ∫ k : O, B (k, Y) ∂ν ∂μM := by
      apply integral_congr_ae
      refine Filter.Eventually.of_forall fun Y => ?_
      change Ψ Y * ψ.complex (rectangularPairing Y X) = ∫ k, B (k, Y) ∂ν
      have hY : (∫ k, H (k, Y) ∂ν) = Ψ Y := by
        simpa only [H, c, realCompactMatrixTranslate, mul_assoc] using hRepro Y
      rw [← hY, ← integral_mul_const]
    _ = ∫ p, B p ∂ν.prod μM := (integral_prod_symm _ hB).symm
    _ = ∫ k : O, ∫ Y : Mat, B (k, Y) ∂μM ∂ν := integral_prod _ hB
    _ = _ := by
      apply integral_congr_ae
      refine Filter.Eventually.of_forall fun k => ?_
      calc
        (∫ Y, B (k, Y) ∂μM) = c k * F[b] (fun Y => Ψ (((k⁻¹ : O) : Mat) * Y)) X := by
          simp only [B, H, mul_assoc, integral_const_mul, toUnits_inv_val]
          rfl
        _ = c k * F[b] Ψ (((k⁻¹ : O) : Mat) * X) :=
          congrArg (fun z : ℂ => c k * z) (realOrthogonalMatrixFourier b k⁻¹ Ψ X)
        _ = κ k * realCompactMatrixTranslate d (F[b] Ψ) (Unitary.toUnits k) X := by
          simp only [c, realCompactMatrixTranslate, toUnits_inv_val, mul_assoc]

/-! ### Fourier conventions -/

/-- The trace-pairing square Fourier transform of `RealSquareFourierMarginal` is the
entrywise rectangular Fourier transform of `RealGodementRectangularFourier`. -/
theorem matrixTransform_eq_realRectangularSchwartzFourier (b : ℝˣ) (Φ : 𝓢(Mat, ℂ)) :
    (RealSquareFourier.matrixTransform b Φ : Mat → ℂ) = realRectangularSchwartzFourier b Φ :=
  funext (Langlands.GodementJacquet.matrixTransform_eq_realRectangularSchwartzFourier b Φ)

/-! ### Finite weights -/

/-- A continuous weight whose left translates span a finite-dimensional space of
functions has finite orbit under the left regular representation. -/
theorem mem_finiteWeights_of_finiteDimensional (κ : C(O, ℂ))
    (h : FiniteDimensional ℂ (Submodule.span ℂ (range fun x : O => fun k : O => κ (x⁻¹ * k)))) :
    κ ∈ (finiteWeights : StarSubalgebra ℂ C(O, ℂ)) := by
  let T := Submodule.span ℂ (range fun x : O => fun k : O => κ (x⁻¹ * k))
  let L : C(O, ℂ) →ₗ[ℂ] (O → ℂ) :=
    { toFun := fun f => f
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hL : Function.Injective L := fun f g hfg => ContinuousMap.ext (congrFun hfg)
  have hle : (FiniteVectors.orbitSpan leftRegular κ).map L ≤ T := by
    rw [FiniteVectors.orbitSpan, Submodule.map_span, Submodule.span_le]
    rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
    exact Submodule.subset_span ⟨x, rfl⟩
  have hfin : FiniteDimensional ℂ ((FiniteVectors.orbitSpan leftRegular κ).map L) :=
    Submodule.finiteDimensional_of_le hle
  change Module.Finite ℂ (FiniteVectors.orbitSpan leftRegular κ)
  exact Module.Finite.of_injective
    ((Submodule.equivMapOfInjective L hL (FiniteVectors.orbitSpan leftRegular κ)).toLinearMap)
    (Submodule.equivMapOfInjective L hL _).injective

/-- The finite left orbit condition of the orthogonal density theorem, stated with the
compact subgroup of `GL_j(ℝ)`, is the same condition along `Unitary.toUnits`. -/
theorem finiteDimensional_toUnits_span (Φ : Mat → ℂ)
    (h : FiniteDimensional ℂ (Submodule.span ℂ (range fun k : unitaryCompact ℝ j =>
      fun X : Mat => Φ (k.val⁻¹.val * X)))) :
    FiniteDimensional ℂ (Submodule.span ℂ (range fun k : O =>
      fun X : Mat => Φ (((Unitary.toUnits k)⁻¹ : G).val * X))) := by
  have hr : (range fun k : O => fun X : Mat => Φ (((Unitary.toUnits k)⁻¹ : G).val * X)) ⊆
      range fun k : unitaryCompact ℝ j => fun X : Mat => Φ (k.val⁻¹.val * X) := by
    rintro _ ⟨k, rfl⟩
    exact ⟨⟨Unitary.toUnits k, k.property⟩, rfl⟩
  exact Submodule.finiteDimensional_of_le (Submodule.span_mono hr)

/-! ### Dual compact expansions -/

/-- A finite expansion of the compact average of right translates of `V` gives the
expansion of the same average of the Weyl inverse-transpose dual `g ↦ V(w (gᵀ)⁻¹)`,
because inverse transpose fixes orthogonal matrices. -/
theorem dualFunction_compactExpansion {c : ℕ} (ν : Measure O) (κ : O → ℂ) (V : G → ℂ)
    (Vj bj : Fin c → G → ℂ)
    (hExp : ∀ x g : G, (∫ k, κ k * V (x * Unitary.toUnits k * g) ∂ν) = ∑ i, Vj i x * bj i g)
    (x g : G) :
    (∫ k, κ k * ArchimedeanLocal.dualFunction j V (x * Unitary.toUnits k * g) ∂ν) =
      ∑ i, ArchimedeanLocal.dualFunction j (Vj i) x * bj i (GeneralLinear.inverseTranspose j ℝ g) := by
  have h (k : O) : ArchimedeanLocal.dualFunction j V (x * Unitary.toUnits k * g) =
      V ((GeneralLinear.weylLong j ℝ * GeneralLinear.inverseTranspose j ℝ x) * Unitary.toUnits k *
        GeneralLinear.inverseTranspose j ℝ g) := by
    simp only [ArchimedeanLocal.dualFunction, map_mul, inverseTranspose_toUnits, mul_assoc]
  simp only [h]
  exact hExp _ _

/-! ### Matched weights -/

variable (j) in
/-- For a square Schwartz test with finite left orthogonal orbit there is one weight with
finite left orbit on the orthogonal group which reproduces, with the same determinant
character, both the test and its real square Fourier transform. -/
def RealOrthogonalMatchedWeightStatement : Prop :=
  ∀ (b : ℝˣ) (ν : Measure O) [ν.IsHaarMeasure] (d : RealCharacterData) (Ψ : 𝓢(Mat, ℂ)),
    FiniteDimensional ℂ (Submodule.span ℂ (range fun k : unitaryCompact ℝ j =>
      fun X : Mat => Ψ (k.val⁻¹.val * X))) →
    ∃ κ : C(O, ℂ), κ ∈ (finiteWeights : StarSubalgebra ℂ C(O, ℂ)) ∧
      (∀ A, ∫ k, κ k * realCompactMatrixTranslate d Ψ (Unitary.toUnits k) A ∂ν = Ψ A) ∧
      ∀ X, ∫ k, κ k * realCompactMatrixTranslate d (realRectangularSchwartzFourier b Ψ)
        (Unitary.toUnits k) X ∂ν = realRectangularSchwartzFourier b Ψ X

theorem realOrthogonalMatchedWeight : RealOrthogonalMatchedWeightStatement j := by
  intro b ν _ d Ψ hfin
  obtain ⟨κ, hκ, hκfin, hrep⟩ := exists_realCompactMatrixWeight ν Unitary.toUnits
    continuous_unitary_toUnits d Ψ Ψ.continuous (finiteDimensional_toUnits_span Ψ hfin)
  have hΨ : Integrable (Ψ : Mat → ℂ) μ[b] := by
    let νR := realSelfDualMeasure b
    let : νR.measure.IsAddHaarMeasure := νR.isAddHaar
    let : (μ[b]).IsAddHaarMeasure := RankinSelberg.rectangularMeasure_isAddHaar νR j j
    exact Ψ.integrable
  refine ⟨⟨κ, hκ⟩, mem_finiteWeights_of_finiteDimensional ⟨κ, hκ⟩ hκfin, hrep, fun X => ?_⟩
  have hF : (realRectangularSchwartzFourier b Ψ : Mat → ℂ) = F[b] Ψ :=
    funext (realRectangularSchwartzFourier_apply b Ψ)
  rw [hF]
  exact realLocalCompactFourierWeight b ν κ hκ d Ψ hΨ hrep X

end Langlands.Global.RankinSelbergGlobal.RealGodement
