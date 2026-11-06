import Langlands.Global.LocalModularCharacterAdjointDeterminantStatement
import Langlands.Global.FiniteCompletionLocalField
import Langlands.Global.CompletionResidueAdic
import Langlands.HarmonicAnalysis.PadicRectangularHaarScalingProof
import Langlands.HarmonicAnalysis.GeneralScalarHaarScalingProof
import Langlands.HarmonicAnalysis.TriangularHaarModulus
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.RingTheory.Complex

/-!
# Haar scaling of linear automorphisms over the completions of a number field

For every place `i` of a number field `F` and every `K`-linear automorphism `A` of `K^d`,
where `K = placeCompletion F i`, the additive Haar character of `A` is the normalized
absolute value `placeNorm F i (det A)`. The paired Markdown records the argument.
-/

noncomputable section

universe u

open MeasureTheory MeasureTheory.Measure NumberField
open scoped NNReal ENNReal WithZero

namespace Langlands.Global

set_option backward.isDefEq.respectTransparency false

section General

variable {K : Type*} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]

/-- The continuous additive automorphism of `ι → K` underlying a `K`-linear automorphism. -/
def linearPiContinuousAddEquiv {ι : Type*} [Finite ι] (A : (ι → K) ≃ₗ[K] (ι → K)) :
    (ι → K) ≃ₜ+ (ι → K) where
  toAddEquiv := A.toAddEquiv
  continuous_toFun := LinearMap.continuous_on_pi (A : (ι → K) →ₗ[K] (ι → K))
  continuous_invFun := LinearMap.continuous_on_pi (A.symm : (ι → K) →ₗ[K] (ι → K))

@[simp] theorem coe_linearPiContinuousAddEquiv {ι : Type*} [Finite ι]
    (A : (ι → K) ≃ₗ[K] (ι → K)) : ⇑(linearPiContinuousAddEquiv A) = ⇑A := rfl

end General

section ExtendByZero

variable {K : Type*} [Field K]

open Classical in
/-- A positive character of `Kˣ`, extended by zero to `K`. -/
def unitsCharWithZero (χ : Kˣ →* ℝ≥0) : K →*₀ ℝ≥0 where
  toFun a := if h : a = 0 then 0 else χ (Units.mk0 a h)
  map_zero' := by simp
  map_one' := by
    simp only [one_ne_zero, ↓reduceDIte]
    rw [show Units.mk0 (1 : K) one_ne_zero = 1 from Units.ext rfl, map_one]
  map_mul' a b := by
    by_cases ha : a = 0
    · simp [ha]
    by_cases hb : b = 0
    · simp [hb]
    simp only [mul_ne_zero ha hb, ha, hb, ↓reduceDIte, ← map_mul]
    congr 1
    exact Units.ext rfl

theorem unitsCharWithZero_units (χ : Kˣ →* ℝ≥0) (a : Kˣ) :
    unitsCharWithZero χ (a : K) = χ a := by
  classical
  change (if h : (a : K) = 0 then 0 else χ (Units.mk0 (a : K) h)) = χ a
  simp only [a.ne_zero, ↓reduceDIte, Units.mk0_val]

end ExtendByZero

section LinearScaling

variable {K : Type*} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]
  [SecondCountableTopology K] [LocallyCompactSpace K] [MeasurableSpace K] [BorelSpace K]

/-- **Haar scaling of a linear automorphism.** If multiplication by every unit `a` of the
field `K` scales one additive Haar measure of `K` by `χ a`, then every `K`-linear automorphism
`A` of `ι → K` scales additive Haar measure by `χ (det A)`. -/
theorem addEquivAddHaarChar_linearPi_eq (hK : IsField K)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [mE : MeasurableSpace (ι → K)] [BorelSpace (ι → K)]
    (ν : Measure K) [IsAddHaarMeasure ν] (χ : Kˣ →* ℝ≥0)
    (hχ : ∀ a : Kˣ, ν.map (fun x => (a : K) * x) = (χ a)⁻¹ • ν)
    (A : (ι → K) ≃ₗ[K] (ι → K)) :
    addEquivAddHaarChar (linearPiContinuousAddEquiv A) = χ (LinearEquiv.det A) := by
  have hm : mE = MeasurableSpace.pi :=
    (BorelSpace.measurable_eq).trans
      (@BorelSpace.measurable_eq (ι → K) _ MeasurableSpace.pi Pi.borelSpace).symm
  subst hm
  let _ : Field K := hK.toField
  set M := LinearMap.toMatrix' (A : (ι → K) →ₗ[K] (ι → K)) with hMdef
  have hdet : M.det = (LinearEquiv.det A : K) := by
    rw [hMdef, LinearMap.det_toMatrix', LinearEquiv.coe_det]
  have hM : M.det ≠ 0 := hdet ▸ (LinearEquiv.det A).ne_zero
  have hφ : ⇑(linearPiContinuousAddEquiv A) = ⇑(Matrix.toLin' M) := by
    rw [hMdef, Matrix.toLin'_toMatrix']
    rfl
  have hχ' : ∀ a : K, a ≠ 0 →
      ν.map (fun x => a * x) = (unitsCharWithZero χ a)⁻¹ • ν := by
    intro a ha
    have h := hχ (Units.mk0 a ha)
    rwa [← unitsCharWithZero_units χ (Units.mk0 a ha), Units.val_mk0] at h
  have hχ0 : χ (LinearEquiv.det A) ≠ 0 := (χ.toHomUnits (LinearEquiv.det A)).ne_zero
  apply Langlands.HarmonicAnalysis.addEquivAddHaarChar_eq_of_smul_map
    (addHaar : Measure (ι → K))
  rw [hφ, Langlands.HarmonicAnalysis.haarMeasure_map_matrix ν (unitsCharWithZero χ) hχ' _ hM,
    smul_smul, hdet, unitsCharWithZero_units, mul_inv_cancel₀ hχ0, one_smul]

end LinearScaling

section Transfer

variable {K k : Type*} [Ring K] [TopologicalSpace K] [IsTopologicalRing K]
  [LocallyCompactSpace K] [SecondCountableTopology K] [MeasurableSpace K] [BorelSpace K]
  [Ring k] [TopologicalSpace k] [IsTopologicalRing k] [MeasurableSpace k] [BorelSpace k]

/-- Scalar Haar scaling transfers along a ring isomorphism that is a homeomorphism: if left
multiplication by `e a` scales one additive Haar measure of `k` by `c`, then left
multiplication by `a` scales every additive Haar measure of `K` by `c`. -/
theorem map_mul_left_eq_smul_of_ringEquiv (e : K ≃+* k) (he : Continuous e)
    (he' : Continuous e.symm) (ν₀ : Measure k) [IsAddHaarMeasure ν₀] (a : K) (c : ℝ≥0)
    (h : ν₀.map (fun y => e a * y) = c • ν₀) (ν : Measure K) [IsAddHaarMeasure ν] :
    ν.map (fun x => a * x) = c • ν := by
  have : IsAddHaarMeasure (ν₀.map e.symm) :=
    e.symm.toAddEquiv.isAddHaarMeasure_map ν₀ he' he
  have hν : ν = addHaarScalarFactor ν (ν₀.map e.symm) • ν₀.map e.symm :=
    isAddLeftInvariant_eq_smul ν (ν₀.map e.symm)
  have hcomp : (fun x => a * x) ∘ e.symm = e.symm ∘ (fun y => e a * y) := by
    funext y
    simp
  have hma : Measurable fun x : K => a * x := (by fun_prop : Continuous fun x : K => a * x).measurable
  have hmb : Measurable fun y : k => e a * y :=
    (by fun_prop : Continuous fun y : k => e a * y).measurable
  rw [hν, Measure.map_smul _ hma.aemeasurable, Measure.map_map hma he'.measurable, hcomp,
    ← Measure.map_map he'.measurable hmb, h, Measure.map_smul _ he'.measurable.aemeasurable,
    smul_comm]

end Transfer

section Infinite

variable {F : Type*} [Field F]

open NumberField.InfinitePlace.Completion in
/-- Left multiplication by a nonzero `a` scales every additive Haar measure on an
archimedean completion by `‖a‖⁻ᵐ`, where `m` is the multiplicity of the place. -/
theorem infiniteCompletion_map_mul_left (w : InfinitePlace F)
    [MeasurableSpace w.Completion] [BorelSpace w.Completion]
    (ν : Measure w.Completion) [IsAddHaarMeasure ν] {a : w.Completion} (ha : a ≠ 0) :
    ν.map (fun x => a * x) = (‖a‖₊ ^ w.mult)⁻¹ • ν := by
  have := infiniteCompletion_secondCountableTopology F w
  rcases w.isReal_or_isComplex with hw | hw
  · have hn : ‖extensionEmbeddingOfIsReal hw a‖ = ‖a‖ :=
      (AddMonoidHomClass.isometry_iff_norm _).mp (isometry_extensionEmbeddingOfIsReal hw) a
    have hb : extensionEmbeddingOfIsReal hw a ≠ 0 := (map_ne_zero _).mpr ha
    refine map_mul_left_eq_smul_of_ringEquiv (ringEquivRealOfIsReal hw)
      (isometry_extensionEmbeddingOfIsReal hw).continuous
      (isometryEquivRealOfIsReal hw).symm.continuous volume a _ ?_ ν
    rw [ringEquivRealOfIsReal_apply, Real.map_volume_mul_left hb, ← Measure.coe_nnreal_smul,
      hw.mult_eq_one, pow_one, abs_inv, ← Real.norm_eq_abs, hn, ← ENNReal.ofReal_coe_nnreal,
      NNReal.coe_inv, coe_nnnorm]
  · have hn : ‖extensionEmbedding w a‖ = ‖a‖ :=
      (AddMonoidHomClass.isometry_iff_norm _).mp (isometry_extensionEmbedding w) a
    have hb : extensionEmbedding w a ≠ 0 := (map_ne_zero _).mpr ha
    refine map_mul_left_eq_smul_of_ringEquiv (ringEquivComplexOfIsComplex hw)
      (isometry_extensionEmbedding w).continuous
      (isometryEquivComplexOfIsComplex hw).symm.continuous (addHaar : Measure ℂ) a _ ?_ ν
    have hdet : LinearMap.det (Algebra.lmul ℝ ℂ (extensionEmbedding w a)) =
        ‖extensionEmbedding w a‖ ^ 2 := by
      rw [← Algebra.norm_apply, Algebra.norm_complex_apply, Complex.normSq_eq_norm_sq]
    have hdet0 : LinearMap.det (Algebra.lmul ℝ ℂ (extensionEmbedding w a)) ≠ 0 := by
      rw [hdet]
      exact pow_ne_zero 2 (norm_ne_zero_iff.mpr hb)
    rw [ringEquivComplexOfIsComplex_apply]
    have hmap := Measure.map_linearMap_addHaar_eq_smul_addHaar (addHaar : Measure ℂ) hdet0
    change (addHaar : Measure ℂ).map (Algebra.lmul ℝ ℂ (extensionEmbedding w a)) = _
    rw [hmap, ← Measure.coe_nnreal_smul, hw.mult_eq_two, hdet, hn, abs_of_nonneg (by positivity),
      ← ENNReal.ofReal_coe_nnreal, NNReal.coe_inv, NNReal.coe_pow, coe_nnnorm]

end Infinite

section Finite

variable {F : Type u} [Field F] [NumberField F]

open IsDedekindDomain HeightOneSpectrum GeneralLinear.Iwasawa in
/-- Left multiplication by a unit `a` scales every additive Haar measure on a finite
completion by `‖a‖⁻¹`, for the existing norm of the adic completion. -/
theorem finiteCompletion_map_mul_left (v : FinitePlace F)
    [MeasurableSpace (FiniteCompletion F v)] [BorelSpace (FiniteCompletion F v)]
    (ν : Measure (FiniteCompletion F v)) [IsAddHaarMeasure ν] (a : (FiniteCompletion F v)ˣ) :
    ν.map (fun x => (a : FiniteCompletion F v) * x) = (‖(a : FiniteCompletion F v)‖₊)⁻¹ • ν := by
  let := FiniteCompletion.valuativeRel v
  have := FiniteCompletion.isNonarchimedeanLocalField v
  have : (Valued.v : Valuation (FiniteCompletion F v) ℤᵐ⁰).Compatible :=
    Valuation.Compatible.ofValuation _
  have hE : (ValuativeRel.valuation (FiniteCompletion F v)).IsEquiv
      (Valued.v : Valuation (FiniteCompletion F v) ℤᵐ⁰) := ValuativeRel.isEquiv _ _
  obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer F
  have hϖv : Valued.v (π : FiniteCompletion F v) = WithZero.exp (-1) := by
    rw [valuedAdicCompletion_eq_valuation', hπ]
  have hϖ0 : (π : FiniteCompletion F v) ≠ 0 := by
    intro h
    rw [h, map_zero] at hϖv
    exact WithZero.exp_ne_zero hϖv.symm
  set ϖ : (FiniteCompletion F v)ˣ := Units.mk0 _ hϖ0 with hϖdef
  have hunif : IsUniformizingElement (ValuativeRel.valuation (FiniteCompletion F v)) ϖ := by
    refine ⟨?_, fun x hx => ?_⟩
    · rw [hϖdef, Units.val_mk0, hE.lt_one_iff_lt_one, hϖv, WithZero.exp_lt_one_iff]
      norm_num
    · have hx' : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).mpr hx
      refine ⟨-WithZero.log (Valued.v x), ?_⟩
      rw [← map_zpow₀, hE.eq_iff, map_zpow₀, hϖdef, Units.val_mk0, hϖv, ← WithZero.exp_zsmul,
        smul_neg, smul_eq_mul, mul_one, neg_neg, WithZero.exp_log hx']
  -- the valuation subrings of the two equivalent valuations coincide
  let eInt : (ValuativeRel.valuation (FiniteCompletion F v)).integer ≃+*
      v.adicCompletionIntegers F :=
    { toFun x := ⟨x.1, (mem_adicCompletionIntegers (𝓞 F) F v).mpr
        (hE.le_one_iff_le_one.mp (Valuation.mem_integer_iff _ _ |>.mp x.2))⟩
      invFun x := ⟨x.1, (Valuation.mem_integer_iff _ _).mpr
        (hE.le_one_iff_le_one.mpr ((mem_adicCompletionIntegers (𝓞 F) F v).mp x.2))⟩
      left_inv _ := rfl
      right_inv _ := rfl
      map_mul' _ _ := rfl
      map_add' _ _ := rfl }
  have hq : Ideal.absNorm v.asIdeal = Nat.card (IsLocalRing.ResidueField
      (ValuativeRel.valuation (FiniteCompletion F v)).integer) := by
    rw [← CompletionResidue.card_adicResidueField F v]
    exact Nat.card_congr (IsLocalRing.ResidueField.mapEquiv eInt).symm.toEquiv
  have habvϖ : NormedField.toAbsoluteValue (FiniteCompletion F v) (ϖ : FiniteCompletion F v) =
      ((Ideal.absNorm v.asIdeal : ℕ) : ℝ)⁻¹ := by
    rw [NormedField.toAbsoluteValue_apply, hϖdef, Units.val_mk0,
      NumberField.FinitePlace.norm_def, hϖv,
      WithZeroMulInt.toNNReal_neg_apply _ WithZero.exp_ne_zero,
      WithZero.toAdd_unzero_eq_log, WithZero.log_exp]
    simp
  have habv1 : ∀ x : FiniteCompletion F v, ValuativeRel.valuation (FiniteCompletion F v) x = 1 →
      NormedField.toAbsoluteValue (FiniteCompletion F v) x = 1 := by
    intro x hx
    rw [NormedField.toAbsoluteValue_apply, NumberField.FinitePlace.norm_def,
      hE.eq_one_iff_eq_one.mp hx, map_one, NNReal.coe_one]
  exact Langlands.HarmonicAnalysis.generalScalarHaarScalingStatement (FiniteCompletion F v)
    (Ideal.absNorm v.asIdeal) hq (NormedField.toAbsoluteValue _) ϖ hunif habvϖ habv1 ν a

end Finite

section Place

variable (F : Type u) [Field F] [NumberField F]

/-- Every actual completion of a number field is a field. -/
theorem placeCompletion.isField : (i : Place F) → IsField (placeCompletion F i)
  | .inl w => Field.toIsField w.Completion
  | .inr v => Field.toIsField (FiniteCompletion F v)

/-- Left multiplication by a unit `a` of an actual completion scales every additive Haar
measure by `(placeNormValue F i a)⁻¹`. -/
theorem placeCompletion_map_mul_left (i : Place F)
    [mK : MeasurableSpace (placeCompletion F i)] [hK : BorelSpace (placeCompletion F i)]
    (ν : Measure (placeCompletion F i)) [hν : IsAddHaarMeasure ν] (a : (placeCompletion F i)ˣ) :
    ν.map (fun x => (a : placeCompletion F i) * x) = (placeNormValue F i a)⁻¹ • ν := by
  rcases i with w | v
  · have : Nontrivial (placeCompletion F (.inl w)) := inferInstanceAs (Nontrivial w.Completion)
    exact @infiniteCompletion_map_mul_left F _ w mK hK ν hν _ a.ne_zero
  · exact @finiteCompletion_map_mul_left F _ _ v mK hK ν hν a

/-- The continuous additive automorphism of `K^d`, `K = placeCompletion F i`, underlying a
`K`-linear automorphism `A`. -/
abbrev placeLinearContinuousAddEquiv (i : Place F) {d : ℕ}
    (A : (Fin d → placeCompletion F i) ≃ₗ[placeCompletion F i] (Fin d → placeCompletion F i)) :
    (Fin d → placeCompletion F i) ≃ₜ+ (Fin d → placeCompletion F i) :=
  linearPiContinuousAddEquiv A

/-- **Haar normalization at a place.** A linear automorphism `A` of `K^d`,
`K = placeCompletion F i`, scales additive Haar measure by the normalized absolute value
`placeNorm F i (det A)`. -/
theorem addEquivAddHaarChar_placeLinear_eq_placeNorm (i : Place F) {d : ℕ}
    [MeasurableSpace (Fin d → placeCompletion F i)] [BorelSpace (Fin d → placeCompletion F i)]
    (A : (Fin d → placeCompletion F i) ≃ₗ[placeCompletion F i] (Fin d → placeCompletion F i)) :
    addEquivAddHaarChar (placeLinearContinuousAddEquiv F i A) =
      (placeNorm F i (LinearEquiv.det A) : ℝ≥0) := by
  let _ : MeasurableSpace (placeCompletion F i) := borel _
  have _ : BorelSpace (placeCompletion F i) := ⟨rfl⟩
  exact addEquivAddHaarChar_linearPi_eq (placeCompletion.isField F i) addHaar
    (placeNormValue F i) (placeCompletion_map_mul_left F i addHaar) A

end Place

end Langlands.Global
