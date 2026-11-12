import Langlands.Automorphic.CuspidalAdmissible.EnergyConversion
import Langlands.Automorphic.CuspidalAdmissible.Split
import Langlands.Automorphic.CuspidalAdmissible.CompactEstimate
import Langlands.Automorphic.CuspidalAdmissible.CompactUnfold
import Langlands.Automorphic.CuspidalAdmissible.HaarInstances
import Langlands.Automorphic.UnitaryContragredientCriterion

/-!
# The separation property for the band unitary form

Let `b` be a unitary form of a cuspidal realization with unitary central character whose square
norm is the band integral of `|f|²`. For an open subgroup `L` of the finite adelic group and a
constant `C`, finitely many local averages separate the `L`-invariant vectors `e` with
`energy b e ≤ C · b(e, e)`.

The band integral of `|e|²` is bounded by the integral over the part of a Siegel set lying over
the band. That part is split into a compact region and cusp regions. On the cusp regions the
integral is at most `exp(-2(T - 2nK))` times a constant times the band integrals of the
derivatives of `e`, hence times `b(e, e)`; for `T` large this is at most `b(e, e)/4`. On the
compact region the integral is at most `ε` times a constant times `b(e, e)` plus a constant times
the squares of finitely many local averages of `e`; for `ε` small the first term is at most
`b(e, e)/4`. When the averages vanish, `b(e, e) ≤ b(e, e)/2`, so `e = 0`.
-/

noncomputable section

universe uF

open MeasureTheory NumberField
open scoped Classical Topology ENNReal NNReal

set_option autoImplicit false

namespace Langlands.Automorphic.CuspidalAdmissible

open Langlands.Global Langlands.Automorphic Langlands.Automorphic.ContinuousRationalFunctions
  Langlands.Automorphic.CuspidalL2 Langlands.Automorphic.OperatorDeterminantSlice

/-- A set covered by finitely many sets: the integral is at most the sum of the integrals. -/
theorem setLIntegral_le_add_sum {α ι : Type*} [MeasurableSpace α] [Fintype ι] (μ : Measure α)
    (f : α → ℝ≥0∞) {t K : Set α} {R : ι → Set α} (h : t ⊆ K ∪ ⋃ i, R i) :
    ∫⁻ x in t, f x ∂μ ≤ ∫⁻ x in K, f x ∂μ + ∑ i, ∫⁻ x in R i, f x ∂μ := by
  refine (lintegral_mono_set h).trans ((lintegral_union_le f K _).trans ?_)
  gcongr
  exact (lintegral_iUnion_le R f).trans (le_of_eq (tsum_fintype _))

/-- A choice of `T` making the cusp coefficient at most `1/4`. -/
theorem exists_exp_small (A : ℝ≥0∞) (hA : A ≠ ⊤) (K₀ : ℝ) (hK₀ : 0 ≤ K₀) :
    ∃ T : ℝ, 0 ≤ T ∧ K₀ ≤ T ∧
      ENNReal.ofReal (Real.exp (-(T - K₀)) ^ 2) * A ≤ ENNReal.ofReal (1 / 4) := by
  obtain ⟨M, hM, rfl⟩ : ∃ M : ℝ, 0 ≤ M ∧ A = ENNReal.ofReal M :=
    ⟨A.toReal, ENNReal.toReal_nonneg, (ENNReal.ofReal_toReal hA).symm⟩
  have hlog : 0 ≤ Real.log (4 * M + 1) := Real.log_nonneg (by linarith)
  refine ⟨K₀ + Real.log (4 * M + 1), by linarith, by linarith, ?_⟩
  have hT : -(K₀ + Real.log (4 * M + 1) - K₀) = -Real.log (4 * M + 1) := by ring
  rw [hT, Real.exp_neg, Real.exp_log (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have h0 : 0 ≤ (4 * M + 1)⁻¹ := by positivity
  have h1 : (4 * M + 1)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
  have h2 : ((4 * M + 1)⁻¹) ^ 2 ≤ (4 * M + 1)⁻¹ := by nlinarith
  calc ((4 * M + 1)⁻¹) ^ 2 * M ≤ (4 * M + 1)⁻¹ * M := mul_le_mul_of_nonneg_right h2 hM
    _ ≤ 1 / 4 := by
        rw [inv_mul_le_iff₀ (by positivity)]
        linarith

/-- A choice of `ε` making the smoothing coefficient at most `1/4`. -/
theorem exists_eps_small (A : ℝ≥0∞) (hA : A ≠ ⊤) :
    ∃ ε : ℝ, 0 < ε ∧ ENNReal.ofReal ε * A ≤ ENNReal.ofReal (1 / 4) := by
  obtain ⟨M, hM, rfl⟩ : ∃ M : ℝ, 0 ≤ M ∧ A = ENNReal.ofReal M :=
    ⟨A.toReal, ENNReal.toReal_nonneg, (ENNReal.ofReal_toReal hA).symm⟩
  refine ⟨(4 * (M + 1))⁻¹, by positivity, ?_⟩
  rw [← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [inv_mul_le_iff₀ (by positivity)]
  linarith

/-- `r ≤ r/4 + r/4` forces `r ≤ 0`. -/
theorem nonpos_of_le_two_quarters {r : ℝ} (hr : 0 ≤ r)
    (h : ENNReal.ofReal r ≤
      ENNReal.ofReal (1 / 4) * ENNReal.ofReal r + ENNReal.ofReal (1 / 4) * ENNReal.ofReal r) :
    r ≤ 0 := by
  rw [← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_add (by positivity) (by positivity),
    ENNReal.ofReal_le_ofReal_iff (by positivity)] at h
  linarith

variable {F : Type uF} [Field F] [NumberField F] {n : ℕ}

local instance separationIsAffine :
    _root_.AlgebraicGeometry.IsAffine (matrixGroupScheme F n).X.left :=
  Langlands.GroupScheme.GeneralLinear.isAffine_groupScheme (Fin n) (CommRingCat.of F)
local instance separationSmooth : _root_.AlgebraicGeometry.Smooth (matrixGroupScheme F n).X.hom :=
  Langlands.GroupScheme.GeneralLinear.smoothStatement (Fin n) (CommRingCat.of F)
local instance separationRationalGroup : AddCommGroup (RationalInvariantFunctions F n) :=
  Submodule.addCommGroup _
local instance separationContinuousGroup : AddCommGroup (ContinuousRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance separationSmoothGroup : AddCommGroup (FiniteSmoothRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance separationFormsGroup : AddCommGroup (AutomorphicForms F n) :=
  Submodule.addCommGroup _
local instance separationStableGroup : AddCommGroup (StableAutomorphicFunctions F n) :=
  Submodule.addCommGroup _

/-- Rational left translates keep the determinant band. -/
theorem point_rational_mul_mem_band (γ : RationalGL F n) {g : AdelicGL F n}
    (hg : point F n g ∈ band F n) : point F n (AdelicGL.rational F n γ * g) ∈ band F n := by
  have hdet : quotientDeterminantNorm F n (point F n (AdelicGL.rational F n γ * g)) =
      quotientDeterminantNorm F n (point F n g) := by
    rw [quotientDeterminantNorm_point, quotientDeterminantNorm_point, map_mul,
      AdelicBlockDeterminantCharacter.determinantNorm_rational, one_mul]
  change 1 < (quotientDeterminantNorm F n (point F n (AdelicGL.rational F n γ * g)) : ℝ≥0) ∧
    (quotientDeterminantNorm F n (point F n (AdelicGL.rational F n γ * g)) : ℝ≥0) < 2
  rw [hdet]
  exact hg

variable (S : OperatorRealization F n)

local instance separationSpaceGroup : AddCommGroup S.Space := Submodule.addCommGroup _

/-- The local average of a realized vector at `p`, as a linear functional. -/
def averageFunctional [MeasurableSpace (AdelicGL F n)] [BorelSpace (AdelicGL F n)]
    {U : Set (AdelicGL F n)} (hU : IsCompact U) (hU0 : matrixHaarMeasure F n U ≠ 0)
    (p : AdelicGL F n) : S.Space →ₗ[ℂ] ℂ where
  toFun e := average (matrixHaarMeasure F n) U (evaluate F n (S.toContinuous e)) p
  map_add' e f := by
    have := adelicGL_t2Space F n
    have h : evaluate F n (S.toContinuous (e + f)) =
        evaluate F n (S.toContinuous e) + evaluate F n (S.toContinuous f) := by
      funext x
      exact congrArg (fun v => evaluate F n v x) (map_add S.toContinuous e f)
    change average _ U (evaluate F n (S.toContinuous (e + f))) p = _
    rw [h]
    exact average_add _ hU hU0 (continuous_evaluate F n _) (continuous_evaluate F n _) p
  map_smul' a e := by
    have h : evaluate F n (S.toContinuous (a • e)) = a • evaluate F n (S.toContinuous e) := by
      funext x
      exact congrArg (fun v => evaluate F n v x) (map_smul S.toContinuous a e)
    change average _ U (evaluate F n (S.toContinuous (a • e))) p = a • _
    rw [h]
    exact average_smul _ U a _ p

/-- The compact estimate for the matrix Haar measure. -/
theorem exists_compact_estimate_matrix [MeasurableSpace (AdelicGL F n)]
    [BorelSpace (AdelicGL F n)] (L' : OpenSubgroup (FiniteAdelicGL F n))
    (hL'c : IsCompact (L' : Set (FiniteAdelicGL F n)))
    (Kc : Set (AdelicGL F n)) (hKc : IsCompact Kc) :
    ∃ K₃ : Set (AdelicGL F n), IsCompact K₃ ∧ ∀ ε : ℝ, 0 < ε →
      ∃ (U : Set (AdelicGL F n)) (P : Finset (AdelicGL F n)) (C : ℝ≥0∞),
        IsCompact U ∧ matrixHaarMeasure F n U ≠ 0 ∧ C ≠ ⊤ ∧
        ∀ (φ : AdelicGL F n → ℂ)
          (dφ : Fin (Module.finrank ℝ (ArchimedeanMatrix F n)) → AdelicGL F n → ℂ),
          Continuous φ → (∀ k, Continuous (dφ k)) →
          (∀ g, ∀ l ∈ L', φ (g * AdelicGL.ofFinite F n l) = φ g) →
          (∀ y : FiniteAdelicGL F n, ∃ s : ArchimedeanGL.SmoothFunctions F n,
            (∀ g, s.val g = φ (AdelicGL.ofInfinite F n g * AdelicGL.ofFinite F n y)) ∧
            ∀ k g, (ArchimedeanGL.smoothDifferential F n (ArchimedeanGL.lieDirection F n k) s).val g =
              dφ k (AdelicGL.ofInfinite F n g * AdelicGL.ofFinite F n y)) →
          ∫⁻ g in Kc, ‖φ g‖ₑ ^ 2 ∂matrixHaarMeasure F n ≤
            ENNReal.ofReal ε * ∑ k, ∫⁻ g in K₃, ‖dφ k g‖ₑ ^ 2 ∂matrixHaarMeasure F n +
              C * ∑ p ∈ P, ‖average (matrixHaarMeasure F n) U φ p‖ₑ ^ 2 := by
  have : SecondCountableTopology (AdelicGL F n) := secondCountableTopology_adelicGL F n
  have : (matrixHaarMeasure F n).IsMulRightInvariant := matrixHaarMeasure_isMulRightInvariant F n
  have : SFinite (matrixHaarMeasure F n) := sFinite_matrixHaarMeasure F n
  exact exists_compact_estimate F n (matrixHaarMeasure F n) L'.toSubgroup L'.isOpen hL'c Kc hKc

set_option maxHeartbeats 1000000 in
/-- **The compact part.** If the band integrals of the derivatives of `e` are at most `A` times
that of `e`, the integral of `|e|²` over a compact set is at most a quarter of the band
integral plus a constant times the squares of finitely many local averages. -/
theorem exists_compact_part [MeasurableSpace (AdelicGL F n)] [BorelSpace (AdelicGL F n)]
    (hn : n ≠ 0) (χ : IdeleClassGroup (𝓞 F) F →ₜ* ℂˣ) (hχ : ∀ x, ‖(χ x : ℂ)‖ = 1)
    (hSχ : S.HasCentralCharacter χ) (L : OpenSubgroup (FiniteAdelicGL F n))
    {Kc : Set (AdelicGL F n)} (hKc : IsCompact Kc) (A : ℝ≥0∞) (hA : A ≠ ⊤) :
    ∃ (U : Set (AdelicGL F n)) (P : Finset (AdelicGL F n)) (Cn : ℝ≥0∞), IsCompact U ∧
      matrixHaarMeasure F n U ≠ 0 ∧ ∀ e : S.Space, (∀ l ∈ L, S.finiteRepresentation l e = e) →
        ∑ k, bandNorm S (basisDerivative S k e) ≤ A * bandNorm S e →
        ∫⁻ g in Kc, ‖evaluate F n (S.toContinuous e) g‖ₑ ^ 2 ∂matrixHaarMeasure F n ≤
          ENNReal.ofReal (1 / 4) * bandNorm S e +
            Cn * ∑ p ∈ P, ‖average (matrixHaarMeasure F n) U
              (evaluate F n (S.toContinuous e)) p‖ₑ ^ 2 := by
  obtain ⟨L', hL'L, hL'c⟩ := OperatorRealization.exists_compact_openSubgroup_le L
  obtain ⟨K₃, hK₃, hest⟩ := exists_compact_estimate_matrix L' hL'c Kc hKc
  obtain ⟨C₃, hC₃top, hC₃⟩ := exists_lintegral_compact_le S hn χ hχ hSχ hK₃
  obtain ⟨ε, hε, hεsmall⟩ := exists_eps_small (C₃ * A) (ENNReal.mul_ne_top hC₃top hA)
  obtain ⟨U, P, Cn, hU, hU0, -, hmain⟩ := hest ε hε
  refine ⟨U, P, Cn, hU, hU0, fun e he hder => ?_⟩
  have hcpt := hmain (evaluate F n (S.toContinuous e))
    (fun k => evaluate F n (S.toContinuous (basisDerivative S k e)))
    (continuous_evaluate F n _) (fun k => continuous_evaluate F n _)
    (fun g l hl => (OperatorRealization.evaluate_finiteRepresentation S l e g).symm.trans
      (congrArg (fun v => evaluate F n (S.toContinuous v) g) (he l (hL'L hl))))
    (fun y => slice_data_one S e y)
  refine hcpt.trans (add_le_add ?_ le_rfl)
  have hK3 : ∑ k, ∫⁻ g in K₃, ‖evaluate F n (S.toContinuous (basisDerivative S k e)) g‖ₑ ^ 2
      ∂matrixHaarMeasure F n ≤ C₃ * (A * bandNorm S e) := by
    refine (Finset.sum_le_sum fun k _ => hC₃ _).trans ?_
    rw [← Finset.mul_sum]
    exact mul_le_mul' le_rfl hder
  calc ENNReal.ofReal ε * ∑ k, ∫⁻ g in K₃,
        ‖evaluate F n (S.toContinuous (basisDerivative S k e)) g‖ₑ ^ 2 ∂matrixHaarMeasure F n
      ≤ ENNReal.ofReal ε * (C₃ * (A * bandNorm S e)) := mul_le_mul' le_rfl hK3
    _ = ENNReal.ofReal ε * (C₃ * A) * bandNorm S e := by ring
    _ ≤ ENNReal.ofReal (1 / 4) * bandNorm S e := mul_le_mul' hεsmall le_rfl

set_option maxHeartbeats 1000000 in
/-- **The cusp part.** If the band integrals of the derivatives of `e` are at most `A` times
that of `e`, then for `T` large the integrals of `|e|²` over the cusp regions add up to at most
a quarter of the band integral. -/
theorem exists_cusp_part [CompactSpace (AdeleQuotient F)]
    [MeasurableSpace (AdelicGL F n)] [BorelSpace (AdelicGL F n)]
    (hSF : PrimitiveAdelicHeight.SiegelSetGLFinitenessStatement.{uF}) (hS : S.IsCuspidal)
    (L : OpenSubgroup (FiniteAdelicGL F n))
    {ΩN : Set (Matrix (Fin n) (Fin n) (Adeles F))} {C : Set (Ideles F)} {c : ℝ}
    (hΩ : IsCompact ΩN) (hΩN : ∀ N ∈ ΩN, PrimitiveAdelicHeight.IsUnitriangular N)
    (hC : IsCompact C) (hC1 : C ⊆ NormOneIdeleClass.normOneIdeles F) (hc : 0 < c)
    {Q₁ : Set (AdelicGL F n)} (hQ₁ : IsCompact Q₁) {K : ℝ} (hK : 0 ≤ K)
    (A : ℝ≥0∞) (hA : A ≠ ⊤) :
    ∃ T : ℝ, 0 ≤ T ∧ ∀ e : S.Space, (∀ l ∈ L, S.finiteRepresentation l e = e) →
      ∑ k, bandNorm S (basisDerivative S k e) ≤ A * bandNorm S e →
      ∑ a : {a : Fin n // 0 < a.val}, ∫⁻ g in cuspRegion ΩN C c Q₁ K a.val T,
        ‖evaluate F n (S.toContinuous e) g‖ₑ ^ 2 ∂matrixHaarMeasure F n ≤
          ENNReal.ofReal (1 / 4) * bandNorm S e := by
  have hcusp : ∀ a : {a : Fin n // 0 < a.val}, ∃ c₁ : ℝ≥0∞, c₁ ≠ ⊤ ∧ ∀ T : ℝ,
      2 * n * K ≤ T → ∀ e : S.Space, (∀ l ∈ L, S.finiteRepresentation l e = e) →
      ∫⁻ g in cuspRegion ΩN C c Q₁ K a.val T, ‖evaluate F n (S.toContinuous e) g‖ₑ ^ 2
          ∂matrixHaarMeasure F n ≤
        ENNReal.ofReal (Real.exp (-(T - 2 * n * K)) ^ 2) * c₁ *
          ∑ k, bandNorm S (basisDerivative S k e) := fun a =>
    exists_cuspRegion_le S hSF hS L.toSubgroup L.isOpen hΩ hΩN hC hC1 hc hQ₁ hK a.val a.property
  choose c₁ hc₁top hc₁ using hcusp
  have hc₁tot : ∑ a, c₁ a ≠ ⊤ := ENNReal.sum_ne_top.mpr fun a _ => hc₁top a
  obtain ⟨T, hT0, hTK, hTsmall⟩ := exists_exp_small ((∑ a, c₁ a) * A)
    (ENNReal.mul_ne_top hc₁tot hA) (2 * n * K) (by positivity)
  refine ⟨T, hT0, fun e he hder => ?_⟩
  calc _ ≤ ∑ a : {a : Fin n // 0 < a.val}, ENNReal.ofReal (Real.exp (-(T - 2 * n * K)) ^ 2) *
          c₁ a * ∑ k, bandNorm S (basisDerivative S k e) :=
        Finset.sum_le_sum fun a _ => hc₁ a T hTK e he
    _ = ENNReal.ofReal (Real.exp (-(T - 2 * n * K)) ^ 2) * (∑ a, c₁ a) *
          ∑ k, bandNorm S (basisDerivative S k e) := by
        rw [← Finset.sum_mul, ← Finset.mul_sum]
    _ ≤ ENNReal.ofReal (Real.exp (-(T - 2 * n * K)) ^ 2) * (∑ a, c₁ a) *
          (A * bandNorm S e) := mul_le_mul' le_rfl hder
    _ = ENNReal.ofReal (Real.exp (-(T - 2 * n * K)) ^ 2) * ((∑ a, c₁ a) * A) *
          bandNorm S e := by ring
    _ ≤ ENNReal.ofReal (1 / 4) * bandNorm S e := mul_le_mul' hTsmall le_rfl

/-- **Covering.** The band integral of `|e|²` is at most its integral over the part of a
covering Siegel set lying over the band. -/
theorem bandNorm_le_siegel [MeasurableSpace (AdelicGL F n)] [BorelSpace (AdelicGL F n)]
    {ΩN : Set (Matrix (Fin n) (Fin n) (Adeles F))} {C : Set (Ideles F)} {c : ℝ}
    (hΩ : IsCompact ΩN) (hΩN : ∀ N ∈ ΩN, PrimitiveAdelicHeight.IsUnitriangular N)
    (hC : IsCompact C)
    (hcov : ∀ g : AdelicGL F n, ∃ γ : RationalGL F n,
      AdelicGL.rational F n γ * g ∈ PrimitiveAdelicHeight.siegelSetGL F n ΩN C c)
    (e : S.Space) :
    bandNorm S e ≤ ∫⁻ g in PrimitiveAdelicHeight.siegelSetGL F n ΩN C c ∩
      point F n ⁻¹' band F n, ‖evaluate F n (S.toContinuous e) g‖ₑ ^ 2 ∂matrixHaarMeasure F n := by
  have ht0 : MeasurableSet (PrimitiveAdelicHeight.siegelSetGL F n ΩN C c ∩
      point F n ⁻¹' band F n) :=
    (measurableSet_siegelSetGL F n ΩN C c hΩ hΩN hC).inter
      ((continuous_point F n).measurable (measurableSet_band F n))
  have h := lintegral_quotient_le_cover F n (band F n) (measurableSet_band F n) _ ht0
    (fun x hx => by
      obtain ⟨γ, hγ⟩ := hcov x
      exact ⟨γ, hγ, point_rational_mul_mem_band γ hx⟩)
    (fun q => ‖toQuotient F n S e q‖ₑ ^ 2)
    ((toQuotient F n S e).continuous.measurable.enorm.pow_const 2)
  refine h.trans (le_of_eq (lintegral_congr fun g => ?_))
  rw [toQuotient_point]

set_option maxHeartbeats 1000000 in
/-- **Separation.** For a unitary form whose square norm is the band integral of `|f|²`,
finitely many local averages separate the `L`-invariant vectors with energy at most `C` times
their square norm. -/
theorem separating_of_bandNorm [CompactSpace (AdeleQuotient F)]
    [MeasurableSpace (AdelicGL F n)] [BorelSpace (AdelicGL F n)]
    (hSF : PrimitiveAdelicHeight.SiegelSetGLFinitenessStatement.{uF})
    (hn : n ≠ 0) (hS : S.IsCuspidal) (χ : IdeleClassGroup (𝓞 F) F →ₜ* ℂˣ)
    (hχ : ∀ x, ‖(χ x : ℂ)‖ = 1) (hSχ : S.HasCentralCharacter χ) (b : S.UnitaryForm)
    (hb : ∀ f, bandNorm S f = ENNReal.ofReal (b.inner f f).re)
    (L : OpenSubgroup (FiniteAdelicGL F n)) (C : ℝ) :
    ∃ (P : ℕ) (lam : Fin P → S.Space →ₗ[ℂ] ℂ), ∀ e : S.Space,
      (∀ l ∈ L, S.finiteRepresentation l e = e) →
      energy b e ≤ C * (b.inner e e).re → (∀ p, lam p e = 0) → e = 0 := by
  -- the derivative constant
  obtain ⟨CD, hCD, hCDdef⟩ : ∃ CD : ℝ, 0 ≤ CD ∧
      CD = ∑ k, ∑ i, cartanCoord (F := F) (n := n) k i ^ 2 :=
    ⟨_, Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _, rfl⟩
  have hC' : 0 ≤ max C 0 := le_max_right _ _
  have hder : ∀ e : S.Space, energy b e ≤ C * (b.inner e e).re →
      ∑ k, bandNorm S (basisDerivative S k e) ≤
        ENNReal.ofReal (CD * max C 0) * bandNorm S e := by
    intro e he
    refine (sum_bandNorm_basisDerivative_le_of S b hb e).trans ?_
    rw [← hCDdef, hb e, ← ENNReal.ofReal_mul (mul_nonneg hCD hC')]
    refine ENNReal.ofReal_le_ofReal ?_
    have hre : 0 ≤ (b.inner e e).re := b.finiteForm.toInnerProductCore.re_inner_nonneg e
    have h1 : energy b e ≤ max C 0 * (b.inner e e).re :=
      he.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hre)
    calc CD * energy b e ≤ CD * (max C 0 * (b.inner e e).re) :=
          mul_le_mul_of_nonneg_left h1 hCD
      _ = CD * max C 0 * (b.inner e e).re := by ring
  -- Siegel data and the split
  obtain ⟨ΩN, Cid, c, hΩ, hΩN, hC, hC1, hc, hcov⟩ :=
    PrimitiveAdelicHeight.exists_rational_mul_mem_siegelSetGL F n
  obtain ⟨Q₁, K, hQ₁, hK, hform⟩ := exists_torus_form F n ΩN Cid c hΩ hΩN hC hc
  obtain ⟨R, hsplit⟩ := exists_siegel_band_split hQ₁ hK hform
  obtain ⟨T, hT0, hcusp⟩ := exists_cusp_part S hSF hS L hΩ hΩN hC hC1 hc hQ₁ hK
    (ENNReal.ofReal (CD * max C 0)) ENNReal.ofReal_ne_top
  obtain ⟨U, P, Cn, hU, hU0, hcpt⟩ := exists_compact_part S hn χ hχ hSχ L
    (isCompact_compactRegion hQ₁ (R + n * (n * (K + T)))) (ENNReal.ofReal (CD * max C 0))
    ENNReal.ofReal_ne_top
  refine ⟨P.card, fun i => averageFunctional S hU hU0 ((P.equivFin.symm i : P) : AdelicGL F n),
    fun e he hen hlam => ?_⟩
  -- the averages vanish
  have hav : ∑ p ∈ P, ‖average (matrixHaarMeasure F n) U (evaluate F n (S.toContinuous e)) p‖ₑ ^ 2
      = 0 := by
    refine Finset.sum_eq_zero fun p hp => ?_
    have hpi : ((P.equivFin.symm (P.equivFin ⟨p, hp⟩) : P) : AdelicGL F n) = p := by
      rw [Equiv.symm_apply_apply]
    have h1 : averageFunctional S hU hU0 p e = 0 := hpi ▸ hlam (P.equivFin ⟨p, hp⟩)
    have h2 : average (matrixHaarMeasure F n) U (evaluate F n (S.toContinuous e)) p = 0 := h1
    rw [h2, enorm_zero, zero_pow two_ne_zero]
  have hre : 0 ≤ (b.inner e e).re := b.finiteForm.toInnerProductCore.re_inner_nonneg e
  have hdere := hder e hen
  -- the split of the Siegel integral
  have hsub : PrimitiveAdelicHeight.siegelSetGL F n ΩN Cid c ∩ point F n ⁻¹' band F n ⊆
      compactRegion Q₁ (R + n * (n * (K + T))) ∪
        ⋃ a : {a : Fin n // 0 < a.val}, cuspRegion ΩN Cid c Q₁ K a.val T := by
    rintro g ⟨hg, hgb⟩
    rcases hsplit T hT0 g hg hgb with h | ⟨a, ha, h⟩
    · exact Or.inl h
    · exact Or.inr (Set.mem_iUnion.mpr ⟨⟨a, ha⟩, h⟩)
  have hcptX := hcpt e he hdere
  rw [hav, mul_zero, add_zero] at hcptX
  have htot : bandNorm S e ≤
      ENNReal.ofReal (1 / 4) * bandNorm S e + ENNReal.ofReal (1 / 4) * bandNorm S e :=
    (bandNorm_le_siegel S hΩ hΩN hC hcov e).trans
      ((setLIntegral_le_add_sum (matrixHaarMeasure F n)
        (fun g => ‖evaluate F n (S.toContinuous e) g‖ₑ ^ 2) hsub).trans
        (add_le_add hcptX (hcusp e he hdere)))
  rw [hb e] at htot
  exact eq_zero_of_re_inner_self_le_zero_core b.finiteForm.toInnerProductCore
    (nonpos_of_le_two_quarters hre htot)

end Langlands.Automorphic.CuspidalAdmissible
