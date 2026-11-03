import Langlands.Geometry.Analytic.GeneralizedAffinoid.RelativeLaurentScalarExtension
import Langlands.Geometry.Analytic.GeneralizedAffinoid.RelativeUnitAnnulusNormalFormProof

/-! # A contractive coefficient retraction for every relative Laurent radius -/

noncomputable section

universe u

namespace Langlands.Analytic.RelativeLaurentAnnulus

open PresentedAffinoidAlgebra GeneralizedTateAlgebra Filter

variable (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  (A : PresentedAffinoidAlgebra K) (t : ℝ) [Fact (0 < t)]

namespace ConstantCoefficient

open PresentedAffinoidAlgebra.RelativeUnitAnnulus.NormalForm

local notation "𝕋" => GeneralizedTateAlgebra (LaurentAnnulus.radii t) A

/-- Every monomial on the constant Laurent diagonal has weight one. -/
theorem weight_eq_one {d : Fin 2 →₀ ℕ} (hd : degree d = 0) :
    (LaurentAnnulus.radii t).weight d = 1 := by
  have he : d 0 = d 1 := by
    unfold degree at hd
    omega
  unfold PositivePolyradius.weight
  rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fin.prod_univ_two]
  change t ^ d 0 * (t⁻¹) ^ d 1 = 1
  rw [he, ← mul_pow, mul_inv_cancel₀ (ne_of_gt (Fact.out : 0 < t)), one_pow]

/-- The constant Laurent coefficient, computed on relative weighted series. -/
def series (f : 𝕋) : A :=
  ∑' d, if degree d = 0 then MvPowerSeries.coeff d (GeneralizedTateAlgebra.series _ A f)
    else 0

theorem summable (f : 𝕋) :
    Summable fun d => if degree d = 0 then
      MvPowerSeries.coeff d (GeneralizedTateAlgebra.series _ A f) else 0 := by
  apply NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  refine squeeze_zero (fun _ => norm_nonneg _) (fun d => ?_) f.property
  split_ifs with hd
  · change ‖MvPowerSeries.coeff d (GeneralizedTateAlgebra.series _ A f)‖ ≤
      ‖MvPowerSeries.coeff d (GeneralizedTateAlgebra.series _ A f)‖ *
        (LaurentAnnulus.radii t).weight d
    rw [weight_eq_one t hd, mul_one]
  · simp only [norm_zero]
    exact mul_nonneg
      (norm_nonneg (MvPowerSeries.coeff d (GeneralizedTateAlgebra.series _ A f)))
      ((LaurentAnnulus.radii t).weight_pos d).le

omit [CompleteSpace K] in
theorem norm_series_le (f : 𝕋) : ‖series K A t f‖ ≤ ‖f‖ :=
  IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (norm_nonneg f) fun d => by
    split_ifs with hd
    · simpa only [weight_eq_one t hd, mul_one] using
        weighted_norm_coeff_le (LaurentAnnulus.radii t) A f d
    · simp

theorem series_add (f g : 𝕋) :
    series K A t (f + g) = series K A t f + series K A t g := by
  unfold series
  rw [← (summable K A t f).tsum_add (summable K A t g)]
  apply tsum_congr
  intro d
  change (if degree d = 0 then MvPowerSeries.coeff d
    (GeneralizedTateAlgebra.series _ A f + GeneralizedTateAlgebra.series _ A g) else 0) = _
  rw [map_add]
  split_ifs <;> simp

/-- The bounded additive functional before passing to the closed quotient. -/
def seriesHom : 𝕋 →+ A :=
  AddMonoidHom.mk' (series K A t) (series_add K A t)

theorem continuous_series : Continuous (series K A t) :=
  AddMonoidHomClass.continuous_of_bound (seriesHom K A t) 1 fun f => by
    rw [one_mul]
    exact norm_series_le K A t f

theorem series_sub (f g : 𝕋) :
    series K A t (f - g) = series K A t f - series K A t g :=
  map_sub (seriesHom K A t) f g

omit [CompleteSpace K] in
theorem series_monomial (d : Fin 2 →₀ ℕ) (a : A) :
    series K A t (monomial _ A d a) = if degree d = 0 then a else 0 := by
  unfold series
  rw [tsum_eq_single d]
  · simp
  · intro e he
    simp [coeff_monomial, Ne.symm he]

omit [CompleteSpace K] in
theorem series_constant (a : A) :
    series K A t (constantAlgHom (LaurentAnnulus.radii t) K A a) = a := by
  change series K A t (monomial _ A 0 a) = a
  simp [series_monomial, degree]

/-- Multiplication by the inverse equation leaves every Laurent degree unchanged. -/
theorem series_mul_relation (h : 𝕋) :
    series K A t (h * (X (LaurentAnnulus.radii t) A 0 *
      X (LaurentAnnulus.radii t) A 1 - 1)) = 0 := by
  refine eq_of_monomial
    (fun h : 𝕋 => series K A t (h * (X (LaurentAnnulus.radii t) A 0 *
      X (LaurentAnnulus.radii t) A 1 - 1)))
    (fun _ => (0 : A)) (fun f g => by rw [add_mul, series_add])
    (fun _ _ => (add_zero 0).symm)
    ((continuous_series K A t).comp (continuous_id.mul continuous_const))
    continuous_const (fun d a => ?_) h
  rw [mul_sub, mul_one, X, X, monomial_mul_monomial, monomial_mul_monomial,
    mul_one, mul_one, series_sub, series_monomial, series_monomial]
  have hdeg : degree (d + (Finsupp.single 0 1 + Finsupp.single 1 1)) = degree d := by
    simp [degree]
  rw [hdeg, sub_self]

theorem relativeEquationRelations_eq :
    Adjoin.relativeEquationRelations K A (LaurentAnnulus.radii t) {relation K A t} =
      {X (LaurentAnnulus.radii t) A 0 * X (LaurentAnnulus.radii t) A 1 - 1} := by
  rw [Adjoin.relativeEquationRelations, Set.image_singleton]
  congr 1
  simp only [relation, map_sub, map_mul, map_one, Adjoin.relativeSeriesEvaluation_X,
    Adjoin.relativeSeriesTuple_natAdd]

/-- Continuity makes the functional vanish on the entire closed relation ideal. -/
theorem series_ideal {f : 𝕋}
    (hf : f ∈ RelativeRelations.ideal K A (LaurentAnnulus.radii t)
      (Adjoin.relativeEquationRelations K A (LaurentAnnulus.radii t) {relation K A t})) :
    series K A t f = 0 := by
  rw [RelativeRelations.ideal, relativeEquationRelations_eq] at hf
  have hclosed : IsClosed {f : 𝕋 | series K A t f = 0} :=
    isClosed_eq (continuous_series K A t) continuous_const
  apply closure_minimal (t := {f : 𝕋 | series K A t f = 0}) ?_ hclosed hf
  intro f hf
  rw [SetLike.mem_coe, Ideal.mem_span_singleton'] at hf
  obtain ⟨h, rfl⟩ := hf
  exact series_mul_relation K A t h

/-- The additive functional on the actual relative closed-equation quotient. -/
def relative :
    Adjoin.relativeEquationAlgebra K A (LaurentAnnulus.radii t) {relation K A t} →+ A :=
  QuotientAddGroup.lift
    (RelativeRelations.ideal K A (LaurentAnnulus.radii t)
      (Adjoin.relativeEquationRelations K A (LaurentAnnulus.radii t)
        {relation K A t})).toAddSubgroup
    (seriesHom K A t) (fun f hf => by
      rw [AddMonoidHom.mem_ker]
      exact series_ideal K A t hf)

@[simp]
theorem relative_quotientMap (f : 𝕋) :
    relative K A t
      (RelativeRelations.quotientMap K A (LaurentAnnulus.radii t)
        (Adjoin.relativeEquationRelations K A (LaurentAnnulus.radii t)
          {relation K A t}) f) = series K A t f := rfl

theorem norm_relative_le (b :
    Adjoin.relativeEquationAlgebra K A (LaurentAnnulus.radii t) {relation K A t}) :
    ‖relative K A t b‖ ≤ ‖b‖ := by
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨f, rfl, hf⟩ := RelativeRelations.exists_representative_norm_lt K A
    (LaurentAnnulus.radii t)
    (Adjoin.relativeEquationRelations K A (LaurentAnnulus.radii t) {relation K A t}) b hε
  exact (norm_series_le K A t f).trans hf.le

end ConstantCoefficient

/-- Constant Laurent coefficient on the actual enlarged scalar quotient. -/
def retraction : algebra K A t →+ A :=
  (ConstantCoefficient.relative K A t).comp
    (Adjoin.relativeEquationMap K A (LaurentAnnulus.radii t)
      {relation K A t}).toAlgHom.toRingHom.toAddMonoidHom

theorem norm_retraction_le (b : algebra K A t) : ‖retraction K A t b‖ ≤ ‖b‖ :=
  (ConstantCoefficient.norm_relative_le K A t _).trans
    (Adjoin.norm_relativeEquationMap_le K A (LaurentAnnulus.radii t)
      {relation K A t} b)

theorem continuous_retraction : Continuous (retraction K A t) :=
  AddMonoidHomClass.continuous_of_bound (retraction K A t) 1 fun b => by
    rw [one_mul]
    exact norm_retraction_le K A t b

@[simp]
theorem retraction_baseMap (a : A) : retraction K A t (baseMap K A t a) = a := by
  change ConstantCoefficient.relative K A t
    (Adjoin.relativeEquationMap K A (LaurentAnnulus.radii t) {relation K A t}
      (Adjoin.baseMap K A (LaurentAnnulus.radii t) {relation K A t} a)) = a
  rw [Adjoin.relativeEquationMap_baseMap]
  exact ConstantCoefficient.series_constant K A t a

/-- The original algebra embeds isometrically even for trivial scalar valuations. -/
theorem norm_baseMap (a : A) : ‖baseMap K A t a‖ = ‖a‖ := by
  apply le_antisymm
  · exact Adjoin.norm_baseMap_le K A (LaurentAnnulus.radii t) {relation K A t} a
  · have h := norm_retraction_le K A t (baseMap K A t a)
    rw [retraction_baseMap] at h
    exact h

theorem isometry_baseMap : Isometry (baseMap K A t) :=
  AddMonoidHomClass.isometry_of_norm (baseMap K A t).toAlgHom (norm_baseMap K A t)

end Langlands.Analytic.RelativeLaurentAnnulus
