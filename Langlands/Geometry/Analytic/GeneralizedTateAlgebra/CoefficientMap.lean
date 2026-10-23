import Langlands.Geometry.Analytic.GeneralizedTateAlgebra.EvaluationDefinitions
import Langlands.Geometry.Analytic.Spectrum.Definitions

/-! # Bounded coefficient maps on weighted restricted series -/

noncomputable section

universe u v w z

namespace Langlands.Analytic.GeneralizedTateAlgebra

variable {σ : Type u} (r : PositivePolyradius σ)
  {A : Type v} {B : Type w} {D : Type z}
  [NormedCommRing A] [IsUltrametricDist A]
  [NormedCommRing B] [IsUltrametricDist B]
  [NormedCommRing D] [IsUltrametricDist D]

omit [IsUltrametricDist B] in
/-- A bounded coefficient homomorphism preserves weighted restrictedness. -/
theorem isRestricted_mapCoefficients (φ : BoundedRingHom A B)
    (f : GeneralizedTateAlgebra r A) :
    MvPowerSeries.IsRestricted r (MvPowerSeries.map φ.toRingHom (series r A f)) := by
  obtain ⟨C, hC, hφ⟩ := φ.bounded
  have hlim := f.property.const_mul C
  simp only [mul_zero] at hlim
  apply squeeze_zero
    (fun d => mul_nonneg (norm_nonneg _) (r.weight_pos d).le) _ hlim
  intro d
  change ‖φ.toRingHom (MvPowerSeries.coeff d f.val)‖ * r.weight d ≤
    C * (‖MvPowerSeries.coeff d f.val‖ * r.weight d)
  exact (mul_le_mul_of_nonneg_right (hφ _) (r.weight_pos d).le).trans_eq
    (mul_assoc _ _ _)

/-- Restrict the actual formal-series coefficient map to weighted restricted series. -/
def mapCoefficientsRingHom (φ : BoundedRingHom A B) :
    GeneralizedTateAlgebra r A →+* GeneralizedTateAlgebra r B :=
  ((MvPowerSeries.map φ.toRingHom).comp
    (weightedRestrictedSubalgebra r A).val.toRingHom).codRestrict
      (weightedRestrictedSubalgebra r B) (isRestricted_mapCoefficients r φ)

@[simp] theorem series_mapCoefficientsRingHom (φ : BoundedRingHom A B)
    (f : GeneralizedTateAlgebra r A) :
    series r B (mapCoefficientsRingHom r φ f) =
      MvPowerSeries.map φ.toRingHom (series r A f) := rfl

/-- Every nonnegative coefficient bound is also a bound on the weighted Gauss norm. -/
theorem norm_mapCoefficientsRingHom_le (φ : BoundedRingHom A B) {C : ℝ}
    (hC : 0 ≤ C) (hφ : ∀ a, ‖φ a‖ ≤ C * ‖a‖)
    (f : GeneralizedTateAlgebra r A) :
    ‖mapCoefficientsRingHom r φ f‖ ≤ C * ‖f‖ := by
  apply (norm_le_iff r B _ (mul_nonneg hC (norm_nonneg f))).mpr
  intro d
  rw [series_mapCoefficientsRingHom, MvPowerSeries.coeff_map]
  exact (mul_le_mul_of_nonneg_right (hφ _) (r.weight_pos d).le).trans
    ((mul_assoc _ _ _).le.trans
      (mul_le_mul_of_nonneg_left (weighted_norm_coeff_le r A f d) hC))

/-- The bounded homomorphism on actual weighted restricted series induced by a
bounded coefficient homomorphism. -/
def mapCoefficients (φ : BoundedRingHom A B) :
    BoundedRingHom (GeneralizedTateAlgebra r A) (GeneralizedTateAlgebra r B) where
  toRingHom := mapCoefficientsRingHom r φ
  bounded := by
    obtain ⟨C, hC, hφ⟩ := φ.bounded
    exact ⟨C, hC, norm_mapCoefficientsRingHom_le r φ hC.le hφ⟩

@[simp] theorem series_mapCoefficients (φ : BoundedRingHom A B)
    (f : GeneralizedTateAlgebra r A) :
    series r B (mapCoefficients r φ f) =
      MvPowerSeries.map φ.toRingHom (series r A f) :=
  series_mapCoefficientsRingHom r φ f

@[simp] theorem coeff_mapCoefficients (φ : BoundedRingHom A B)
    (f : GeneralizedTateAlgebra r A) (d : σ →₀ ℕ) :
    MvPowerSeries.coeff d (series r B (mapCoefficients r φ f)) =
      φ (MvPowerSeries.coeff d (series r A f)) := rfl

theorem norm_mapCoefficients_le (φ : BoundedRingHom A B) {C : ℝ}
    (hC : 0 ≤ C) (hφ : ∀ a, ‖φ a‖ ≤ C * ‖a‖)
    (f : GeneralizedTateAlgebra r A) :
    ‖mapCoefficients r φ f‖ ≤ C * ‖f‖ :=
  norm_mapCoefficientsRingHom_le r φ hC hφ f

@[simp] theorem mapCoefficients_id :
    mapCoefficients r (BoundedRingHom.id A) =
      BoundedRingHom.id (GeneralizedTateAlgebra r A) := by
  apply BoundedRingHom.ext
  intro f
  apply Subtype.ext
  rfl

@[simp] theorem mapCoefficients_comp (ψ : BoundedRingHom B D) (φ : BoundedRingHom A B) :
    mapCoefficients r (ψ.comp φ) =
      (mapCoefficients r ψ).comp (mapCoefficients r φ) := by
  apply BoundedRingHom.ext
  intro f
  apply Subtype.ext
  rfl

@[simp] theorem mapCoefficients_monomial (φ : BoundedRingHom A B)
    (d : σ →₀ ℕ) (a : A) :
    mapCoefficients r φ (monomial r A d a) = monomial r B d (φ a) := by
  apply Subtype.ext
  exact MvPowerSeries.map_monomial φ.toRingHom d a

@[simp] theorem mapCoefficients_algebraMap (φ : BoundedRingHom A B) (a : A) :
    mapCoefficients r φ (algebraMap A (GeneralizedTateAlgebra r A) a) =
      algebraMap B (GeneralizedTateAlgebra r B) (φ a) := by
  apply Subtype.ext
  exact MvPowerSeries.map_C φ.toRingHom a

@[simp] theorem mapCoefficients_X (φ : BoundedRingHom A B) (i : σ) :
    mapCoefficients r φ (X r A i) = X r B i := by
  simpa only [X, map_one] using mapCoefficients_monomial r φ (Finsupp.single i 1) 1

/-- Injectivity on coefficients gives injectivity on the actual restricted series. -/
theorem mapCoefficients_injective (φ : BoundedRingHom A B) (hφ : Function.Injective φ) :
    Function.Injective (mapCoefficients r φ) := by
  intro f g h
  apply Subtype.ext
  apply MvPowerSeries.ext
  intro d
  apply hφ
  exact congrArg (fun q => MvPowerSeries.coeff d (series r B q)) h

/-- A norm-preserving coefficient homomorphism preserves the weighted Gauss norm. -/
theorem norm_mapCoefficients (φ : BoundedRingHom A B) (hφ : ∀ a, ‖φ a‖ = ‖a‖)
    (f : GeneralizedTateAlgebra r A) : ‖mapCoefficients r φ f‖ = ‖f‖ := by
  apply le_antisymm
  · simpa only [one_mul] using
      norm_mapCoefficients_le r φ zero_le_one (fun a => (hφ a).le.trans_eq (one_mul _).symm) f
  · apply (norm_le_iff r A f (norm_nonneg _)).mpr
    intro d
    have h := weighted_norm_coeff_le r B (mapCoefficients r φ f) d
    simpa only [coeff_mapCoefficients, hφ] using h

/-- Isometric coefficient homomorphisms induce isometries of weighted series. -/
theorem isometry_mapCoefficients (φ : BoundedRingHom A B) (hφ : Isometry φ) :
    Isometry (mapCoefficients r φ) := by
  apply AddMonoidHomClass.isometry_of_norm (mapCoefficients r φ).toRingHom
  exact norm_mapCoefficients r φ (hφ.norm_map_of_map_zero (map_zero φ.toRingHom))

end Langlands.Analytic.GeneralizedTateAlgebra
