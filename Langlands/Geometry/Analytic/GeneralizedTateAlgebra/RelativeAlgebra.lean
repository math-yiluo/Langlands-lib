import Langlands.Geometry.Analytic.GeneralizedTateAlgebra.CoefficientMap
import Langlands.Geometry.Analytic.Affinoid

/-! # Scalar-compatible relative weighted restricted series -/

noncomputable section

universe u v w z

namespace Langlands.Analytic.GeneralizedTateAlgebra

variable {σ : Type u} (r : PositivePolyradius σ)
  (R : Type v) [CommSemiring R]
  (A : Type w) [NormedCommRing A] [IsUltrametricDist A] [Algebra R A]

/-- Relative series inherit the base algebra structure through the actual
coefficient subalgebra. -/
instance (priority := 500) instAlgebraOfAlgebra : Algebra R (GeneralizedTateAlgebra r A) :=
  inferInstanceAs (Algebra R ↥(weightedRestrictedSubalgebra r A))

instance instIsScalarTower : IsScalarTower R A (GeneralizedTateAlgebra r A) :=
  inferInstanceAs (IsScalarTower R A ↥(weightedRestrictedSubalgebra r A))

@[simp] theorem series_smul (c : R) (f : GeneralizedTateAlgebra r A) :
    series r A (c • f) = c • series r A f := rfl

@[simp] theorem series_algebraMap (c : R) :
    series r A (algebraMap R (GeneralizedTateAlgebra r A) c) =
      MvPowerSeries.C (algebraMap R A c) := by
  exact MvPowerSeries.algebraMap_apply

section Normed

variable (K : Type v) [NormedField K]
  (B : Type w) [NormedCommRing B] [IsUltrametricDist B] [NormedAlgebra K B]

/-- The weighted coefficient norm makes relative series a normed algebra over
the coefficient ring's normed base field. -/
instance (priority := 500) instNormedAlgebraOfNormedAlgebra :
    NormedAlgebra K (GeneralizedTateAlgebra r B) where
  toAlgebra := instAlgebraOfAlgebra r K B
  norm_smul_le c f := by
    apply (norm_le_iff r B _ (mul_nonneg (norm_nonneg c) (norm_nonneg f))).mpr
    intro d
    change ‖c • MvPowerSeries.coeff d (series r B f)‖ * r.weight d ≤ _
    calc
      ‖c • MvPowerSeries.coeff d (series r B f)‖ * r.weight d
          ≤ (‖c‖ * ‖MvPowerSeries.coeff d (series r B f)‖) * r.weight d :=
        mul_le_mul_of_nonneg_right (norm_smul_le _ _) (r.weight_pos d).le
      _ = ‖c‖ * (‖MvPowerSeries.coeff d (series r B f)‖ * r.weight d) := mul_assoc _ _ _
      _ ≤ ‖c‖ * ‖f‖ := mul_le_mul_of_nonneg_left
        (weighted_norm_coeff_le r B f d) (norm_nonneg c)

end Normed

section BoundedAlgebraMaps

variable (K : Type v) [NormedField K]
  (B : Type w) [NormedCommRing B] [IsUltrametricDist B] [Algebra K B]

/-- The coefficient inclusion as an actual bounded algebra map over the base field. -/
def constantAlgHom : BoundedAlgHom K B (GeneralizedTateAlgebra r B) where
  toAlgHom := IsScalarTower.toAlgHom K B (GeneralizedTateAlgebra r B)
  bounded := ⟨1, zero_lt_one, fun b => by
    change ‖algebraMap B (GeneralizedTateAlgebra r B) b‖ ≤ 1 * ‖b‖
    rw [norm_algebraMap, one_mul]⟩

@[simp] theorem constantAlgHom_apply (b : B) :
    constantAlgHom r K B b = algebraMap B (GeneralizedTateAlgebra r B) b := rfl

@[simp] theorem norm_constantAlgHom (b : B) : ‖constantAlgHom r K B b‖ = ‖b‖ :=
  norm_algebraMap r B b

theorem isometry_constantAlgHom : Isometry (constantAlgHom r K B) :=
  AddMonoidHomClass.isometry_of_norm (constantAlgHom r K B).toAlgHom
    (norm_constantAlgHom r K B)

variable {K B} {D : Type z} [NormedCommRing D] [IsUltrametricDist D] [Algebra K D]

/-- A bounded map of coefficient algebras induces a bounded map of relative
weighted series algebras over the same base. -/
def mapCoefficientsAlgHom (φ : BoundedAlgHom K B D) :
    BoundedAlgHom K (GeneralizedTateAlgebra r B) (GeneralizedTateAlgebra r D) where
  toAlgHom :=
    { toRingHom := (mapCoefficients r φ.toBoundedRingHom).toRingHom
      commutes' := by
        intro c
        apply Subtype.ext
        change series r D (mapCoefficients r φ.toBoundedRingHom
          (algebraMap K (GeneralizedTateAlgebra r B) c)) =
            series r D (algebraMap K (GeneralizedTateAlgebra r D) c)
        rw [series_mapCoefficients, series_algebraMap, series_algebraMap,
          MvPowerSeries.map_C]
        exact congrArg MvPowerSeries.C (φ.toAlgHom.commutes c) }
  bounded := (mapCoefficients r φ.toBoundedRingHom).bounded

@[simp] theorem mapCoefficientsAlgHom_apply (φ : BoundedAlgHom K B D)
    (f : GeneralizedTateAlgebra r B) :
    mapCoefficientsAlgHom r φ f = mapCoefficients r φ.toBoundedRingHom f := rfl

theorem norm_mapCoefficientsAlgHom_le (φ : BoundedAlgHom K B D) {C : ℝ}
    (hC : 0 ≤ C) (hφ : ∀ b, ‖φ b‖ ≤ C * ‖b‖) (f : GeneralizedTateAlgebra r B) :
    ‖mapCoefficientsAlgHom r φ f‖ ≤ C * ‖f‖ :=
  norm_mapCoefficients_le r φ.toBoundedRingHom hC hφ f

@[simp] theorem mapCoefficientsAlgHom_id :
    mapCoefficientsAlgHom r (BoundedAlgHom.id K B) =
      BoundedAlgHom.id K (GeneralizedTateAlgebra r B) := by
  apply BoundedAlgHom.ext
  intro f
  apply Subtype.ext
  rfl

@[simp] theorem mapCoefficientsAlgHom_comp {E : Type*} [NormedCommRing E]
    [IsUltrametricDist E] [Algebra K E]
    (ψ : BoundedAlgHom K D E) (φ : BoundedAlgHom K B D) :
    mapCoefficientsAlgHom r (ψ.comp φ) =
      (mapCoefficientsAlgHom r ψ).comp (mapCoefficientsAlgHom r φ) := by
  apply BoundedAlgHom.ext
  intro f
  apply Subtype.ext
  rfl

/-- The coefficient inclusion is natural in bounded coefficient algebra maps. -/
theorem mapCoefficientsAlgHom_constantAlgHom (φ : BoundedAlgHom K B D) :
    (mapCoefficientsAlgHom r φ).comp (constantAlgHom r K B) =
      (constantAlgHom r K D).comp φ := by
  apply BoundedAlgHom.ext
  intro b
  exact mapCoefficients_algebraMap r φ.toBoundedRingHom b

end BoundedAlgebraMaps

end Langlands.Analytic.GeneralizedTateAlgebra
