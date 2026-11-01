import Langlands.Representation.RankinSelberg.AdjacentRankCompactAverage
import Langlands.HarmonicAnalysis.RectangularTestSmooth
import Langlands.Representation.Induction.Definitions
import Mathlib.LinearAlgebra.TensorProduct.Basic

/-! Covariance and smoothness of the compact rectangular average. -/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Matrix

universe uF uV

variable {K : Type uF} [Field K] [TopologicalSpace K]
  [IsTopologicalDivisionRing K] [T2Space K] {n : ℕ}
  {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- The compact full-rank tests are stable under actual rectangular right translation. -/
def adjacentRankCompactTestTranslate (g : GeneralLinear (n + 1) K)
    (Φ : adjacentRankCompactTests n K) : adjacentRankCompactTests n K :=
  ⟨rectangularTranslate g Φ.val, adjacentRankCompactOrbit_translate Φ.val Φ.property g⟩

omit [T2Space K] in
@[simp] theorem adjacentRankCompactTestTranslate_apply
    (g : GeneralLinear (n + 1) K) (Φ : adjacentRankCompactTests n K)
    (M : Matrix (Fin n) (Fin (n + 1)) K) :
    (adjacentRankCompactTestTranslate g Φ).val M = Φ.val (M * g.val) := rfl

variable [MeasurableSpace (GeneralLinear n K)] [OpensMeasurableSpace (GeneralLinear n K)]

theorem adjacentRankCompactAverage_test_add
    (μ : Measure (GeneralLinear n K)) [IsFiniteMeasureOnCompacts μ]
    (ρ : Representation ℂ (GeneralLinear n K) V) (hρ : IsSmooth ρ)
    (ξ : GeneralLinear n K →* ℂˣ)
    (hξ : IsLocallyConstant (fun h => (ξ h : ℂ)))
    (Φ Ψ : adjacentRankCompactTests n K) (v : V) (g : GeneralLinear (n + 1) K) :
    adjacentRankCompactAverage μ ρ hρ ξ hξ (Φ + Ψ) v g =
      adjacentRankCompactAverage μ ρ hρ ξ hξ Φ v g +
        adjacentRankCompactAverage μ ρ hρ ξ hξ Ψ v g := by
  have he : adjacentRankCompactIntegrand ρ hρ ξ hξ (Φ + Ψ) v g =
      adjacentRankCompactIntegrand ρ hρ ξ hξ Φ v g +
        adjacentRankCompactIntegrand ρ hρ ξ hξ Ψ v g := by
    ext h
    simp [add_mul, add_smul]
  unfold adjacentRankCompactAverage
  rw [he, AlgebraicIntegral.integral_add _
    _ (adjacentRankCompactIntegrand_finMeasSupp μ ρ hρ ξ hξ Φ v g)
    (adjacentRankCompactIntegrand_finMeasSupp μ ρ hρ ξ hξ Ψ v g)]

theorem adjacentRankCompactAverage_test_smul
    (μ : Measure (GeneralLinear n K)) [IsFiniteMeasureOnCompacts μ]
    (ρ : Representation ℂ (GeneralLinear n K) V) (hρ : IsSmooth ρ)
    (ξ : GeneralLinear n K →* ℂˣ)
    (hξ : IsLocallyConstant (fun h => (ξ h : ℂ)))
    (Φ : adjacentRankCompactTests n K) (c : ℂ) (v : V) (g : GeneralLinear (n + 1) K) :
    adjacentRankCompactAverage μ ρ hρ ξ hξ (c • Φ) v g =
      c • adjacentRankCompactAverage μ ρ hρ ξ hξ Φ v g := by
  have he : adjacentRankCompactIntegrand ρ hρ ξ hξ (c • Φ) v g =
      c • adjacentRankCompactIntegrand ρ hρ ξ hξ Φ v g := by
    ext h
    simp [smul_smul, mul_assoc]
  unfold adjacentRankCompactAverage
  rw [he, AlgebraicIntegral.integral_smul c _
    (adjacentRankCompactIntegrand_finMeasSupp μ ρ hρ ξ hξ Φ v g)]

/-- The average depends bilinearly on its full-rank test and representation vector. -/
def adjacentRankCompactAverageLinear
    (μ : Measure (GeneralLinear n K)) [IsFiniteMeasureOnCompacts μ]
    (ρ : Representation ℂ (GeneralLinear n K) V) (hρ : IsSmooth ρ)
    (ξ : GeneralLinear n K →* ℂˣ)
    (hξ : IsLocallyConstant (fun h => (ξ h : ℂ))) :
    adjacentRankCompactTests n K →ₗ[ℂ] V →ₗ[ℂ] (GeneralLinear (n + 1) K → V) where
  toFun Φ :=
    { toFun := fun v g => adjacentRankCompactAverage μ ρ hρ ξ hξ Φ v g
      map_add' := fun v w => funext (adjacentRankCompactAverage_add μ ρ hρ ξ hξ Φ v w)
      map_smul' := fun c v => funext (adjacentRankCompactAverage_smul μ ρ hρ ξ hξ Φ c v) }
  map_add' Φ Ψ := LinearMap.ext fun v =>
    funext (adjacentRankCompactAverage_test_add μ ρ hρ ξ hξ Φ Ψ v)
  map_smul' c Φ := LinearMap.ext fun v =>
    funext (adjacentRankCompactAverage_test_smul μ ρ hρ ξ hξ Φ c v)

/-- Right multiplication in the ambient variable is right translation of the test. -/
theorem adjacentRankCompactAverage_right
    (μ : Measure (GeneralLinear n K)) [IsFiniteMeasureOnCompacts μ]
    (ρ : Representation ℂ (GeneralLinear n K) V) (hρ : IsSmooth ρ)
    (ξ : GeneralLinear n K →* ℂˣ)
    (hξ : IsLocallyConstant (fun h => (ξ h : ℂ)))
    (Φ : adjacentRankCompactTests n K) (v : V) (g k : GeneralLinear (n + 1) K) :
    adjacentRankCompactAverage μ ρ hρ ξ hξ Φ v (g * k) =
      adjacentRankCompactAverage μ ρ hρ ξ hξ (adjacentRankCompactTestTranslate k Φ) v g := by
  unfold adjacentRankCompactAverage
  congr 1
  ext h
  simp [Matrix.mul_assoc]

/-- The change of variables underlying lower-parabolic covariance. The sole
matrix hypothesis expresses `[h,0] p = [ha,0]`; the sole measure hypothesis
is the actual right-Haar invariance used in the substitution. -/
theorem adjacentRankCompactAverage_left
    (μ : Measure (GeneralLinear n K)) [IsFiniteMeasureOnCompacts μ]
    (ρ : Representation ℂ (GeneralLinear n K) V) (hρ : IsSmooth ρ)
    (ξ : GeneralLinear n K →* ℂˣ)
    (hξ : IsLocallyConstant (fun h => (ξ h : ℂ)))
    (Φ : adjacentRankCompactTests n K) (v : V)
    (p : GeneralLinear (n + 1) K) (a : GeneralLinear n K)
    (hmat : ∀ h : GeneralLinear n K,
      rectangularJoin h.val 0 * p.val = rectangularJoin (h * a).val 0)
    (hμ : MeasurePreserving (fun h : GeneralLinear n K => h * a) μ μ)
    (g : GeneralLinear (n + 1) K) :
    adjacentRankCompactAverage μ ρ hρ ξ hξ Φ v (p * g) =
      (ξ a⁻¹ : ℂ) • ρ a (adjacentRankCompactAverage μ ρ hρ ξ hξ Φ v g) := by
  let T : V →ₗ[ℂ] V := (ξ a⁻¹ : ℂ) • ρ a
  have he : adjacentRankCompactIntegrand ρ hρ ξ hξ Φ v (p * g) =
      ((adjacentRankCompactIntegrand ρ hρ ξ hξ Φ v g).map T).comp
        (fun h => h * a) hμ.measurable := by
    ext h
    have horbit : ρ a (ρ (h * a)⁻¹ v) = ρ h⁻¹ v := by
      rw [← Module.End.mul_apply, ← map_mul]
      simp [_root_.mul_inv_rev]
    change (Φ.val (rectangularJoin h.val 0 * (p * g).val) * (ξ h : ℂ)) • ρ h⁻¹ v =
      (ξ a⁻¹ : ℂ) • ρ a
        ((Φ.val (rectangularJoin (h * a).val 0 * g.val) * (ξ (h * a) : ℂ)) •
          ρ (h * a)⁻¹ v)
    rw [Units.val_mul, ← Matrix.mul_assoc, hmat, map_smul, horbit, smul_smul]
    congr 1
    simp [map_mul, mul_assoc, mul_comm]
  unfold adjacentRankCompactAverage
  rw [he, AlgebraicIntegral.integral_comp_measurePreserving _ _ hμ,
    AlgebraicIntegral.integral_linearMap _
      (adjacentRankCompactIntegrand_finMeasSupp μ ρ hρ ξ hξ Φ v g) T]
  rfl

/-- The actual vector-valued section formula, including its outer smooth character. -/
def adjacentRankCompactSectionValue
    (μ : Measure (GeneralLinear n K)) [IsFiniteMeasureOnCompacts μ]
    (ρ : Representation ℂ (GeneralLinear n K) V) (hρ : IsSmooth ρ)
    (ξ : GeneralLinear n K →* ℂˣ)
    (hξ : IsLocallyConstant (fun h => (ξ h : ℂ)))
    (θ : Induction.SmoothCharacter ℂ (GeneralLinear (n + 1) K))
    (Φ : adjacentRankCompactTests n K) (v : V) (g : GeneralLinear (n + 1) K) : V :=
  (θ.toMonoidHom g : ℂ) • adjacentRankCompactAverage μ ρ hρ ξ hξ Φ v g

theorem adjacentRankCompactSectionValue_right
    (μ : Measure (GeneralLinear n K)) [IsFiniteMeasureOnCompacts μ]
    (ρ : Representation ℂ (GeneralLinear n K) V) (hρ : IsSmooth ρ)
    (ξ : GeneralLinear n K →* ℂˣ)
    (hξ : IsLocallyConstant (fun h => (ξ h : ℂ)))
    (θ : Induction.SmoothCharacter ℂ (GeneralLinear (n + 1) K))
    (Φ : adjacentRankCompactTests n K) (v : V) (g k : GeneralLinear (n + 1) K) :
    adjacentRankCompactSectionValue μ ρ hρ ξ hξ θ Φ v (g * k) =
      (θ.toMonoidHom k : ℂ) • adjacentRankCompactSectionValue μ ρ hρ ξ hξ θ
        (adjacentRankCompactTestTranslate k Φ) v g := by
  simp only [adjacentRankCompactSectionValue, map_mul, Units.val_mul,
    adjacentRankCompactAverage_right, smul_smul]
  rw [mul_comm]

/-- One open right stabilizer fixes the entire weighted average. -/
theorem adjacentRankCompactSectionValue_smooth
    (μ : Measure (GeneralLinear n K)) [IsFiniteMeasureOnCompacts μ]
    (ρ : Representation ℂ (GeneralLinear n K) V) (hρ : IsSmooth ρ)
    (ξ : GeneralLinear n K →* ℂˣ)
    (hξ : IsLocallyConstant (fun h => (ξ h : ℂ)))
    (θ : Induction.SmoothCharacter ℂ (GeneralLinear (n + 1) K))
    (Φ : adjacentRankCompactTests n K) (v : V) :
    ∃ U : OpenSubgroup (GeneralLinear (n + 1) K),
      ∀ (k : U) (g : GeneralLinear (n + 1) K),
        adjacentRankCompactSectionValue μ ρ hρ ξ hξ θ Φ v (g * (k : GeneralLinear _ K)) =
          adjacentRankCompactSectionValue μ ρ hρ ξ hξ θ Φ v g := by
  obtain ⟨U, hU⟩ := rectangularTestSmooth Φ.val
  let T : OpenSubgroup (GeneralLinear (n + 1) K) :=
    ⟨θ.toMonoidHom.ker, θ.isOpen_ker⟩
  refine ⟨U ⊓ T, ?_⟩
  intro k g
  have ht : adjacentRankCompactTestTranslate k.val Φ = Φ := by
    apply Subtype.ext
    ext M
    exact hU k.val k.property.1 M
  have hk : θ.toMonoidHom k.val = 1 := k.property.2
  rw [adjacentRankCompactSectionValue_right, ht, hk, Units.val_one, one_smul]

/-- The inducing representation dictated by the weighted average's covariance. -/
def adjacentRankCompactSectionRepresentation
    (P : Subgroup (GeneralLinear (n + 1) K)) (a : P →* GeneralLinear n K)
    (ρ : Representation ℂ (GeneralLinear n K) V)
    (ξ : GeneralLinear n K →* ℂˣ)
    (θ : Induction.SmoothCharacter ℂ (GeneralLinear (n + 1) K)) :
    Representation ℂ P V :=
  Langlands.twist (θ.toMonoidHom.comp P.subtype * (ξ.comp a)⁻¹) (ρ.comp a)

/-- An actual smooth induced function, for every subgroup whose elements satisfy
the displayed lower-block matrix identity and preserve the integration measure. -/
def adjacentRankCompactSection
    (μ : Measure (GeneralLinear n K)) [IsFiniteMeasureOnCompacts μ]
    (ρ : Representation ℂ (GeneralLinear n K) V) (hρ : IsSmooth ρ)
    (ξ : GeneralLinear n K →* ℂˣ)
    (hξ : IsLocallyConstant (fun h => (ξ h : ℂ)))
    (θ : Induction.SmoothCharacter ℂ (GeneralLinear (n + 1) K))
    (P : Subgroup (GeneralLinear (n + 1) K)) (a : P →* GeneralLinear n K)
    (hmat : ∀ (p : P) (h : GeneralLinear n K),
      rectangularJoin h.val 0 * p.val.val = rectangularJoin (h * a p).val 0)
    (hμ : ∀ p : P, MeasurePreserving (fun h : GeneralLinear n K => h * a p) μ μ)
    (Φ : adjacentRankCompactTests n K) (v : V) :
    Induction.SmoothFunctions P (adjacentRankCompactSectionRepresentation P a ρ ξ θ) := by
  let hs := adjacentRankCompactSectionValue_smooth μ ρ hρ ξ hξ θ Φ v
  let U := Classical.choose hs
  have hU := Classical.choose_spec hs
  refine Induction.smoothFunctionOf P (adjacentRankCompactSectionRepresentation P a ρ ξ θ)
    (adjacentRankCompactSectionValue μ ρ hρ ξ hξ θ Φ v) ?_ U hU
  intro p g
  rw [adjacentRankCompactSectionValue, map_mul, Units.val_mul,
    adjacentRankCompactAverage_left μ ρ hρ ξ hξ Φ v p.val (a p) (hmat p) (hμ p) g]
  change ((θ.toMonoidHom p.val : ℂ) * (θ.toMonoidHom g : ℂ)) •
      ((ξ (a p)⁻¹ : ℂ) • ρ (a p) (adjacentRankCompactAverage μ ρ hρ ξ hξ Φ v g)) =
    (((θ.toMonoidHom p.val) * (ξ (a p))⁻¹ : ℂˣ) : ℂ) •
      ρ (a p) ((θ.toMonoidHom g : ℂ) •
        adjacentRankCompactAverage μ ρ hρ ξ hξ Φ v g)
  rw [map_smul]
  simp only [map_inv, Units.val_mul, smul_smul]
  congr 1
  ring

@[simp] theorem adjacentRankCompactSection_eval
    (μ : Measure (GeneralLinear n K)) [IsFiniteMeasureOnCompacts μ]
    (ρ : Representation ℂ (GeneralLinear n K) V) (hρ : IsSmooth ρ)
    (ξ : GeneralLinear n K →* ℂˣ)
    (hξ : IsLocallyConstant (fun h => (ξ h : ℂ)))
    (θ : Induction.SmoothCharacter ℂ (GeneralLinear (n + 1) K))
    (P : Subgroup (GeneralLinear (n + 1) K)) (a : P →* GeneralLinear n K)
    (hmat : ∀ (p : P) (h : GeneralLinear n K),
      rectangularJoin h.val 0 * p.val.val = rectangularJoin (h * a p).val 0)
    (hμ : ∀ p : P, MeasurePreserving (fun h : GeneralLinear n K => h * a p) μ μ)
    (Φ : adjacentRankCompactTests n K) (v : V) (g : GeneralLinear (n + 1) K) :
    Induction.eval P (adjacentRankCompactSectionRepresentation P a ρ ξ θ)
      (adjacentRankCompactSection μ ρ hρ ξ hξ θ P a hmat hμ Φ v) g =
      (θ.toMonoidHom g : ℂ) • adjacentRankCompactAverage μ ρ hρ ξ hξ Φ v g := rfl

section Linear

variable (μ : Measure (GeneralLinear n K)) [IsFiniteMeasureOnCompacts μ]
  (ρ : Representation ℂ (GeneralLinear n K) V) (hρ : IsSmooth ρ)
  (ξ : GeneralLinear n K →* ℂˣ)
  (hξ : IsLocallyConstant (fun h => (ξ h : ℂ)))
  (θ : Induction.SmoothCharacter ℂ (GeneralLinear (n + 1) K))
  (P : Subgroup (GeneralLinear (n + 1) K)) (a : P →* GeneralLinear n K)
  (hmat : ∀ (p : P) (h : GeneralLinear n K),
    rectangularJoin h.val 0 * p.val.val = rectangularJoin (h * a p).val 0)
  (hμ : ∀ p : P, MeasurePreserving (fun h : GeneralLinear n K => h * a p) μ μ)

/-- Bilinear dependence of the actual induced section on its test and vector. -/
def adjacentRankCompactSectionLinear :
    adjacentRankCompactTests n K →ₗ[ℂ] V →ₗ[ℂ]
      Induction.SmoothFunctions P (adjacentRankCompactSectionRepresentation P a ρ ξ θ) where
  toFun Φ :=
    { toFun := adjacentRankCompactSection μ ρ hρ ξ hξ θ P a hmat hμ Φ
      map_add' := by
        intro v w
        apply Subtype.ext
        apply Subtype.ext
        funext g
        change (θ.toMonoidHom g : ℂ) •
            adjacentRankCompactAverage μ ρ hρ ξ hξ Φ (v + w) g =
          (θ.toMonoidHom g : ℂ) • adjacentRankCompactAverage μ ρ hρ ξ hξ Φ v g +
            (θ.toMonoidHom g : ℂ) • adjacentRankCompactAverage μ ρ hρ ξ hξ Φ w g
        rw [adjacentRankCompactAverage_add, smul_add]
      map_smul' := by
        intro c v
        apply Subtype.ext
        apply Subtype.ext
        funext g
        change (θ.toMonoidHom g : ℂ) •
            adjacentRankCompactAverage μ ρ hρ ξ hξ Φ (c • v) g =
          c • ((θ.toMonoidHom g : ℂ) • adjacentRankCompactAverage μ ρ hρ ξ hξ Φ v g)
        rw [adjacentRankCompactAverage_smul, smul_comm] }
  map_add' := by
    intro Φ Ψ
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    apply Subtype.ext
    funext g
    change (θ.toMonoidHom g : ℂ) •
        adjacentRankCompactAverage μ ρ hρ ξ hξ (Φ + Ψ) v g =
      (θ.toMonoidHom g : ℂ) • adjacentRankCompactAverage μ ρ hρ ξ hξ Φ v g +
        (θ.toMonoidHom g : ℂ) • adjacentRankCompactAverage μ ρ hρ ξ hξ Ψ v g
    rw [adjacentRankCompactAverage_test_add, smul_add]
  map_smul' := by
    intro c Φ
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    apply Subtype.ext
    funext g
    change (θ.toMonoidHom g : ℂ) •
        adjacentRankCompactAverage μ ρ hρ ξ hξ (c • Φ) v g =
      c • ((θ.toMonoidHom g : ℂ) • adjacentRankCompactAverage μ ρ hρ ξ hξ Φ v g)
    rw [adjacentRankCompactAverage_test_smul, smul_comm]

/-- The linear section map on the algebraic test-vector tensor product. -/
def adjacentRankCompactSectionTensor :
    TensorProduct ℂ (adjacentRankCompactTests n K) V →ₗ[ℂ]
      Induction.SmoothFunctions P (adjacentRankCompactSectionRepresentation P a ρ ξ θ) :=
  TensorProduct.lift (adjacentRankCompactSectionLinear μ ρ hρ ξ hξ θ P a hmat hμ)

@[simp] theorem adjacentRankCompactSectionTensor_tmul
    (Φ : adjacentRankCompactTests n K) (v : V) :
    adjacentRankCompactSectionTensor μ ρ hρ ξ hξ θ P a hmat hμ
        (TensorProduct.tmul ℂ Φ v) =
      adjacentRankCompactSection μ ρ hρ ξ hξ θ P a hmat hμ Φ v := rfl

/-- The actual induced right action translates the test and multiplies by the
outer character, as in the formula defining the section. -/
theorem adjacentRankCompactSection_right
    (Φ : adjacentRankCompactTests n K) (v : V) (k : GeneralLinear (n + 1) K) :
    Induction.smoothInduced P (adjacentRankCompactSectionRepresentation P a ρ ξ θ) k
        (adjacentRankCompactSection μ ρ hρ ξ hξ θ P a hmat hμ Φ v) =
      (θ.toMonoidHom k : ℂ) • adjacentRankCompactSection μ ρ hρ ξ hξ θ P a hmat hμ
        (adjacentRankCompactTestTranslate k Φ) v := by
  apply Subtype.ext
  apply Subtype.ext
  funext g
  exact adjacentRankCompactSectionValue_right μ ρ hρ ξ hξ θ Φ v g k

end Linear

end Langlands.RankinSelberg
