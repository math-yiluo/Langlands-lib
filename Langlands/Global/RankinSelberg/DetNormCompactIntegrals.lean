import Langlands.Global.AdelicGroupNormOneFunctorial
import Langlands.Global.AdelicGLStandardCompact
import Langlands.Global.RankinSelberg.RectangularRightIntegration

/-! # Compact subgroups and the rectangular determinant factor -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry NumberField MeasureTheory
open scoped CategoryTheory.MonObj ENNReal NNReal
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal

local instance compactDetSchemeAffine (F : Type u) [Field F] (n : ℕ) :
    IsAffine (Scheme F n).X.left := GroupScheme.GeneralLinear.isAffine_groupScheme _ _

variable (F : Type u) [Field F] [NumberField F]

/-- The determinant norm on actual adelic points, retaining its positive units
codomain and continuous homomorphism structure. -/
def detNormHom (n : ℕ) : Points F n →ₜ* ℝ≥0ˣ :=
  (AdelicBlockDeterminantCharacter.determinantNorm F n).comp
    (ContinuousMonoidHom.toContinuousMonoidHom
      (GeneralLinearGroupPoints.adelicHomeomorph F n))

@[simp]
theorem coe_detNormHom (n : ℕ) (g : Points F n) :
    ((detNormHom F n g : ℝ≥0) : ℝ) = detNorm F n g := rfl

/-- The positive determinant norm is one on any compact subgroup. -/
theorem detNorm_eq_one_of_mem_compactSubgroup {n : ℕ}
    (K : Subgroup (Points F n)) (hK : IsCompact (K : Set (Points F n)))
    {g : Points F n} (hg : g ∈ K) :
    detNorm F n g = 1 := by
  have he := continuousMonoidHom_eq_one_on_compactSubgroup
    (detNormHom F n) K hK hg
  exact congrArg (fun a : ℝ≥0ˣ => ((a : ℝ≥0) : ℝ)) he

/-- In particular, the norm is one on the standard adelic compact subgroup
transported to actual group-scheme points. -/
theorem detNorm_eq_one_of_mem_standardCompact {n : ℕ} {g : Points F n}
    (hg : GeneralLinearGroupPoints.adelicEquiv F n g ∈
      PrimitiveAdelicHeight.standardCompact F n) :
    detNorm F n g = 1 := by
  have he := continuousMonoidHom_eq_one_on_compactSubgroup
    (AdelicBlockDeterminantCharacter.determinantNorm F n)
    (PrimitiveAdelicHeight.standardCompact F n)
    (PrimitiveAdelicHeight.isCompact_standardCompact F n) hg
  exact congrArg (fun a : ℝ≥0ˣ => ((a : ℝ≥0) : ℝ)) he

variable [CompactSpace (AdeleQuotient F)]

/-- For a compact leading block, fixed-unipotent right integration has no
determinant factor. -/
theorem rectangularRightIntegral_eq_of_mem_compactSubgroup {r t : ℕ} (h : t < r)
    (Ξ : Points F (r + 1) → ℝ≥0∞) (hΞ : Measurable Ξ)
    (K : Subgroup (Points F (t + 1)))
    (hK : IsCompact (K : Set (Points F (t + 1))))
    {g : Points F (t + 1)} (hg : g ∈ K) :
    rectangularRightIntegral F h Ξ g =
      ∫⁻ x, Ξ (rectangularPoint F h g x)
        ∂rectangleMeasure F (r - (t + 1)) (t + 1) := by
  rw [rectangularRightIntegral_eq F h Ξ hΞ,
    detNorm_eq_one_of_mem_compactSubgroup F K hK hg]
  simp

/-- A padded right symmetry from a compact subgroup is preserved by
rectangular integration. -/
theorem lintegral_rectangularPoint_right_invariant_of_compactSubgroup
    {r t : ℕ} (h : t < r)
    (Ξ : Points F (r + 1) → ℝ≥0∞) (hΞ : Measurable Ξ)
    (K : Subgroup (Points F (t + 1)))
    (hK : IsCompact (K : Set (Points F (t + 1))))
    {a : Points F (t + 1)} (ha : a ∈ K)
    (hinv : ∀ y : Points F (r + 1),
      Ξ (y * pad F (Nat.le_of_lt (Nat.succ_lt_succ h)) a) = Ξ y)
    (g : Points F (t + 1)) :
    (∫⁻ x, Ξ (rectangularPoint F h (g * a) x)
      ∂rectangleMeasure F (r - (t + 1)) (t + 1)) =
      ∫⁻ x, Ξ (rectangularPoint F h g x)
        ∂rectangleMeasure F (r - (t + 1)) (t + 1) := by
  exact lintegral_rectangularPoint_right_invariant F h Ξ hΞ a
    (detNorm_eq_one_of_mem_compactSubgroup F K hK ha) hinv g

end Langlands.Global.RankinSelbergGlobal
