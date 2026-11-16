import Langlands.Global.RankinSelberg.UnfoldingDual

/-! # Nonnegative rectangular integration and quotient descent -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry NumberField MeasureTheory
open scoped CategoryTheory.MonObj ENNReal
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal

open Unfolding

local instance rectangularLIntegralSchemeAffine (F : Type u) [Field F] (n : ℕ) :
    IsAffine (Scheme F n).X.left := GroupScheme.GeneralLinear.isAffine_groupScheme _ _

local instance rectangularLIntegralRectangleMeasurableSpace (F : Type u) [Field F]
    [NumberField F] (k m : ℕ) :
    MeasurableSpace (Matrix (Fin k) (Fin m) (Adeles F)) := borel _

local instance rectangularLIntegralRectangleBorelSpace (F : Type u) [Field F]
    [NumberField F] (k m : ℕ) :
    BorelSpace (Matrix (Fin k) (Fin m) (Adeles F)) := ⟨rfl⟩

local instance rectangularLIntegralSchemeSmooth (F : Type u) [Field F] (n : ℕ) :
    Smooth (Scheme F n).X.hom := GroupScheme.GeneralLinear.smoothStatement _ _

variable (F : Type u) [Field F] [NumberField F]

/-- Integrate an extended nonnegative function along the rectangular chart. -/
def rectangularLIntegral {r t : ℕ} (h : t < r)
    (Ξ : Points F (r + 1) → ℝ≥0∞) (g : Points F (t + 1)) : ℝ≥0∞ :=
  ∫⁻ x, Ξ (rectangularPoint F h g x)
    ∂rectangleMeasure F (r - (t + 1)) (t + 1)

theorem rectangularLIntegral_mono {r t : ℕ} (h : t < r)
    {Ξ Ξ' : Points F (r + 1) → ℝ≥0∞} (hΞ : Ξ ≤ Ξ') :
    rectangularLIntegral F h Ξ ≤ rectangularLIntegral F h Ξ' := by
  intro g
  exact lintegral_mono fun x => hΞ (rectangularPoint F h g x)

theorem measurable_rectangularLIntegral {r t : ℕ} (h : t < r)
    {Ξ : Points F (r + 1) → ℝ≥0∞} (hΞ : Measurable Ξ) :
    Measurable (rectangularLIntegral F h Ξ) :=
  (hΞ.comp (continuous_rectangularPoint F h).measurable).lintegral_prod_right'

/-- Left unipotent invariance is preserved by the rectangular integral. -/
theorem rectangularLIntegral_unipotent_mul {r t : ℕ} (h : t < r)
    (Ξ : Points F (r + 1) → ℝ≥0∞)
    (hΞ : ∀ (n : unipotentAdelic F (r + 1)) (g : Points F (r + 1)),
      Ξ ((n : Points F (r + 1)) * g) = Ξ g)
    (n : unipotentAdelic F (t + 1)) (g : Points F (t + 1)) :
    rectangularLIntegral F h Ξ ((n : Points F (t + 1)) * g) =
      rectangularLIntegral F h Ξ g := by
  unfold rectangularLIntegral
  apply lintegral_congr
  intro x
  rw [rectangularPoint_mul_left]
  exact hΞ (padUnipotent F (Nat.le_of_lt (Nat.succ_lt_succ h)) n) _

/-- Evaluate the rectangular integral on the published quotient representatives. -/
def rectangularQuotientLIntegral {r t : ℕ} (h : t < r)
    (Ξ : Points F (r + 1) → ℝ≥0∞) (p : WhittakerQuotient F (t + 1)) : ℝ≥0∞ :=
  rectangularLIntegral F h Ξ p.out

/-- For a left unipotent-invariant function, this quotient evaluation recovers
the rectangular integral at every representative. -/
theorem rectangularQuotientLIntegral_mk {r t : ℕ} (h : t < r)
    (Ξ : Points F (r + 1) → ℝ≥0∞)
    (hΞ : ∀ (n : unipotentAdelic F (r + 1)) (g : Points F (r + 1)),
      Ξ ((n : Points F (r + 1)) * g) = Ξ g)
    (g : Points F (t + 1)) :
    rectangularQuotientLIntegral F h Ξ
        (LeftCosetSpace.mk (unipotentAdelic F (t + 1)) g) =
      rectangularLIntegral F h Ξ g := by
  obtain ⟨n, hn⟩ := exists_out_mk_eq (unipotentAdelic F (t + 1)) g
  unfold rectangularQuotientLIntegral
  rw [hn, rectangularLIntegral_unipotent_mul F h Ξ hΞ]

/-- Quotient measurability follows by descent, without a measurability claim
for the arbitrary choice of representatives. -/
theorem measurable_rectangularQuotientLIntegral {r t : ℕ} (h : t < r)
    {Ξ : Points F (r + 1) → ℝ≥0∞} (hΞm : Measurable Ξ)
    (hΞ : ∀ (n : unipotentAdelic F (r + 1)) (g : Points F (r + 1)),
      Ξ ((n : Points F (r + 1)) * g) = Ξ g) :
    Measurable (rectangularQuotientLIntegral F h Ξ) := by
  unfold rectangularQuotientLIntegral
  rw [out_eq_lift (unipotentAdelic F (t + 1)) _
    (rectangularLIntegral_unipotent_mul F h Ξ hΞ)]
  exact measurable_from_quotient.mpr (measurable_rectangularLIntegral F h hΞm)

end Langlands.Global.RankinSelbergGlobal
