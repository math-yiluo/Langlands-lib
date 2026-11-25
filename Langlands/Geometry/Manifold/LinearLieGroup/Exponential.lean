import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# The exponential of a real Banach algebra as a local diffeomorphism

For a complete normed real algebra `𝔸`: the exponential `NormedSpace.exp` is smooth
(`contDiff_exp`), its derivative at `0` is the identity, and `expPartialHomeomorph 𝔸` is `exp` as an
open partial homeomorphism around `0` whose inverse (a local logarithm near `1`) is smooth on its
domain (`contDiffOn_expPartialHomeomorph_symm`). `expUnit 𝔸 X` is `exp X` as an element of `𝔸ˣ`.

These are the charts of the linear Lie groups of `Langlands.LinearLieGroup.IsExpLieAlgebra`
(`Basic`) and of `𝔸ˣ` itself (`Units`). The algebra need not be finite-dimensional here.
-/

namespace Langlands.LinearLieGroup

open scoped ContDiff Topology
open NormedSpace Set

section ExpChart

variable (𝔸 : Type*) [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]

/-- The exponential of a complete normed real algebra is smooth (it is analytic). -/
theorem contDiff_exp {n : WithTop ℕ∞} : ContDiff ℝ n (exp : 𝔸 → 𝔸) :=
  contDiff_iff_contDiffAt.2 fun x => (exp_analytic (𝕂 := ℝ) x).contDiffAt

variable {𝔸} in
/-- `exp (x + y) = exp x * exp y` for commuting `x`, `y` in a complete normed real algebra. (Mathlib's
`NormedSpace.exp_add_of_commute` asks for a normed `ℚ`-algebra structure, which is not an instance
for real algebras.) -/
theorem exp_add_of_commute' {x y : 𝔸} (h : Commute x y) : exp (x + y) = exp x * exp y :=
  exp_add_of_commute_of_mem_ball (𝕂 := ℝ) h
    (by rw [expSeries_radius_eq_top]; exact edist_lt_top _ _)
    (by rw [expSeries_radius_eq_top]; exact edist_lt_top _ _)

/-- The open set of points at which the derivative of `exp` is invertible. -/
def expRegularSet : Set 𝔸 := {X | IsUnit (fderiv ℝ (exp : 𝔸 → 𝔸) X)}

/-- The set where the derivative of `exp` is invertible is open. -/
theorem isOpen_expRegularSet : IsOpen (expRegularSet 𝔸) :=
  Units.isOpen.preimage ((contDiff_exp 𝔸 (n := 1)).continuous_fderiv one_ne_zero)

/-- The derivative of `exp` at `0` is the identity, hence invertible. -/
theorem zero_mem_expRegularSet : (0 : 𝔸) ∈ expRegularSet 𝔸 := by
  simp [expRegularSet, (hasFDerivAt_exp_zero (𝕂 := ℝ) (𝔸 := 𝔸)).fderiv]

/-- `exp` has strict derivative the identity at `0`, as a continuous linear equivalence. -/
theorem hasStrictFDerivAt_exp_zero_equiv :
    HasStrictFDerivAt (exp : 𝔸 → 𝔸) ((ContinuousLinearEquiv.refl ℝ 𝔸 : 𝔸 →L[ℝ] 𝔸)) 0 := by
  convert (hasStrictFDerivAt_exp_zero (𝕂 := ℝ) (𝔸 := 𝔸)) using 1
  exact ContinuousLinearMap.ext fun _ => rfl

/-- `exp` as an open partial homeomorphism: the local inverse at `0` given by the inverse function
theorem, restricted to the open set where the derivative of `exp` is invertible. -/
noncomputable def expPartialHomeomorph : OpenPartialHomeomorph 𝔸 𝔸 :=
  ((hasStrictFDerivAt_exp_zero_equiv 𝔸).toOpenPartialHomeomorph exp).restrOpen
    (expRegularSet 𝔸) (isOpen_expRegularSet 𝔸)

/-- The partial homeomorphism `expPartialHomeomorph 𝔸` is `exp`. -/
theorem coe_expPartialHomeomorph : ⇑(expPartialHomeomorph 𝔸) = exp := rfl

/-- `0` is in the source of `expPartialHomeomorph 𝔸`. -/
theorem zero_mem_expPartialHomeomorph_source : (0 : 𝔸) ∈ (expPartialHomeomorph 𝔸).source :=
  ⟨(hasStrictFDerivAt_exp_zero_equiv 𝔸).mem_toOpenPartialHomeomorph_source,
    zero_mem_expRegularSet 𝔸⟩

/-- `1` is in the target of `expPartialHomeomorph 𝔸`. -/
theorem one_mem_expPartialHomeomorph_target : (1 : 𝔸) ∈ (expPartialHomeomorph 𝔸).target := by
  simpa [coe_expPartialHomeomorph] using
    (expPartialHomeomorph 𝔸).map_source (zero_mem_expPartialHomeomorph_source 𝔸)

/-- The local logarithm sends `1` to `0`. -/
theorem expPartialHomeomorph_symm_one : (expPartialHomeomorph 𝔸).symm 1 = 0 := by
  simpa [coe_expPartialHomeomorph] using
    (expPartialHomeomorph 𝔸).left_inv (zero_mem_expPartialHomeomorph_source 𝔸)

/-- On the source of `expPartialHomeomorph 𝔸` the derivative of `exp` is invertible. -/
theorem expPartialHomeomorph_source_subset :
    (expPartialHomeomorph 𝔸).source ⊆ expRegularSet 𝔸 := fun _ h => h.2

/-- The local logarithm is smooth on its domain (inverse function theorem at every point, using the
invertibility of the derivative of `exp` on the source). -/
theorem contDiffOn_expPartialHomeomorph_symm {n : WithTop ℕ∞} :
    ContDiffOn ℝ n (expPartialHomeomorph 𝔸).symm (expPartialHomeomorph 𝔸).target := by
  intro y hy
  set e := expPartialHomeomorph 𝔸
  have hs : e.symm y ∈ e.source := e.map_target hy
  have hu : IsUnit (fderiv ℝ (exp : 𝔸 → 𝔸) (e.symm y)) :=
    expPartialHomeomorph_source_subset 𝔸 hs
  refine (e.contDiffAt_symm (f₀' := ContinuousLinearEquiv.unitsEquiv ℝ 𝔸 hu.unit) hy ?_
    ?_).contDiffWithinAt
  · have h1 : ((ContinuousLinearEquiv.unitsEquiv ℝ 𝔸 hu.unit : 𝔸 ≃L[ℝ] 𝔸) : 𝔸 →L[ℝ] 𝔸) =
        fderiv ℝ (exp : 𝔸 → 𝔸) (e.symm y) := by
      ext x; simp
    rw [h1]
    exact ((contDiff_exp 𝔸 (n := 1)).differentiable one_ne_zero _).hasFDerivAt
  · exact (contDiff_exp 𝔸).contDiffAt

/-- `exp X` as a unit, with inverse `exp (-X)`. -/
noncomputable def expUnit (X : 𝔸) : 𝔸ˣ :=
  ⟨exp X, exp (-X), by
    rw [← exp_add_of_commute' (Commute.neg_right (Commute.refl X)), add_neg_cancel, exp_zero],
   by rw [← exp_add_of_commute' (Commute.neg_left (Commute.refl X)), neg_add_cancel, exp_zero]⟩

/-- The value of `expUnit 𝔸 X` is `exp X`. -/
@[simp] theorem coe_expUnit (X : 𝔸) : (expUnit 𝔸 X : 𝔸) = exp X := rfl

/-- The inverse of `expUnit 𝔸 X` is `exp (-X)`. -/
@[simp] theorem coe_expUnit_inv (X : 𝔸) : ((expUnit 𝔸 X)⁻¹ : 𝔸ˣ) = exp (-X) := rfl

/-- `expUnit 𝔸` is continuous into the units. -/
theorem continuous_expUnit : Continuous (expUnit 𝔸) :=
  Units.continuous_iff.2 ⟨(contDiff_exp 𝔸 (n := 0)).continuous,
    (contDiff_exp 𝔸 (n := 0)).continuous.comp continuous_neg⟩

end ExpChart

end Langlands.LinearLieGroup
