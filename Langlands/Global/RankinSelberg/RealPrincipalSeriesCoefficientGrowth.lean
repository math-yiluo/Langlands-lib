import Langlands.Global.RankinSelberg.RealPrincipalSeriesHeight
import Langlands.Representation.Archimedean.KIntegralInvariance

/-! # Growth of coefficients of derivative-bounded functionals on the real principal series -/

noncomputable section

open Langlands.Archimedean Langlands.LocalFactor.Archimedean
open scoped Matrix.Norms.Operator Manifold ContDiff

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal
namespace RealPrincipalSeries

open RealPlaceRestriction

variable (r : ℕ) (ds : List RealBlock)

local notation "G" => Langlands.GeneralLinear (r + 1) ℝ
local notation "Mat" => Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ
local notation "P" => principalSeries ℝ (r + 1) (realPositionCharacter ds)
local notation "D" => rightDerivative (matrixModel ℝ (r + 1))

/-- Right translation on the smooth position principal series. -/
def translate (g : G) : P →ₗ[ℂ] P :=
  ((Whittaker.rightTranslation ℂ G g).domRestrict P).codRestrict P
    (fun f => rightTranslation_mem_principalSeries _ f.2 g)

private def derivative (X : Mat) : P →ₗ[ℂ] P :=
  (rightDerivativeLinearMap P (fun _ h => h.1) X).codRestrict P
    (fun f => rightDerivative_mem_principalSeries _ f.2 X)

private def derivativeWord (Xs : List Mat) : P →ₗ[ℂ] P :=
  Xs.foldr (fun X B => (derivative r ds X).comp B) LinearMap.id

@[simp] private theorem derivativeWord_apply (Xs : List Mat) (f : P) :
    (derivativeWord r ds Xs f : G → ℂ) =
      RealLocalWhittaker.iteratedRightDerivative r Xs f := by
  induction Xs with
  | nil => rfl
  | cons X Xs ih =>
    change D X (derivativeWord r ds Xs f) = D X (RealLocalWhittaker.iteratedRightDerivative r Xs f)
    rw [ih]

private theorem derivativeWord_append_singleton (Xs : List Mat) (X : Mat) (f : P) :
    derivativeWord r ds (Xs ++ [X]) f = derivativeWord r ds Xs (derivative r ds X f) := by
  induction Xs with
  | nil => rfl
  | cons Y Xs ih =>
    change derivative r ds Y (derivativeWord r ds (Xs ++ [X]) f) =
      derivative r ds Y (derivativeWord r ds Xs (derivative r ds X f))
    rw [ih]

private def adjointDirection (g : G) (X : Mat) : Mat := (g⁻¹).val * X * g.val

private theorem derivative_translate_apply (f : P) (g k : G) (X : Mat) :
    (derivative r ds X (translate r ds g f) : G → ℂ) k =
      (derivative r ds (adjointDirection r g X) f : G → ℂ) (k * g) := by
  have h := KIntegralInvariance.rightDerivative_mul_eq f.2.1 g k (adjointDirection r g X)
  have hX : g.val * adjointDirection r g X * (g⁻¹).val = X := by
    calc
      _ = (g.val * (g⁻¹).val) * X * (g.val * (g⁻¹).val) := by
        simp only [adjointDirection, Matrix.mul_assoc]
      _ = _ := by rw [g.mul_inv, Matrix.one_mul, Matrix.mul_one]
  rw [hX] at h
  exact h.symm

private theorem derivativeWord_translate_apply (f : P) (g k : G) (Xs : List Mat) :
    (derivativeWord r ds Xs (translate r ds g f) : G → ℂ) k =
      (derivativeWord r ds (Xs.map (adjointDirection r g)) f : G → ℂ) (k * g) := by
  induction Xs generalizing k with
  | nil => rfl
  | cons X Xs ih =>
    have heq : derivativeWord r ds Xs (translate r ds g f) =
        translate r ds g (derivativeWord r ds (Xs.map (adjointDirection r g)) f) := by
      apply Subtype.ext
      exact funext ih
    change (derivative r ds X (derivativeWord r ds Xs (translate r ds g f)) : G → ℂ) k = _
    rw [heq, derivative_translate_apply]
    rfl

open scoped Matrix.Norms.Frobenius in
private theorem adjointDirection_entry_bound (X : Mat) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ g : G, ∀ p q, ‖adjointDirection r g X p q‖ ≤ C * realMatrixHeight g := by
  refine ⟨‖X‖, norm_nonneg _, fun g p q => ?_⟩
  have he : ‖(g⁻¹).val‖ * ‖g.val‖ ≤ realMatrixHeight g := by
    rw [realMatrixHeight_eq_frobenius]
    nlinarith [sq_nonneg (‖(g⁻¹).val‖ - ‖g.val‖), sq_nonneg ‖g.val‖, sq_nonneg ‖(g⁻¹).val‖]
  let A := adjointDirection r g X
  have hEntry : ‖A p q‖ ≤ ‖A‖ :=
    (PiLp.norm_apply_le (WithLp.toLp 2 (A p)) q).trans
      (PiLp.norm_apply_le (WithLp.toLp 2 (fun i => WithLp.toLp 2 (A i))) p)
  calc
    _ ≤ ‖A‖ := hEntry
    _ ≤ ‖(g⁻¹).val‖ * ‖X‖ * ‖g.val‖ :=
      (Matrix.frobenius_norm_mul ((g⁻¹).val * X) g.val).trans
        (mul_le_mul_of_nonneg_right (Matrix.frobenius_norm_mul _ _) (norm_nonneg _))
    _ = ‖X‖ * (‖(g⁻¹).val‖ * ‖g.val‖) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left he (norm_nonneg _)

private theorem derivative_basis_sum (X : Mat) (f : P) :
    derivative r ds X f =
      ∑ ij : Fin (r + 1) × Fin (r + 1),
        X ij.1 ij.2 • derivative r ds (Matrix.single ij.1 ij.2 1) f := by
  classical
  have hX : X = ∑ ij : Fin (r + 1) × Fin (r + 1),
      X ij.1 ij.2 • Matrix.single ij.1 ij.2 1 := by
    rw [Fintype.sum_prod_type]
    simp only [Matrix.smul_single, smul_eq_mul, mul_one]
    exact Matrix.matrix_eq_sum_single X
  apply Subtype.ext
  simp only [Submodule.coe_sum, Submodule.coe_smul_of_tower]
  change D X (f : G → ℂ) = ∑ ij : Fin (r + 1) × Fin (r + 1),
    X ij.1 ij.2 • D (Matrix.single ij.1 ij.2 1) (f : G → ℂ)
  conv_lhs => rw [hX]
  exact rightDerivative_sum_smul _ _ _ _

private theorem conjugated_word_bound {N : ℕ}
    (hN : ∀ f : P, ∃ C : ℝ, 0 ≤ C ∧ ∀ g, ‖(f : G → ℂ) g‖ ≤ C * realMatrixHeight g ^ N)
    (Xs : List Mat) (f : P) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (g k : G), k ∈ unitaryCompact ℝ (r + 1) →
      ‖(derivativeWord r ds (Xs.map (adjointDirection r g)) f : G → ℂ) (k * g)‖ ≤
        C * realMatrixHeight g ^ (N + Xs.length) := by
  induction Xs using List.reverseRecOn generalizing f with
  | nil =>
    obtain ⟨C, hC, hb⟩ := hN f
    exact ⟨C, hC, fun g k hk => by
      simpa only [realMatrixHeight_unitary_mul hk, List.map_nil, List.length_nil, add_zero,
        derivativeWord, List.foldr_nil, LinearMap.id_apply] using hb (k * g)⟩
  | append_singleton Xs X ih =>
    classical
    let I := Fin (r + 1) × Fin (r + 1)
    let f' (ij : I) : P := derivative r ds (Matrix.single ij.1 ij.2 1) f
    choose C hC hBound using fun ij : I => ih (f' ij)
    obtain ⟨A, hA, hAdj⟩ := adjointDirection_entry_bound r X
    refine ⟨A * ∑ ij, C ij, mul_nonneg hA (Finset.sum_nonneg fun ij _ => hC ij),
      fun g k hk => ?_⟩
    rw [List.map_append, List.map_singleton, derivativeWord_append_singleton, derivative_basis_sum]
    simp only [map_sum, LinearMap.map_smul_of_tower, Submodule.coe_sum, Submodule.coe_smul_of_tower,
      Finset.sum_apply, Pi.smul_apply]
    have hH := realMatrixHeight_nonneg g
    calc
      _ ≤ ∑ ij : I, (A * realMatrixHeight g) *
          (C ij * realMatrixHeight g ^ (N + Xs.length)) := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun ij _ => ?_)
        rw [norm_smul]
        exact mul_le_mul (hAdj g ij.1 ij.2) (hBound ij g k hk) (norm_nonneg _)
          (mul_nonneg hA hH)
      _ = _ := by
        simp only [List.length_append, List.length_singleton, ← Nat.add_assoc, pow_succ]
        rw [← Finset.mul_sum, ← Finset.sum_mul]
        ring

/-- A finite bound by compact right-derivative supremum seminorms on the smooth
position principal series. The bound records only the norms needed below. -/
def HasCompactDerivativeBound (ℓ : P →ₗ[ℂ] ℂ) : Prop :=
  ∃ (m : ℕ) (Xs : Fin m → List Mat) (A : ℝ), 0 ≤ A ∧
    ∀ (f : P) (B : Fin m → ℝ),
      (∀ i, ∀ k ∈ unitaryCompact ℝ (r + 1),
        ‖RealLocalWhittaker.iteratedRightDerivative r (Xs i) f k‖ ≤ B i) →
      ‖ℓ f‖ ≤ A * ∑ i, B i

/-- A linear form with a finite compact derivative bound has one height exponent
for all its coefficients. The coefficient at `g` is the form on the right translate. -/
def CompactFunctionalGrowthStatement : Prop :=
  ∀ (r : ℕ) (ds : List RealBlock)
    (ℓ : principalSeries ℝ (r + 1) (realPositionCharacter ds) →ₗ[ℂ] ℂ),
    HasCompactDerivativeBound r ds ℓ →
      ∃ N : ℕ, ∀ f : principalSeries ℝ (r + 1) (realPositionCharacter ds),
        ∃ C : ℝ, 0 ≤ C ∧ ∀ g : Langlands.GeneralLinear (r + 1) ℝ,
          ‖ℓ (translate r ds g f)‖ ≤ C * realMatrixHeight g ^ N

theorem compactFunctionalGrowth : CompactFunctionalGrowthStatement := by
  intro r ds ℓ hℓ
  obtain ⟨m, Xs, A, hA, hBound⟩ := hℓ
  obtain ⟨N, hN⟩ := exists_uniform_principalSeries_derivative_height r ds
  have hN' : ∀ f : principalSeries ℝ (r + 1) (realPositionCharacter ds),
      ∃ C : ℝ, 0 ≤ C ∧ ∀ g, ‖(f : Langlands.GeneralLinear (r + 1) ℝ → ℂ) g‖ ≤
        C * realMatrixHeight g ^ N := by
    intro f
    exact hN f f.2 []
  let M := N + ∑ i, (Xs i).length
  refine ⟨M, fun f => ?_⟩
  choose C hC hCBound using fun i => conjugated_word_bound r ds hN' (Xs i) f
  refine ⟨A * ∑ i, C i, mul_nonneg hA (Finset.sum_nonneg fun i _ => hC i), fun g => ?_⟩
  have hH : 1 ≤ realMatrixHeight g := le_trans (by norm_num) (two_le_realMatrixHeight (Nat.succ_pos r) g)
  have hlen (i : Fin m) : N + (Xs i).length ≤ M :=
    Nat.add_le_add_left (Finset.single_le_sum (fun j _ => Nat.zero_le (Xs j).length)
      (Finset.mem_univ i)) N
  calc
    _ ≤ A * ∑ i, C i * realMatrixHeight g ^ M := by
      apply hBound
      intro i k hk
      rw [← derivativeWord_apply, derivativeWord_translate_apply]
      exact (hCBound i g k hk).trans (mul_le_mul_of_nonneg_left
        (pow_le_pow_right₀ hH (hlen i)) (hC i))
    _ = _ := by rw [← Finset.sum_mul, mul_assoc]

end RealPrincipalSeries
end Langlands.Global.RankinSelbergGlobal
