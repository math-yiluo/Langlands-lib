import Langlands.Representation.Archimedean.RealLeviParabolicIntegration
import Langlands.Representation.Archimedean.RealCartanCompactSupport
import Langlands.Representation.Archimedean.RealLeviLimit

/-! # Compact integration in opposed block coordinates -/

noncomputable section

open Matrix MeasureTheory
open scoped Matrix.Norms.Operator Manifold ContDiff

namespace Langlands.Archimedean.RealLeviCompactChart

open Langlands.GeneralLinear GramFormula PrincipalSeriesExtension
  MaximalParabolicIntegration RealPrincipalSeriesDuality RealLeviChart
  RealCartanCompactSupport OrthogonalFinitePolynomial

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

local notation "G" k:max => Langlands.GeneralLinear k ℝ
local notation "K" k:max => Matrix.unitaryGroup (Fin k) ℝ
local notation "Mat" k:max => Matrix (Fin k) (Fin k) ℝ

section Modulus

variable {n : ℕ}

private def halfExponent (n : ℕ) (i : ℕ) : ℂ :=
  ((n : ℂ) - 1) / 2 - (i : ℂ)

private abbrev modulusExponent (n : ℕ) : Fin n → ℂ :=
  shiftedExponent n (halfExponent n)

/-- The Borel-modulus radial extension of the constant compact test. -/
def modulusWeight (x : G n) : ℂ :=
  extension (modulusExponent n) 1 x

theorem continuous_modulusWeight : Continuous (modulusWeight : G n → ℂ) :=
  (contMDiff_extension (modulusExponent n) (P := 1) (φ := 1) (by intro k; simp)).continuous

@[simp]
theorem modulusWeight_one : modulusWeight (1 : G n) = 1 := by
  change extension (modulusExponent n) (fun _ => (1 : ℂ)) (Unitary.toUnits (1 : K n)) = 1
  exact extension_unitary _ _ _

private theorem signedOrthogonalPart_eq {x : G n} {b : Mat n} {k : K n}
    (hb : b.IsUpperTriangular) (hnz : ∀ i, b i i ≠ 0)
    (hx : (x : Mat n) = b * (k : Mat n)) :
    signedOrthogonalPart x = signDiagonal (fun i => b i i) * k := by
  apply Subtype.ext
  change signedOrthogonal (x : Mat n) = _
  rw [hx, signedOrthogonal_mul hb hnz]
  · rfl
  · simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] using
      (Matrix.mem_unitaryGroup_iff.mp k.2)

private theorem exists_triangular_compact (x : G n) :
    ∃ (B : Mat n) (w : K n), B.IsUpperTriangular ∧
      (∀ i, B i i ≠ 0) ∧ (x : Mat n) = B * (w : Mat n) := by
  obtain ⟨a, u, v, hv, rfl⟩ := exists_diagonalUnits_mul_upperUnipotent_mul_unitaryCompact x
  let B := Matrix.diagonal (fun i => (a i : ℝ)) * (u : G n).val
  refine ⟨B, ⟨v.val, hv⟩, isUpperTriangular_diagonal_mul a u, fun i => ?_, rfl⟩
  change (Matrix.diagonal (fun j => (a j : ℝ)) * (u : G n).val) i i ≠ 0
  rw [diagonal_mul_apply_self]
  exact (a i).ne_zero

/-- The signed orthogonal factor is equivariant under right orthogonal multiplication. -/
theorem orthogonalPart_mul_right (x : G n) (k : K n) :
    signedOrthogonalPart (x * Unitary.toUnits k) = signedOrthogonalPart x * k := by
  obtain ⟨B, w, hb, hnz, hx⟩ := exists_triangular_compact x
  have hxk : ((x * Unitary.toUnits k : G n) : Mat n) = B * ((w * k : K n) : Mat n) := by
    change (x : Mat n) * (k : Mat n) = B * ((w : Mat n) * (k : Mat n))
    rw [hx, mul_assoc]
  rw [signedOrthogonalPart_eq hb hnz hxk, signedOrthogonalPart_eq hb hnz hx, mul_assoc]

private theorem extension_mul_right (s : Fin n → ℂ) (φ : K n → ℂ) (x : G n) (k : K n) :
    extension s φ (x * Unitary.toUnits k) = extension s (fun y => φ (y * k)) x := by
  obtain ⟨B, w, hb, hnz, hx⟩ := exists_triangular_compact x
  have hxk : ((x * Unitary.toUnits k : G n) : Mat n) = B * ((w * k : K n) : Mat n) := by
    change (x : Mat n) * (k : Mat n) = B * ((w : Mat n) * (k : Mat n))
    rw [hx, mul_assoc]
  rw [extension_eq _ φ hb hnz (w * k).2 hxk, extension_eq _ _ hb hnz w.2 hx, mul_assoc]

theorem modulusWeight_mul_right (x : G n) (k : K n) :
    modulusWeight (x * Unitary.toUnits k) = modulusWeight x :=
  extension_mul_right _ (fun _ => 1) x k

private theorem isModulusCovariant_extension {φ : K n → ℂ}
    (hφ : ∀ (a : Fin n → ℝˣ) (k : K n), φ (signDiagonal (fun i => (a i : ℝ)) * k) = φ k) :
    IsModulusCovariant (extension (modulusExponent n) φ) := by
  let χ (i : ℕ) (x : ℝˣ) := ((|(x : ℝ)| : ℝ) : ℂ) ^ halfExponent n i
  have hχ (i : ℕ) (x : ℝˣ) :
      χ i x = χ i (signUnit x) * ((|(x : ℝ)| : ℝ) : ℂ) ^ halfExponent n i := by
    simp [χ, abs_signUnit]
  have h1 (a : Fin n → ℝˣ) :
      principalSeriesCharacter ℝ n χ (fun i => signUnit (a i)) = 1 := by
    simp [principalSeriesCharacter, χ, Real.norm_eq_abs, abs_signUnit]
  have heq (a : Fin n → ℝˣ) :
      principalSeriesCharacter ℝ n χ a = modulusCharacter n a := by
    rw [principalSeriesCharacter_eq (halfExponent n) hχ, h1, mul_one, modulusCharacter]
    refine Finset.prod_congr rfl fun i _ => ?_
    congr 1
    simp only [shiftedExponent, halfExponent]
    ring
  intro a u x
  rw [← heq a]
  exact extension_mul_left (halfExponent n) hχ (fun b k => by rw [h1, one_mul, hφ]) a u x

theorem isModulusCovariant_modulusWeight : IsModulusCovariant (modulusWeight : G n → ℂ) :=
  isModulusCovariant_extension fun _ _ => rfl

private theorem diagonalSigns_eq (a : Fin n → ℝˣ) :
    Unitary.toUnits (signDiagonal (fun i => (a i : ℝ))) =
      Iwasawa.diagonalUnits (fun i => signUnit (a i)) := by
  apply Units.ext
  change Matrix.diagonal (fun i => signReal (a i)) =
    ((Iwasawa.diagonalUnits (fun i => signUnit (a i)) : G n) : Mat n)
  rw [Iwasawa.diagonalUnits_val]
  simp [signUnit_val]

theorem modulusWeight_mul_sign (a : Fin n → ℝˣ) (x : G n) :
    modulusWeight (Unitary.toUnits (signDiagonal (fun i => (a i : ℝ))) * x) =
      modulusWeight x := by
  rw [diagonalSigns_eq]
  have h := isModulusCovariant_modulusWeight (fun i => signUnit (a i)) 1 x
  simpa [modulusCharacter, abs_signUnit] using h

theorem orthogonalPart_mul_sign (a : Fin n → ℝˣ) (x : G n) :
    signedOrthogonalPart (Unitary.toUnits (signDiagonal (fun i => (a i : ℝ))) * x) =
      signDiagonal (fun i => (a i : ℝ)) * signedOrthogonalPart x := by
  obtain ⟨B, w, hb, hnz, hx⟩ := exists_triangular_compact x
  let s (i : Fin n) := signReal (a i)
  let D := Matrix.diagonal s
  have htri : (D * B).IsUpperTriangular := (blockTriangular_diagonal s).mul hb
  have hs (i : Fin n) : s i ≠ 0 := by
    intro hzero
    simpa [show signReal (a i) = 0 from hzero] using abs_signReal (a i)
  have hDB (i : Fin n) : (D * B) i i ≠ 0 := by
    change (Matrix.diagonal s * B) i i ≠ 0
    rw [Matrix.diagonal_mul]
    exact mul_ne_zero (hs i) (hnz i)
  have hsig : signDiagonal (fun i => (D * B) i i) =
      signDiagonal (fun i => (a i : ℝ)) * signDiagonal (fun i => B i i) := by
    apply Subtype.ext
    change (Matrix.diagonal fun i => signReal ((Matrix.diagonal s * B) i i)) =
      Matrix.diagonal s * (Matrix.diagonal fun i => signReal (B i i))
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    rw [Matrix.diagonal_mul, signReal_mul (hs i) (hnz i)]
    have hi : signReal (s i) = s i := by
      by_cases ha : 0 < (a i : ℝ) <;> norm_num [s, signReal, ha]
    rw [hi]
  have hDx : ((Unitary.toUnits (signDiagonal (fun i => (a i : ℝ))) * x : G n) : Mat n) =
      (D * B) * (w : Mat n) := by
    change D * (x : Mat n) = _
    rw [hx, mul_assoc]
  rw [signedOrthogonalPart_eq htri hDB hDx, hsig,
    signedOrthogonalPart_eq hb hnz hx, mul_assoc]

end Modulus

section SignAverage

variable {n : ℕ}

private abbrev SignChoices (n : ℕ) := Fin n → Fin 2

private def signs (ε : SignChoices n) : K n :=
  signDiagonal (fun i => (-1 : ℝ) ^ (ε i).val)

private theorem signs_val (ε : SignChoices n) :
    (signs ε : Mat n) = Matrix.diagonal (fun i => (-1 : ℝ) ^ (ε i).val) := by
  change Matrix.diagonal (fun i => signReal ((-1 : ℝ) ^ (ε i).val)) = _
  congr 1
  funext i
  generalize ε i = j
  fin_cases j <;> norm_num [signReal]

private theorem signs_mul (ε δ : SignChoices n) :
    signs (ε + δ) = signs ε * signs δ := by
  apply Subtype.ext
  simp only [Submonoid.coe_mul, signs_val, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  change (-1 : ℝ) ^ (ε i + δ i).val = (-1 : ℝ) ^ (ε i).val * (-1 : ℝ) ^ (δ i).val
  generalize ε i = e
  generalize δ i = d
  fin_cases e <;> fin_cases d <;> norm_num [Fin.val_add_eq_ite]

private theorem exists_signs_eq_signDiagonal (a : Fin n → ℝˣ) :
    ∃ ε : SignChoices n, signs ε = signDiagonal (fun i => (a i : ℝ)) := by
  refine ⟨fun i => if 0 < (a i : ℝ) then 0 else 1, ?_⟩
  apply Subtype.ext
  rw [signs_val]
  change Matrix.diagonal (fun i => (-1 : ℝ) ^
    (if 0 < (a i : ℝ) then (0 : Fin 2) else 1).val) =
    Matrix.diagonal (fun i => signReal (a i))
  congr 1
  funext i
  by_cases ha : 0 < (a i : ℝ) <;> simp [signReal, ha]

private def signAverage (φ : K n → ℂ) (k : K n) : ℂ :=
  ((Fintype.card (SignChoices n) : ℂ))⁻¹ * ∑ ε : SignChoices n, φ (signs ε * k)

private theorem signAverage_invariant (φ : K n → ℂ) (a : Fin n → ℝˣ) (k : K n) :
    signAverage φ (signDiagonal (fun i => (a i : ℝ)) * k) = signAverage φ k := by
  obtain ⟨δ, hδ⟩ := exists_signs_eq_signDiagonal a
  rw [← hδ]
  unfold signAverage
  congr 1
  calc
    _ = ∑ ε : SignChoices n, φ (signs (ε + δ) * k) := by
      refine Finset.sum_congr rfl fun ε _ => ?_
      rw [signs_mul, mul_assoc]
    _ = _ := Equiv.sum_comp (Equiv.addRight δ) (fun ε => φ (signs ε * k))

private theorem exists_polynomial_of_signAverage (φ : C(K n, ℂ))
    (hφ : φ ∈ polynomialStar n) :
    ∃ P : MvPolynomial (Fin n × Fin n) ℂ, ∀ k : K n,
      signAverage φ k = MvPolynomial.eval (fun ij => ((k : Mat n) ij.1 ij.2 : ℂ)) P := by
  have hle : (polynomialStar n).toSubalgebra ≤
      (polynomialFunctions n).comap (ContinuousMap.coeFnAlgHom ℂ) := by
    rw [polynomialStar_toSubalgebra]
    refine Algebra.adjoin_le ?_
    rintro f ⟨ij, rfl⟩
    exact entry_mem_polynomialFunctions ij
  obtain ⟨P, hP⟩ := exists_mvPolynomial_of_mem_polynomialFunctions (hle hφ)
  let substSign (ε : SignChoices n) (ij : Fin n × Fin n) :
      MvPolynomial (Fin n × Fin n) ℂ :=
    MvPolynomial.C ((-1 : ℂ) ^ (ε ij.1).val) * MvPolynomial.X ij
  refine ⟨MvPolynomial.C ((Fintype.card (SignChoices n) : ℂ)⁻¹) *
    ∑ ε : SignChoices n, P.eval₂ MvPolynomial.C (substSign ε), fun k => ?_⟩
  simp only [signAverage, map_mul, MvPolynomial.eval_C, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun ε _ => ?_
  have hP' (u : K n) :
      φ u = MvPolynomial.eval (fun ij => ((u : Mat n) ij.1 ij.2 : ℂ)) P := hP u
  rw [hP', MvPolynomial.eval_eval₂]
  have hconst : (MvPolynomial.eval (fun ij => ((k : Mat n) ij.1 ij.2 : ℂ))).comp
      (MvPolynomial.C : ℂ →+* MvPolynomial (Fin n × Fin n) ℂ) = RingHom.id ℂ := by
    ext z
    simp
  rw [hconst, MvPolynomial.eval₂_id]
  have hvars :
      (fun ij : Fin n × Fin n => (((signs ε * k : K n) : Mat n) ij.1 ij.2 : ℂ)) =
      fun ij => MvPolynomial.eval (fun p => ((k : Mat n) p.1 p.2 : ℂ)) (substSign ε ij) := by
    funext ij
    simp only [Submonoid.coe_mul, signs_val, Matrix.diagonal_mul, Complex.ofReal_mul,
      Complex.ofReal_pow, Complex.ofReal_neg, Complex.ofReal_one, substSign, map_mul,
      MvPolynomial.eval_C, MvPolynomial.eval_X]
  rw [hvars]

end SignAverage

section Chart

open RealLeviParabolicIntegration (bd continuous_bd exists_blockDiagGL_eq adBd
  continuous_adBd map_adBd continuous_lower_sz)

attribute [local instance] measurableSpaceK RealLeviBlockHaar.secondCountableTopology_GL
  RealLeviBlockHaar.secondCountableTopology_O

local instance borelSpaceK (n : ℕ) : BorelSpace (unitaryCompact ℝ n) := ⟨rfl⟩

/-- The identification of the orthogonal subgroup of the invertible matrices with
the group of orthogonal matrices. -/
def compactEquiv (n : ℕ) : unitaryCompact ℝ n ≃* K n where
  toFun k := ⟨(k.1 : Mat n), k.2⟩
  invFun k := ⟨Unitary.toUnits k, k.2⟩
  left_inv _ := Subtype.ext (Units.ext rfl)
  right_inv _ := Subtype.ext rfl
  map_mul' _ _ := rfl

theorem continuous_compactEquiv (n : ℕ) : Continuous (compactEquiv n) :=
  (Units.continuous_val.comp continuous_subtype_val).subtype_mk _

/-- Normalized Haar measure on the matrix model of the compact group. -/
def compactHaar (n : ℕ) : Measure (K n) := (haarK n).map (compactEquiv n)

instance (n : ℕ) : (compactHaar n).IsHaarMeasure :=
  Measure.isHaarMeasure_map_of_isFiniteMeasure (haarK n) (compactEquiv n).toMonoidHom
    (continuous_compactEquiv n) (compactEquiv n).surjective

instance (n : ℕ) : IsProbabilityMeasure (compactHaar n) :=
  ⟨by simp [compactHaar, Measure.map_apply (continuous_compactEquiv n).measurable]⟩

section Coordinates

variable {c : ℕ} (sz : Fin c → ℕ)

abbrev LeviFrame (sz : Fin c → ℕ) := ∀ i, unitaryCompact ℝ (sz i)

local notation "N" => ∑ i, sz i
local notation "B" => LeviFrame sz
local notation "XSpace" => (Coord sz → ℝ)

/-- The frame in the compact group represented by the lower block coordinates
and a compact block diagonal factor. -/
def compactFrame (κ : B) (X : XSpace) : K N :=
  signedOrthogonalPart (lowerGL sz X * bd κ)

theorem continuous_compactFrame :
    Continuous (fun p : B × XSpace => compactFrame sz p.1 p.2) := by
  apply continuous_signedOrthogonalPart.comp
  exact ((RealLeviLimit.continuous_lowerGL (sz := sz)).comp continuous_snd).mul
    (continuous_bd.comp continuous_fst)

/-- The compact chart weight, evaluated in the opposite unipotent coordinates. -/
def chartWeight (X : XSpace) : ℂ := modulusWeight (lowerGL sz X)

theorem continuous_chartWeight : Continuous (chartWeight sz) :=
  continuous_modulusWeight.comp RealLeviLimit.continuous_lowerGL

theorem chartWeight_zero : chartWeight sz 0 = 1 := by
  rw [chartWeight, RealLeviLimit.lowerGL_zero, modulusWeight_one]

private theorem chartWeight_mul_bd (κ : B) (X : XSpace) :
    modulusWeight (lowerGL sz X * bd κ) = chartWeight sz X :=
  modulusWeight_mul_right (lowerGL sz X)
    (compactEquiv N ⟨bd κ, blockDiagGL_mem_unitaryCompact κ⟩)

private theorem integrable_chartWeight : Integrable (chartWeight sz) := by
  obtain ⟨_, _, hC⟩ := realLeviParabolicIntegration c sz
  have hs : ContMDiff (matrixModel ℝ N) 𝓘(ℝ, ℂ) ∞ (modulusWeight : G N → ℂ) :=
    contMDiff_extension (modulusExponent N) (P := 1) (φ := 1) (by intro k; simp)
  have h := (hC _ hs isModulusCovariant_modulusWeight).1 (1 : B)
  exact h.congr (ae_of_all _ (chartWeight_mul_bd sz 1))

abbrev frameMeasure : Measure B := Measure.pi fun i => haarK (sz i)

abbrev chartMeasure : Measure (B × XSpace) :=
  Measure.prod (frameMeasure sz) volume

private def chartIntegrand (φ : C(K N, ℂ)) (p : B × XSpace) : ℂ :=
  chartWeight sz p.2 * φ (compactFrame sz p.1 p.2)

private theorem continuous_chartIntegrand (φ : C(K N, ℂ)) :
    Continuous (chartIntegrand sz φ) :=
  ((continuous_chartWeight sz).comp continuous_snd).mul
    (φ.continuous.comp (continuous_compactFrame sz))

private theorem integrable_chartIntegrand (φ : C(K N, ℂ)) :
    Integrable (chartIntegrand sz φ) (chartMeasure sz) := by
  refine (((integrable_chartWeight sz).norm.comp_snd (frameMeasure sz)).mul_const ‖φ‖).mono'
    (continuous_chartIntegrand sz φ).aestronglyMeasurable (ae_of_all _ fun p => ?_)
  rw [chartIntegrand, norm_mul]
  exact mul_le_mul_of_nonneg_left (φ.norm_coe_le_norm _) (norm_nonneg _)

private theorem sign_blockOrth (a : Fin N → ℝˣ) :
    Unitary.toUnits (signDiagonal (fun i => (a i : ℝ))) ∈ blockOrth sz := by
  apply mem_blockOrth_of_mem_unitaryCompact (signDiagonal (fun i => (a i : ℝ))).2
  intro i j hij
  change (Matrix.diagonal fun i => signReal (a i)) i j = 0
  exact Matrix.diagonal_apply_ne _ (fun h => hij (h ▸ rfl))

set_option maxHeartbeats 400000 in
private theorem chart_integral_mul_sign (a : Fin N → ℝˣ) (φ : C(K N, ℂ)) :
    (∫ p : B × XSpace,
      chartWeight sz p.2 * φ (signDiagonal (fun i => (a i : ℝ)) * compactFrame sz p.1 p.2)
      ∂chartMeasure sz) = ∫ p, chartIntegrand sz φ p ∂chartMeasure sz := by
  let s := signDiagonal (fun i => (a i : ℝ))
  obtain ⟨τ, hτ⟩ := exists_blockDiagGL_eq (sign_blockOrth sz a)
  change bd τ = Unitary.toUnits s at hτ
  have hmul (κ : B) : bd (τ * κ) = Unitary.toUnits s * bd κ := by
    rw [← hτ]
    exact map_mul (blockDiagGL sz) (fun i => (τ i : G (sz i))) (fun i => (κ i : G (sz i)))
  have hcoord (X : XSpace) :
      lowerGL sz (adBd τ X) * Unitary.toUnits s = Unitary.toUnits s * lowerGL sz X := by
    rw [← hτ]
    exact (mul_lowerGL (blockDiagGL_mem_blockOrth τ) X).symm
  have hW (X : XSpace) : chartWeight sz (adBd τ X) = chartWeight sz X := by
    change modulusWeight (lowerGL sz (adBd τ X)) = modulusWeight (lowerGL sz X)
    rw [← modulusWeight_mul_right (lowerGL sz (adBd τ X)) s, hcoord, modulusWeight_mul_sign]
  have heq (κ : B) (X : XSpace) :
      compactFrame sz (τ * κ) (adBd τ X) = s * compactFrame sz κ X := by
    unfold compactFrame
    rw [hmul, ← mul_assoc, hcoord, mul_assoc, orthogonalPart_mul_sign]
  let Φ : B × XSpace → B × XSpace := Prod.map (fun κ => τ * κ) (adBd τ)
  have hpres : MeasurePreserving Φ (chartMeasure sz) (chartMeasure sz) :=
    (measurePreserving_mul_left (frameMeasure sz) τ).prod
      (measurePreserving_adCoord (blockDiagGL_mem_blockOrth τ))
  calc
    _ = ∫ p, chartIntegrand sz φ (Φ p) ∂chartMeasure sz := by
      refine integral_congr_ae (ae_of_all _ fun p => ?_)
      change chartWeight sz p.2 * φ (s * compactFrame sz p.1 p.2) =
        chartWeight sz (adBd τ p.2) * φ (compactFrame sz (τ * p.1) (adBd τ p.2))
      rw [hW, heq]
    _ = ∫ p, chartIntegrand sz φ p ∂Measure.map Φ (chartMeasure sz) :=
      (integral_map hpres.measurable.aemeasurable
        (continuous_chartIntegrand sz φ).aestronglyMeasurable).symm
    _ = _ := by rw [hpres.map_eq]

private theorem integral_signAverage {n : ℕ} (φ : C(K n, ℂ)) :
    (∫ k, signAverage φ k ∂compactHaar n) = ∫ k, φ k ∂compactHaar n := by
  unfold signAverage
  rw [integral_const_mul, integral_finsetSum]
  · simp_rw [integral_mul_left_eq_self (fun k => φ k)]
    rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, ← mul_assoc, inv_mul_cancel₀, one_mul]
    exact_mod_cast Fintype.card_ne_zero
  · intro ε _
    exact OrthogonalFinitePolynomial.integrable_of_continuous (compactHaar n)
      (φ.continuous.comp (continuous_const.mul continuous_id))

private theorem continuous_signAverage {n : ℕ} (φ : C(K n, ℂ)) : Continuous (signAverage φ) :=
  continuous_const.mul (continuous_finsetSum _ fun _ _ =>
    φ.continuous.comp (continuous_const.mul continuous_id))

private theorem chart_integral_signAverage (φ : C(K N, ℂ)) :
    (∫ p : B × XSpace, chartWeight sz p.2 * signAverage φ (compactFrame sz p.1 p.2)
      ∂chartMeasure sz) = ∫ p, chartIntegrand sz φ p ∂chartMeasure sz := by
  have hi (ε : SignChoices N) :
      Integrable (fun p : B × XSpace =>
        chartWeight sz p.2 * φ (signs ε * compactFrame sz p.1 p.2)) (chartMeasure sz) :=
    integrable_chartIntegrand sz
      ⟨fun k => φ (signs ε * k), φ.continuous.comp (continuous_const.mul continuous_id)⟩
  have hsum (p : B × XSpace) :
      chartWeight sz p.2 * signAverage φ (compactFrame sz p.1 p.2) =
        ((Fintype.card (SignChoices N) : ℂ))⁻¹ * ∑ ε : SignChoices N,
          chartWeight sz p.2 * φ (signs ε * compactFrame sz p.1 p.2) := by
    unfold signAverage
    rw [mul_left_comm (chartWeight sz p.2)]
    congr 1
    exact Finset.mul_sum ..
  simp_rw [hsum]
  rw [integral_const_mul, integral_finsetSum _ (fun ε _ => hi ε)]
  have he (ε : SignChoices N) :
      (∫ p : B × XSpace, chartWeight sz p.2 * φ (signs ε * compactFrame sz p.1 p.2)
        ∂chartMeasure sz) = ∫ p, chartIntegrand sz φ p ∂chartMeasure sz := by
    have hs : signs ε =
        signDiagonal (fun i => (((-1 : ℝˣ) ^ (ε i).val : ℝˣ) : ℝ)) := by
      simp [signs]
    rw [hs]
    exact chart_integral_mul_sign sz _ φ
  simp_rw [he]
  rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, ← mul_assoc, inv_mul_cancel₀, one_mul]
  exact_mod_cast Fintype.card_ne_zero

private theorem continuous_chartIntegral :
    Continuous (fun φ : C(K N, ℂ) => ∫ p, chartIntegrand sz φ p ∂chartMeasure sz) := by
  let L : C(K N, ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun φ => ∫ p, chartIntegrand sz φ p ∂chartMeasure sz
      map_add' := fun φ ψ => by
        simp only [chartIntegrand, ContinuousMap.add_apply, mul_add]
        exact integral_add (integrable_chartIntegrand sz φ) (integrable_chartIntegrand sz ψ)
      map_smul' := fun a φ => by
        simp only [chartIntegrand, ContinuousMap.smul_apply, smul_eq_mul, RingHom.id_apply,
          mul_left_comm (chartWeight sz _), integral_const_mul] }
  let C := ∫ p : B × XSpace, ‖chartWeight sz p.2‖ ∂chartMeasure sz
  have hL (φ : C(K N, ℂ)) : ‖L φ‖ ≤ C * ‖φ‖ := by
    have hi := (integrable_chartWeight sz).norm.comp_snd (frameMeasure sz)
    calc
      ‖L φ‖ ≤ ∫ p : B × XSpace, ‖chartWeight sz p.2‖ * ‖φ‖ ∂chartMeasure sz := by
        apply norm_integral_le_of_norm_le (hi.mul_const ‖φ‖)
        exact ae_of_all _ fun p => by
          rw [chartIntegrand, norm_mul]
          exact mul_le_mul_of_nonneg_left (φ.norm_coe_le_norm _) (norm_nonneg _)
      _ = _ := integral_mul_const _ _
  exact (L.mkContinuous C hL).continuous

private theorem continuous_compactIntegral (n : ℕ) :
    Continuous (fun φ : C(K n, ℂ) => ∫ k, φ k ∂compactHaar n) := by
  let μ := compactHaar n
  let J := ContinuousMap.toLp (E := ℂ) 1 μ ℂ
  have h : (fun φ : C(K n, ℂ) => ∫ k, φ k ∂μ) =
      (fun F : Lp ℂ 1 μ => ∫ k, F k ∂μ) ∘ J := by
    funext φ
    exact (integral_congr_ae (ContinuousMap.coeFn_toLp (E := ℂ) (p := 1) (𝕜 := ℂ)
      μ φ)).symm
  exact h ▸ continuous_integral.comp J.continuous

end Coordinates

/-- Normalized orthogonal Haar integration of an arbitrary continuous test
in opposed block coordinates, with continuous weight equal to one at zero. -/
def RealLeviCompactChartStatement : Prop :=
  ∀ (c : ℕ) (sz : Fin c → ℕ), ∃ C : ℝ, 0 < C ∧
    ∀ φ : C(K (∑ i, sz i), ℂ),
      ∫ k, φ k ∂compactHaar (∑ i, sz i) =
        (C : ℂ) * ∫ p : LeviFrame sz × (Coord sz → ℝ),
          chartWeight sz p.2 * φ (compactFrame sz p.1 p.2) ∂chartMeasure sz

set_option maxHeartbeats 1000000 in
theorem realLeviCompactChart : RealLeviCompactChartStatement := by
  intro c sz
  let N := ∑ i, sz i
  change ∃ C : ℝ, 0 < C ∧ ∀ φ : C(K N, ℂ), _
  obtain ⟨C, hCpos, hC⟩ := realLeviParabolicIntegration c sz
  refine ⟨C, hCpos, ?_⟩
  have hdense : Dense (polynomialStar N : Set C(K N, ℂ)) := by
    rw [dense_iff_closure_eq, ← StarSubalgebra.topologicalClosure_coe,
      ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints
        _ polynomialStar_separatesPoints, StarSubalgebra.coe_top]
  have hright : Continuous (fun φ : C(K N, ℂ) =>
      (C : ℂ) * ∫ p, chartIntegrand sz φ p ∂chartMeasure sz) :=
    continuous_const.mul (continuous_chartIntegral sz)
  refine fun φ₀ => congrFun (Continuous.ext_on hdense (continuous_compactIntegral N)
    hright ?_) φ₀
  intro φ hφ
  let avg : C(K N, ℂ) := ⟨signAverage φ, continuous_signAverage φ⟩
  obtain ⟨P, hP⟩ := exists_polynomial_of_signAverage φ hφ
  let F := extension (modulusExponent N) (avg : K N → ℂ)
  have hFs : ContMDiff (matrixModel ℝ N) 𝓘(ℝ, ℂ) ∞ F :=
    contMDiff_extension _ hP
  have hFm : IsModulusCovariant F :=
    isModulusCovariant_extension (signAverage_invariant φ)
  have h := (hC F hFs hFm).2
  have hrestrict (k : unitaryCompact ℝ N) : F k.1 = avg (compactEquiv N k) := by
    change extension (modulusExponent N) avg (Unitary.toUnits (compactEquiv N k)) = _
    exact extension_unitary _ _ _
  have hchart (κ : LeviFrame sz) (X : Coord sz → ℝ) :
      F (lowerGL sz X * RealLeviParabolicIntegration.bd κ) = chartIntegrand sz avg (κ, X) := by
    have hsplit (g : G N) : F g = modulusWeight g * avg (signedOrthogonalPart g) := by
      simp [F, extension, modulusWeight]
    rw [hsplit, chartWeight_mul_bd]
    rfl
  calc
    _ = ∫ k, avg k ∂compactHaar N := (integral_signAverage φ).symm
    _ = ∫ k : unitaryCompact ℝ N, F k.1 ∂haarK N := by
      rw [compactHaar, integral_map (continuous_compactEquiv N).measurable.aemeasurable
        avg.continuous.aestronglyMeasurable]
      exact integral_congr_ae (ae_of_all _ fun k => (hrestrict k).symm)
    _ = (C : ℂ) * ∫ κ : LeviFrame sz, (∫ X : Coord sz → ℝ, chartIntegrand sz avg (κ, X))
        ∂frameMeasure sz := by simpa only [hchart] using h
    _ = (C : ℂ) * ∫ p, chartIntegrand sz avg p ∂chartMeasure sz := by
      rw [integral_prod _ (integrable_chartIntegrand sz avg)]
    _ = _ := congrArg (fun z => (C : ℂ) * z) (chart_integral_signAverage sz φ)

end Chart

end Langlands.Archimedean.RealLeviCompactChart
