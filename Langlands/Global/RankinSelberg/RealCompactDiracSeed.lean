import Langlands.Global.RankinSelberg.RealCompactDiracTransfer

/-!
# A compact-finite seed vector concentrated on the big cell

For exponents `p : ℕ → ℕ` (the parities of the inducing characters) and `m : ℕ`, the seed
profile on `O(n)` is

`φ₀(κ) = ∏ₗ (Δₗ(κ) Δₗ₊₁(κ))^{p l} · (∏ₗ Δₗ(κ))^{2m}`,

with `Δₗ = corner · l` the lower-right corner minors. It is the restriction to `O(n)` of a
product of minors, so it is compact-finite; under left multiplication by a diagonal sign
matrix `diag(σ)` it changes by `∏ₗ σₗ^{p l}`, which is the sign character when
`χₗ(-1) = (-1)^{p l}`. Its extension is a compact-finite vector of the smooth principal series.

The seed profile is used in the module `RealCompactDiracWeight`, which defines the weight
`weight` on `O(n)` and proves that its integral has positive real part for sufficiently large
`m` (`exists_re_integral_weight_pos`).
-/

noncomputable section

open Matrix Filter Topology MeasureTheory
open scoped Matrix.Norms.Operator ContDiff Manifold

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealCompactDirac

open Langlands.Archimedean Langlands.GeneralLinear Langlands.LocalFactor.Archimedean
open PrincipalSeriesExtension GramFormula RealPrincipalSeriesDuality PartialJacquet
open RealPrincipalSeriesHilbert OrthogonalFinitePolynomial RealTiedMinorProduct MatrixMinor

variable {n : ℕ}

local notation "G" => Langlands.GeneralLinear n ℝ
local notation "Mat" => Matrix (Fin n) (Fin n) ℝ
local notation "O" => Matrix.unitaryGroup (Fin n) ℝ

/-! ## The seed as a product of minors -/

/-- The product `∏ₗ (Δₗ Δₗ₊₁)^{p l}` of corner minors carrying the sign character. -/
def signPart (p : ℕ → ℕ) (X : Mat) : ℝ := ∏ l : Fin n, (corner X l * corner X (l + 1)) ^ p l

/-- The product `∏ₗ Δₗ` of all corner minors; it vanishes exactly off the big cell. -/
def cornerProduct (X : Mat) : ℝ := ∏ l : Fin n, corner X l

/-- The seed profile `∏ₗ (Δₗ Δₗ₊₁)^{p l} (∏ₗ Δₗ)^{2m}`, as a real function of a matrix. -/
def seedReal (p : ℕ → ℕ) (m : ℕ) (X : Mat) : ℝ := signPart p X * cornerProduct X ^ (2 * m)

/-- The seed as a function on `GL_n(ℝ)`. -/
def seedFunction (p : ℕ → ℕ) (m : ℕ) (g : G) : ℂ := (seedReal p m (g : Mat) : ℂ)

/-- The seed profile on `O(n)`. -/
def seedProfile (p : ℕ → ℕ) (m : ℕ) (κ : O) : ℂ := (seedReal p m (κ : Mat) : ℂ)

theorem seedProfile_eq (p : ℕ → ℕ) (m : ℕ) (κ : O) :
    seedProfile p m κ = seedFunction p m (Unitary.toUnits κ) := rfl

theorem one_mem_kFiniteVectors :
    (1 : G → ℂ) ∈ kFiniteVectors (Whittaker.rightTranslation ℂ G) (unitaryCompact ℝ n) := by
  rw [mem_kFiniteVectors_iff]
  have h : (Set.range fun k : unitaryCompact ℝ n =>
      Whittaker.rightTranslation ℂ G (k : G) (1 : G → ℂ)) ⊆ {1} := by
    rintro _ ⟨k, rfl⟩
    rfl
  exact Submodule.finiteDimensional_of_le (Submodule.span_mono h)

theorem prod_mem_kFiniteVectors {ι : Type*} (s : Finset ι) (f : ι → G → ℂ)
    (hf : ∀ i ∈ s, f i ∈ kFiniteVectors (Whittaker.rightTranslation ℂ G) (unitaryCompact ℝ n)) :
    (∏ i ∈ s, f i) ∈ kFiniteVectors (Whittaker.rightTranslation ℂ G) (unitaryCompact ℝ n) :=
  Finset.prod_induction _ _ (fun _ _ ha hb => mul_mem_kFiniteVectors ha hb)
    one_mem_kFiniteVectors hf

theorem pow_mem_kFiniteVectors {f : G → ℂ}
    (hf : f ∈ kFiniteVectors (Whittaker.rightTranslation ℂ G) (unitaryCompact ℝ n)) (k : ℕ) :
    f ^ k ∈ kFiniteVectors (Whittaker.rightTranslation ℂ G) (unitaryCompact ℝ n) := by
  induction k with
  | zero => simpa using one_mem_kFiniteVectors
  | succ k ih => simpa [pow_succ] using mul_mem_kFiniteVectors ih hf

theorem seedFunction_eq (p : ℕ → ℕ) (m : ℕ) :
    seedFunction (n := n) p m =
      (∏ l : Fin n, (minorG (tail n l) (tail n l) * minorG (tail n (l + 1)) (tail n (l + 1)))
        ^ p l) * (∏ l : Fin n, minorG (tail n l) (tail n l)) ^ (2 * m) := by
  funext g
  simp only [seedFunction, seedReal, signPart, cornerProduct, corner, Pi.mul_apply,
    Finset.prod_apply, Pi.pow_apply, minorG]
  push_cast
  rfl

theorem seedFunction_mem_kFiniteVectors (p : ℕ → ℕ) (m : ℕ) :
    seedFunction (n := n) p m ∈
      kFiniteVectors (Whittaker.rightTranslation ℂ G) (unitaryCompact ℝ n) := by
  rw [seedFunction_eq]
  refine mul_mem_kFiniteVectors (prod_mem_kFiniteVectors _ _ fun l _ => ?_)
    (pow_mem_kFiniteVectors (prod_mem_kFiniteVectors _ _ fun l _ =>
      minorG_mem_kFiniteVectors _ _) _)
  exact pow_mem_kFiniteVectors
    (mul_mem_kFiniteVectors (minorG_mem_kFiniteVectors _ _) (minorG_mem_kFiniteVectors _ _)) _

theorem continuous_seedReal (p : ℕ → ℕ) (m : ℕ) : Continuous (seedReal (n := n) p m) := by
  have hc : ∀ l : ℕ, Continuous fun X : Mat => corner X l := fun l =>
    continuous_minor (tail n l) (tail n l)
  unfold seedReal signPart cornerProduct
  fun_prop

theorem continuous_seedProfile (p : ℕ → ℕ) (m : ℕ) : Continuous (seedProfile (n := n) p m) :=
  Complex.continuous_ofReal.comp ((continuous_seedReal p m).comp continuous_subtype_val)

theorem finiteDimensional_seedProfile (p : ℕ → ℕ) (m : ℕ) :
    FiniteDimensional ℂ (Submodule.span ℂ
      (Set.range fun k : O => fun x => seedProfile (n := n) p m (x * k))) := by
  have h := finiteDimensional_restrict (seedFunction_mem_kFiniteVectors (n := n) p m)
  simpa only [seedProfile_eq] using h

/-! ## Sign covariance -/

theorem signReal_sq_eq_one (x : ℝ) : signReal x ^ 2 = 1 := by
  unfold signReal
  split_ifs <;> norm_num

theorem prod_signReal_sq (σ : Fin n → ℝ) (S : Finset (Fin n)) :
    (∏ i ∈ S, signReal (σ i)) ^ 2 = 1 := by
  rw [← Finset.prod_pow]
  exact Finset.prod_eq_one fun i _ => signReal_sq_eq_one _

theorem seedReal_signDiagonal (p : ℕ → ℕ) (m : ℕ) (d : Fin n → ℝ) (X : Mat) :
    seedReal p m (Matrix.diagonal (fun i => signReal (d i)) * X) =
      (∏ l : Fin n, signReal (d l) ^ p l) * seedReal p m X := by
  set τ : ℕ → ℝ := fun l => ∏ i ∈ tail n l, signReal (d i) with hτ
  have hc : ∀ l : ℕ, corner (Matrix.diagonal (fun i => signReal (d i)) * X) l = τ l * corner X l :=
    fun l => corner_diagonal_mul _ X l
  have hττ : ∀ l : Fin n, τ l * τ (l + 1) = signReal (d l) := by
    intro l
    have hins : τ l = signReal (d l) * τ (l + 1) := by
      simp only [hτ]
      rw [tail_eq_insert l.2, Finset.prod_insert (notMem_tail_succ l.2)]
    rw [hins, mul_assoc, ← sq, prod_signReal_sq, mul_one]
  unfold seedReal signPart cornerProduct
  simp only [hc]
  have h1 : ∏ l : Fin n, (τ l * corner X l * (τ (l + 1) * corner X (l + 1))) ^ p l =
      (∏ l : Fin n, signReal (d l) ^ p l) *
        ∏ l : Fin n, (corner X l * corner X (l + 1)) ^ p l := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun l _ => ?_
    rw [← mul_pow, ← hττ l]
    ring
  have h2 : (∏ l : Fin n, τ l * corner X l) ^ (2 * m) = (∏ l : Fin n, corner X l) ^ (2 * m) := by
    rw [Finset.prod_mul_distrib, mul_pow, pow_mul (∏ l : Fin n, τ l)]
    have : (∏ l : Fin n, τ l) ^ 2 = 1 := by
      rw [← Finset.prod_pow]
      refine Finset.prod_eq_one fun l _ => ?_
      exact prod_signReal_sq _ _
    rw [this, one_pow, one_mul]
  rw [h1, h2]
  ring

theorem char_signUnit {χ : ℕ → ℝˣ → ℂ} {p : ℕ → ℕ} (hχ1 : ∀ l, χ l 1 = 1)
    (hp : ∀ l, χ l (-1) = (-1) ^ p l) (l : ℕ) (x : ℝˣ) :
    χ l (signUnit x) = ((signReal x ^ p l : ℝ) : ℂ) := by
  unfold signUnit signReal
  split_ifs
  · rw [hχ1]
    simp
  · rw [hp]
    push_cast
    rfl

theorem principalSeriesCharacter_signUnit {χ : ℕ → ℝˣ → ℂ} {p : ℕ → ℕ} (hχ1 : ∀ l, χ l 1 = 1)
    (hp : ∀ l, χ l (-1) = (-1) ^ p l) (a : Fin n → ℝˣ) :
    principalSeriesCharacter ℝ n χ (fun i => signUnit (a i)) =
      ((∏ l : Fin n, signReal (a l) ^ p l : ℝ) : ℂ) := by
  unfold principalSeriesCharacter
  push_cast
  refine Finset.prod_congr rfl fun l _ => ?_
  rw [char_signUnit hχ1 hp]
  have h1 : ‖((signUnit (a l) : ℝˣ) : ℝ)‖ = 1 := by
    rw [Real.norm_eq_abs, signUnit_val, abs_signReal]
  rw [h1]
  simp

/-- **Sign covariance of the seed profile.** -/
theorem seedProfile_signDiagonal {χ : ℕ → ℝˣ → ℂ} {p : ℕ → ℕ} (m : ℕ) (hχ1 : ∀ l, χ l 1 = 1)
    (hp : ∀ l, χ l (-1) = (-1) ^ p l) (a : Fin n → ℝˣ) (κ : O) :
    seedProfile p m (signDiagonal (fun i => (a i : ℝ)) * κ) =
      principalSeriesCharacter ℝ n χ (fun i => signUnit (a i)) * seedProfile p m κ := by
  rw [principalSeriesCharacter_signUnit hχ1 hp]
  unfold seedProfile
  have hval : ((signDiagonal (fun i => (a i : ℝ)) * κ : O) : Mat) =
      Matrix.diagonal (fun i => signReal (a i : ℝ)) * (κ : Mat) := rfl
  rw [hval, seedReal_signDiagonal]
  push_cast
  ring

/-! ## The seed vector -/

/-- The seed vector: the extension of the seed profile with the exponents `e`. -/
def seedVector (p : ℕ → ℕ) (m : ℕ) (e : ℕ → ℂ) : G → ℂ :=
  extension (shiftedExponent n e) (seedProfile p m)

theorem seedVector_mem {χ : ℕ → ℝˣ → ℂ} {e : ℕ → ℂ} (hχ : IsSignedPower χ e) {p : ℕ → ℕ}
    (hp : ∀ l, χ l (-1) = (-1) ^ p l) (m : ℕ) :
    seedVector (n := n) p m e ∈ kFiniteFunctions (principalSeries ℝ n χ) (unitaryCompact ℝ n) :=
  extension_mem_kFiniteFunctions e hχ.eq (continuous_seedProfile p m)
    (finiteDimensional_seedProfile p m) fun a κ => seedProfile_signDiagonal m hχ.one hp a κ

theorem seedVector_unitary (p : ℕ → ℕ) (m : ℕ) (e : ℕ → ℂ) (κ : O) :
    seedVector p m e (Unitary.toUnits κ) = seedProfile p m κ :=
  extension_unitary _ _ _


end Langlands.Global.RankinSelbergGlobal.RealCompactDirac
