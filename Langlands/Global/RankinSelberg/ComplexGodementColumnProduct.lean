import Langlands.Global.RankinSelberg.ArchimedeanIntegrals
import Langlands.HarmonicAnalysis.RectangularFourier
import Langlands.LocalFactor.ArchimedeanScaling
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.Matrix.Normed
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Fourier transforms of column-product tests (Jacquet 2009, (8.3)–(8.4))

For an `m × (m+1)` complex matrix `X`, `leadingColumns X` is the square matrix of its first `m`
columns and `lastColumn X` its last column. For a square Schwartz test `Φ` and a vector Schwartz
test `φ`, `columnProduct Φ φ` is the Schwartz test `X ↦ Φ (leadingColumns X) * φ (lastColumn X)`.
`ComplexColumnProductFourierStatement` says that its full matrix Fourier transform is the
product of the square Fourier transform of `Φ` and the vector Fourier transform of `φ`, for the
self-dual measure of `ψ_a`. See the paired Markdown.
-/

noncomputable section

open MeasureTheory
open scoped SchwartzMap Matrix.Norms.Operator ContDiff

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexGodementColumnProduct

open ArchimedeanLocal Langlands.LocalFactor.Archimedean
open Langlands.HarmonicAnalysis (rectangularFourierIntegral rectangularPairing
  UnitaryAdditiveCharacter AdditiveHaarMeasure)
open Langlands.RankinSelberg (rectangularMeasure)

/-! ### A Schwartz product along two linear maps -/

section Product

variable {D E₁ E₂ : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]

theorem norm_iteratedFDeriv_comp_le (f : 𝓢(E₁, ℂ)) (L : D →L[ℝ] E₁) (x : D) (i : ℕ) :
    ‖iteratedFDeriv ℝ i (fun y => f (L y)) x‖ ≤ ‖iteratedFDeriv ℝ i f (L x)‖ * ‖L‖ ^ i := by
  change ‖iteratedFDeriv ℝ i (f ∘ L) x‖ ≤ _
  rw [L.iteratedFDeriv_comp_right (f.smooth ⊤) x (by exact_mod_cast le_top)]
  refine ((iteratedFDeriv ℝ i f (L x)).norm_compContinuousLinearMap_le (fun _ => L)).trans ?_
  simp [Finset.prod_const]

theorem exists_one_add_pow_mul_le (f : 𝓢(E₁, ℂ)) (k n : ℕ) :
    ∃ S : ℝ, 0 ≤ S ∧ ∀ i ≤ n, ∀ y : E₁, (1 + ‖y‖) ^ k * ‖iteratedFDeriv ℝ i f y‖ ≤ S :=
  ⟨2 ^ k * (Finset.Iic (k, n)).sup (fun p : ℕ × ℕ => SchwartzMap.seminorm ℝ p.1 p.2) f,
    mul_nonneg (by positivity) (apply_nonneg _ _),
    fun i hi y => SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (k, n)) le_rfl hi f y⟩

/-- The product `x ↦ f₁ (L₁ x) * f₂ (L₂ x)` of two Schwartz functions along continuous linear maps
`L₁` and `L₂` whose norms jointly control the norm of `x`, as a Schwartz function. -/
def schwartzProd (L₁ : D →L[ℝ] E₁) (L₂ : D →L[ℝ] E₂) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ x, ‖x‖ ≤ C * (‖L₁ x‖ + ‖L₂ x‖)) (f₁ : 𝓢(E₁, ℂ)) (f₂ : 𝓢(E₂, ℂ)) : 𝓢(D, ℂ) where
  toFun x := f₁ (L₁ x) * f₂ (L₂ x)
  smooth' := ((f₁.smooth ⊤).comp L₁.contDiff).mul ((f₂.smooth ⊤).comp L₂.contDiff)
  decay' k n := by
    obtain ⟨S₁, hS₁0, hS₁⟩ := exists_one_add_pow_mul_le f₁ k n
    obtain ⟨S₂, hS₂0, hS₂⟩ := exists_one_add_pow_mul_le f₂ k n
    refine ⟨C ^ k * ∑ i ∈ Finset.range (n + 1),
      (n.choose i : ℝ) * (S₁ * ‖L₁‖ ^ i) * (S₂ * ‖L₂‖ ^ (n - i)), fun x => ?_⟩
    have hx : ‖x‖ ^ k ≤ C ^ k * ((1 + ‖L₁ x‖) ^ k * (1 + ‖L₂ x‖) ^ k) := by
      have h1 : ‖x‖ ≤ C * ((1 + ‖L₁ x‖) * (1 + ‖L₂ x‖)) :=
        (hC x).trans (mul_le_mul_of_nonneg_left
          (by nlinarith [norm_nonneg (L₁ x), norm_nonneg (L₂ x)]) hC0)
      calc ‖x‖ ^ k ≤ (C * ((1 + ‖L₁ x‖) * (1 + ‖L₂ x‖))) ^ k :=
            pow_le_pow_left₀ (norm_nonneg _) h1 k
        _ = _ := by rw [mul_pow, mul_pow]
    have hderiv := norm_iteratedFDeriv_mul_le (𝕜 := ℝ) ((f₁.smooth ⊤).comp L₁.contDiff)
      ((f₂.smooth ⊤).comp L₂.contDiff) x (n := n) (by exact_mod_cast le_top)
    calc ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (fun x => f₁ (L₁ x) * f₂ (L₂ x)) x‖
        ≤ (C ^ k * ((1 + ‖L₁ x‖) ^ k * (1 + ‖L₂ x‖) ^ k)) *
          ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
            ‖iteratedFDeriv ℝ i (fun y => f₁ (L₁ y)) x‖ *
            ‖iteratedFDeriv ℝ (n - i) (fun y => f₂ (L₂ y)) x‖ :=
          mul_le_mul hx hderiv (norm_nonneg _) (by positivity)
      _ = C ^ k * ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
            ((1 + ‖L₁ x‖) ^ k * ‖iteratedFDeriv ℝ i (fun y => f₁ (L₁ y)) x‖) *
            ((1 + ‖L₂ x‖) ^ k * ‖iteratedFDeriv ℝ (n - i) (fun y => f₂ (L₂ y)) x‖) := by
          rw [mul_assoc, Finset.mul_sum]
          congr 1
          refine Finset.sum_congr rfl fun i _ => ?_
          ring
      _ ≤ _ := by
          refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i hi => ?_) (pow_nonneg hC0 k)
          have hi' : i ≤ n := Finset.mem_range_succ_iff.mp hi
          have h1 : (1 + ‖L₁ x‖) ^ k * ‖iteratedFDeriv ℝ i (fun y => f₁ (L₁ y)) x‖ ≤
              S₁ * ‖L₁‖ ^ i :=
            calc _ ≤ (1 + ‖L₁ x‖) ^ k * (‖iteratedFDeriv ℝ i f₁ (L₁ x)‖ * ‖L₁‖ ^ i) :=
                  mul_le_mul_of_nonneg_left (norm_iteratedFDeriv_comp_le f₁ L₁ x i)
                    (by positivity)
              _ = ((1 + ‖L₁ x‖) ^ k * ‖iteratedFDeriv ℝ i f₁ (L₁ x)‖) * ‖L₁‖ ^ i := by ring
              _ ≤ S₁ * ‖L₁‖ ^ i :=
                  mul_le_mul_of_nonneg_right (hS₁ i hi' (L₁ x)) (by positivity)
          have h2 : (1 + ‖L₂ x‖) ^ k * ‖iteratedFDeriv ℝ (n - i) (fun y => f₂ (L₂ y)) x‖ ≤
              S₂ * ‖L₂‖ ^ (n - i) :=
            calc _ ≤ (1 + ‖L₂ x‖) ^ k *
                  (‖iteratedFDeriv ℝ (n - i) f₂ (L₂ x)‖ * ‖L₂‖ ^ (n - i)) :=
                  mul_le_mul_of_nonneg_left (norm_iteratedFDeriv_comp_le f₂ L₂ x (n - i))
                    (by positivity)
              _ = ((1 + ‖L₂ x‖) ^ k * ‖iteratedFDeriv ℝ (n - i) f₂ (L₂ x)‖) *
                  ‖L₂‖ ^ (n - i) := by ring
              _ ≤ S₂ * ‖L₂‖ ^ (n - i) :=
                  mul_le_mul_of_nonneg_right (hS₂ (n - i) (Nat.sub_le n i) (L₂ x))
                    (by positivity)
          exact mul_le_mul (mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg _)) h2
            (by positivity) (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg hS₁0 (by positivity)))

@[simp] theorem schwartzProd_apply (L₁ : D →L[ℝ] E₁) (L₂ : D →L[ℝ] E₂) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ x, ‖x‖ ≤ C * (‖L₁ x‖ + ‖L₂ x‖)) (f₁ : 𝓢(E₁, ℂ)) (f₂ : 𝓢(E₂, ℂ)) (x : D) :
    schwartzProd L₁ L₂ hC0 hC f₁ f₂ x = f₁ (L₁ x) * f₂ (L₂ x) := rfl

end Product

/-! ### Leading columns and last column -/

variable {m : ℕ}

/-- The last column `X_(·, m)` of an `m × (m+1)` matrix. -/
def lastColumn (X : Matrix (Fin m) (Fin (m + 1)) ℂ) : Fin m → ℂ := fun i => X i (Fin.last m)

/-- The square matrix of the first `m` columns of an `m × (m+1)` matrix. -/
def leadingColumns (X : Matrix (Fin m) (Fin (m + 1)) ℂ) : Matrix (Fin m) (Fin m) ℂ :=
  X.submatrix id Fin.castSucc

/-- The `m × (m+1)` matrix with leading columns `S` and last column `v`. -/
def columnJoin (S : Matrix (Fin m) (Fin m) ℂ) (v : Fin m → ℂ) : Matrix (Fin m) (Fin (m + 1)) ℂ :=
  Matrix.of fun i => Fin.snoc (α := fun _ => ℂ) (S i) (v i)

@[simp] theorem leadingColumns_columnJoin (S : Matrix (Fin m) (Fin m) ℂ) (v : Fin m → ℂ) :
    leadingColumns (columnJoin S v) = S := by
  ext i j
  simp [leadingColumns, columnJoin]

@[simp] theorem lastColumn_columnJoin (S : Matrix (Fin m) (Fin m) ℂ) (v : Fin m → ℂ) :
    lastColumn (columnJoin S v) = v := by
  ext i
  simp [lastColumn, columnJoin]

@[simp] theorem columnJoin_leadingColumns_lastColumn (X : Matrix (Fin m) (Fin (m + 1)) ℂ) :
    columnJoin (leadingColumns X) (lastColumn X) = X := by
  ext i j
  refine Fin.lastCases ?_ (fun j => ?_) j <;> simp [leadingColumns, lastColumn, columnJoin]

theorem leadingColumns_neg (X : Matrix (Fin m) (Fin (m + 1)) ℂ) :
    leadingColumns (-X) = -leadingColumns X := rfl

theorem lastColumn_neg (X : Matrix (Fin m) (Fin (m + 1)) ℂ) :
    lastColumn (-X) = -lastColumn X := rfl

variable (m) in
/-- `lastColumn` as a continuous real-linear map. -/
def lastColumnCLM : Matrix (Fin m) (Fin (m + 1)) ℂ →L[ℝ] (Fin m → ℂ) :=
  LinearMap.toContinuousLinearMap
    { toFun := lastColumn, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }

variable (m) in
/-- `leadingColumns` as a continuous real-linear map. -/
def leadingColumnsCLM : Matrix (Fin m) (Fin (m + 1)) ℂ →L[ℝ] Matrix (Fin m) (Fin m) ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := leadingColumns, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }

@[simp] theorem lastColumnCLM_apply (X : Matrix (Fin m) (Fin (m + 1)) ℂ) :
    lastColumnCLM m X = lastColumn X := rfl

@[simp] theorem leadingColumnsCLM_apply (X : Matrix (Fin m) (Fin (m + 1)) ℂ) :
    leadingColumnsCLM m X = leadingColumns X := rfl

theorem columnJoin_add_columnJoin (S S' : Matrix (Fin m) (Fin m) ℂ) (v v' : Fin m → ℂ) :
    columnJoin S v + columnJoin S' v' = columnJoin (S + S') (v + v') := by
  ext i j
  refine Fin.lastCases ?_ (fun j => ?_) j <;> simp [columnJoin]

theorem columnJoin_smul (c : ℝ) (S : Matrix (Fin m) (Fin m) ℂ) (v : Fin m → ℂ) :
    c • columnJoin S v = columnJoin (c • S) (c • v) := by
  ext i j
  refine Fin.lastCases ?_ (fun j => ?_) j <;> simp [columnJoin]

variable (m) in
/-- `S ↦ columnJoin S 0` as a continuous real-linear map. -/
def leadingJoinCLM : Matrix (Fin m) (Fin m) ℂ →L[ℝ] Matrix (Fin m) (Fin (m + 1)) ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun S => columnJoin S 0
      map_add' := fun S S' => by rw [columnJoin_add_columnJoin, add_zero]
      map_smul' := fun c S => by rw [RingHom.id_apply, columnJoin_smul, smul_zero] }

variable (m) in
/-- `v ↦ columnJoin 0 v` as a continuous real-linear map. -/
def lastJoinCLM : (Fin m → ℂ) →L[ℝ] Matrix (Fin m) (Fin (m + 1)) ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => columnJoin 0 v
      map_add' := fun v v' => by rw [columnJoin_add_columnJoin, add_zero]
      map_smul' := fun c v => by rw [RingHom.id_apply, columnJoin_smul, smul_zero] }

theorem norm_le_columnJoin (X : Matrix (Fin m) (Fin (m + 1)) ℂ) :
    ‖X‖ ≤ (‖leadingJoinCLM m‖ + ‖lastJoinCLM m‖) *
      (‖leadingColumnsCLM m X‖ + ‖lastColumnCLM m X‖) := by
  have hX : leadingJoinCLM m (leadingColumns X) + lastJoinCLM m (lastColumn X) = X := by
    change columnJoin (leadingColumns X) 0 + columnJoin 0 (lastColumn X) = X
    rw [columnJoin_add_columnJoin, add_zero, zero_add, columnJoin_leadingColumns_lastColumn]
  rw [leadingColumnsCLM_apply, lastColumnCLM_apply]
  have h1 := (leadingJoinCLM m).le_opNorm (leadingColumns X)
  have h2 := (lastJoinCLM m).le_opNorm (lastColumn X)
  have hA := norm_nonneg (leadingJoinCLM m)
  have hB := norm_nonneg (lastJoinCLM m)
  have hS := norm_nonneg (leadingColumns X)
  have hv := norm_nonneg (lastColumn X)
  calc ‖X‖ = ‖leadingJoinCLM m (leadingColumns X) + lastJoinCLM m (lastColumn X)‖ := by rw [hX]
    _ ≤ ‖leadingJoinCLM m (leadingColumns X)‖ + ‖lastJoinCLM m (lastColumn X)‖ := norm_add_le _ _
    _ ≤ _ := by nlinarith

/-- The column-product test `X ↦ Φ (leadingColumns X) * φ (lastColumn X)`. -/
def columnProduct (Φ : 𝓢(Matrix (Fin m) (Fin m) ℂ, ℂ)) (φ : 𝓢(Fin m → ℂ, ℂ)) :
    𝓢(Matrix (Fin m) (Fin (m + 1)) ℂ, ℂ) :=
  schwartzProd (leadingColumnsCLM m) (lastColumnCLM m)
    (add_nonneg (norm_nonneg (leadingJoinCLM m)) (norm_nonneg (lastJoinCLM m)))
    norm_le_columnJoin Φ φ

@[simp] theorem columnProduct_apply (Φ : 𝓢(Matrix (Fin m) (Fin m) ℂ, ℂ)) (φ : 𝓢(Fin m → ℂ, ℂ))
    (X : Matrix (Fin m) (Fin (m + 1)) ℂ) :
    columnProduct Φ φ X = Φ (leadingColumns X) * φ (lastColumn X) := rfl

/-! ### The measure-preserving column split -/

variable (m) in
/-- The measurable equivalence `X ↦ (lastColumn X, leadingColumns X)`. -/
def columnSplitEquiv : Matrix (Fin m) (Fin (m + 1)) ℂ ≃ᵐ (Fin m → ℂ) × Matrix (Fin m) (Fin m) ℂ :=
  (MeasurableEquiv.piCongrRight fun _ : Fin m =>
      MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℂ) (Fin.last m)).trans
    (MeasurableEquiv.arrowProdEquivProdArrow ℂ (Fin m → ℂ) (Fin m))

theorem columnSplitEquiv_apply (X : Matrix (Fin m) (Fin (m + 1)) ℂ) :
    columnSplitEquiv m X = (lastColumn X, leadingColumns X) := by
  refine Prod.ext rfl ?_
  ext i j
  change X i ((Fin.last m).succAbove j) = X i j.castSucc
  rw [Fin.succAbove_last]

theorem measurePreserving_columnSplitEquiv (ν : Measure ℂ) [SigmaFinite ν] :
    MeasurePreserving (columnSplitEquiv m)
      (Measure.pi fun _ : Fin m => Measure.pi fun _ : Fin (m + 1) => ν)
      ((Measure.pi fun _ : Fin m => ν).prod
        (Measure.pi fun _ : Fin m => Measure.pi fun _ : Fin m => ν)) :=
  (measurePreserving_arrowProdEquivProdArrow ℂ (Fin m → ℂ) (Fin m) (fun _ => ν)
      (fun _ => Measure.pi fun _ : Fin m => ν)).comp
    (measurePreserving_pi _ _ fun _ =>
      measurePreserving_piFinSuccAbove (fun _ : Fin (m + 1) => ν) (Fin.last m))

/-! ### Fourier factorization -/

theorem rectangularPairing_eq_add (Y Z : Matrix (Fin m) (Fin (m + 1)) ℂ) :
    rectangularPairing Y Z = (∑ i, lastColumn Y i * lastColumn Z i) +
      rectangularPairing (leadingColumns Y) (leadingColumns Z) := by
  simp only [rectangularPairing, Fin.sum_univ_castSucc, Finset.sum_add_distrib, lastColumn,
    leadingColumns, Matrix.submatrix_apply, id]
  ring

/-- The raw factorization: for arbitrary functions `f₁` and `f₂`, the plus-sign rectangular Fourier
integral of `Y ↦ f₁ (leadingColumns Y) * f₂ (lastColumn Y)` factors. -/
theorem rectangularFourierIntegral_column_mul (ψ : UnitaryAdditiveCharacter ℂ)
    (μ : AdditiveHaarMeasure ℂ) [SigmaFinite μ.measure]
    (f₁ : Matrix (Fin m) (Fin m) ℂ → ℂ) (f₂ : (Fin m → ℂ) → ℂ)
    (Z : Matrix (Fin m) (Fin (m + 1)) ℂ) :
    rectangularFourierIntegral ψ μ (fun Y => f₁ (leadingColumns Y) * f₂ (lastColumn Y)) Z =
      rectangularFourierIntegral ψ μ f₁ (leadingColumns Z) *
        ∫ v, f₂ v * ψ.complex (∑ i, v i * lastColumn Z i) ∂Measure.pi fun _ : Fin m => μ.measure := by
  let g : (Fin m → ℂ) × Matrix (Fin m) (Fin m) ℂ → ℂ := fun p =>
    (f₂ p.1 * ψ.complex (∑ i, p.1 i * lastColumn Z i)) *
      (f₁ p.2 * ψ.complex (rectangularPairing p.2 (leadingColumns Z)))
  calc rectangularFourierIntegral ψ μ (fun Y => f₁ (leadingColumns Y) * f₂ (lastColumn Y)) Z
      = ∫ Y, g (columnSplitEquiv m Y) ∂rectangularMeasure μ m (m + 1) := by
        unfold rectangularFourierIntegral
        refine integral_congr_ae (ae_of_all _ fun Y => ?_)
        simp only [g, columnSplitEquiv_apply, rectangularPairing_eq_add, AddChar.map_add_eq_mul]
        ring
    _ = ∫ p, g p ∂(Measure.pi fun _ : Fin m => μ.measure).prod (rectangularMeasure μ m m) :=
        (measurePreserving_columnSplitEquiv μ.measure).integral_comp' g
    _ = (∫ v, f₂ v * ψ.complex (∑ i, v i * lastColumn Z i) ∂Measure.pi fun _ : Fin m => μ.measure) *
          rectangularFourierIntegral ψ μ f₁ (leadingColumns Z) :=
        integral_prod_mul (fun v : Fin m → ℂ => f₂ v * ψ.complex (∑ i, v i * lastColumn Z i))
          (fun S : Matrix (Fin m) (Fin m) ℂ =>
            f₁ S * ψ.complex (rectangularPairing S (leadingColumns Z)))
    _ = _ := mul_comm _ _

/-- The negative-sign vector Fourier integral for `ψ_a` and its self-dual product measure. -/
def vectorFourierIntegral (a : ℂˣ) (f : (Fin m → ℂ) → ℂ) (w : Fin m → ℂ) : ℂ :=
  ∫ v, f v * (complexScaledCharacter a).complex (-∑ i, v i * w i)
    ∂Measure.pi fun _ : Fin m => (complexSelfDualMeasure a).measure

/-- The negative-sign Fourier integral in the last column only. -/
def lastColumnFourierIntegral (a : ℂˣ) (F : Matrix (Fin m) (Fin (m + 1)) ℂ → ℂ)
    (X : Matrix (Fin m) (Fin (m + 1)) ℂ) : ℂ :=
  vectorFourierIntegral a (fun v => F (columnJoin (leadingColumns X) v)) (lastColumn X)

/-- **Fourier transform of a column product.** For the self-dual measure of `ψ_a`, the
negative-sign full Fourier integral of `columnProduct Φ φ` at `X` is the product of the
negative-sign square Fourier integral of `Φ` at `leadingColumns X` and the negative-sign vector
Fourier integral of `φ` at `lastColumn X`. -/
def ComplexColumnProductFourierStatement : Prop :=
  ∀ (m : ℕ) (a : ℂˣ) (Φ : 𝓢(Matrix (Fin m) (Fin m) ℂ, ℂ)) (φ : 𝓢(Fin m → ℂ, ℂ))
    (X : Matrix (Fin m) (Fin (m + 1)) ℂ),
    rectangularFourierIntegral (complexScaledCharacter a) (complexSelfDualMeasure a)
        (columnProduct Φ φ) (-X) =
      rectangularFourierIntegral (complexScaledCharacter a) (complexSelfDualMeasure a) Φ
          (-leadingColumns X) *
        vectorFourierIntegral a φ (lastColumn X)

theorem complexColumnProductFourier : ComplexColumnProductFourierStatement := by
  intro m a Φ φ X
  have h := rectangularFourierIntegral_column_mul (complexScaledCharacter a)
    (complexSelfDualMeasure a) Φ φ (-X)
  rw [leadingColumns_neg, lastColumn_neg] at h
  have hfun : (columnProduct Φ φ : Matrix (Fin m) (Fin (m + 1)) ℂ → ℂ) =
      fun Y => Φ (leadingColumns Y) * φ (lastColumn Y) := rfl
  rw [hfun]
  simpa only [vectorFourierIntegral, Pi.neg_apply, mul_neg, Finset.sum_neg_distrib] using h

/-- The partial Fourier integral in the last column of a column product. -/
theorem lastColumnFourierIntegral_columnProduct (a : ℂˣ) (Φ : 𝓢(Matrix (Fin m) (Fin m) ℂ, ℂ))
    (φ : 𝓢(Fin m → ℂ, ℂ)) (X : Matrix (Fin m) (Fin (m + 1)) ℂ) :
    lastColumnFourierIntegral a (columnProduct Φ φ) X =
      Φ (leadingColumns X) * vectorFourierIntegral a φ (lastColumn X) := by
  simp only [lastColumnFourierIntegral, vectorFourierIntegral, columnProduct_apply,
    leadingColumns_columnJoin, lastColumn_columnJoin, mul_assoc, integral_const_mul]

end Langlands.Global.RankinSelbergGlobal.ComplexGodementColumnProduct
