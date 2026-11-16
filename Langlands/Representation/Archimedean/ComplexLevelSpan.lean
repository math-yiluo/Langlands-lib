import Langlands.Representation.Archimedean.ComplexLevelPrincipalSeries
import Langlands.Representation.Archimedean.RealPolynomialFunctions

/-!
# The span of the level products: a finite-dimensional `U(n)`-stable space of principal-series
functions

`levelSpan h b dτ` is the span of the functions `levelProduct h b dτ A` over all level matrices
`A`. It is finite-dimensional (`levelSpan_finiteDimensional`): every level product is the fixed
Gram weight times a polynomial of bounded degree in the entries of `g` and `conj g`. It is
stable under right translation by `U(n)` (`rightTranslation_mem_levelSpan`), contains a function
taking the value `1` at the identity (`levelProduct_tailSelect_one`), and lies in the
`U(n)`-finite principal series when the level data telescope to the characters
(`levelSpan_le_kFiniteFunctions`).
-/

noncomputable section

open scoped Matrix Matrix.Norms.Operator ComplexConjugate

set_option autoImplicit false

namespace Langlands.Archimedean.LevelFunctions

open Langlands.Archimedean.ComplexDuality Langlands.GeneralLinear
open Langlands.Archimedean.RealPolynomialFunctions

set_option backward.isDefEq.respectTransparency false

variable {n : ℕ} (h b : ℕ → ℕ) (dτ : ℕ → ℂ)

/-- The span of all level products. -/
def levelSpan : Submodule ℂ (Langlands.GeneralLinear n ℂ → ℂ) :=
  Submodule.span ℂ (Set.range (levelProduct (n := n) h b dτ))

/-- Matrices from their entry vectors. -/
def toMat (v : Fin n × Fin n → ℂ) : Matrix (Fin n) (Fin n) ℂ := Matrix.of fun i j => v (i, j)

/-- Entry vectors of matrices. -/
def ofMat (y : Matrix (Fin n) (Fin n) ℂ) : Fin n × Fin n → ℂ := fun p => y p.1 p.2

theorem toMat_ofMat (y : Matrix (Fin n) (Fin n) ℂ) : toMat (ofMat y) = y := by
  ext i j; rfl

theorem levelDet_mem_degLE (m : ℕ) (A : Matrix (Fin n) (Tail n m) ℂ) :
    (fun v => levelDet m A (toMat v)) ∈ degLE (Fin n × Fin n) n := by
  have hentry : ∀ i i' : Tail n m,
      (fun v => (tailRows m (toMat v) * A) i i') ∈ degLE (Fin n × Fin n) 1 := by
    intro i i'
    have : (fun v => (tailRows m (toMat v) * A) i i') =
        ∑ j : Fin n, A j i' • coord (Fin n × Fin n) (((i : Fin n), j), false) := by
      funext v
      simp [tailRows, toMat, Matrix.mul_apply, coord, mul_comm]
    rw [this]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (coord_mem_degLE _)
  have hcard : Fintype.card (Tail n m) ≤ n := by
    simpa using Fintype.card_subtype_le (fun j : Fin n => m ≤ (j : ℕ))
  have : (fun v => levelDet m A (toMat v)) = ∑ σ : Equiv.Perm (Tail n m),
      (Equiv.Perm.sign σ : ℤ) • ∏ i : Tail n m, fun v => (tailRows m (toMat v) * A) (σ i) i := by
    funext v
    simp only [levelDet, Matrix.det_apply, Finset.sum_apply, Pi.smul_apply, Finset.prod_apply]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Units.smul_def]
  rw [this]
  refine Submodule.sum_mem _ fun σ _ => Submodule.smul_of_tower_mem _ _ ?_
  have := prod_mem_degLE (ι := Fin n × Fin n) Finset.univ
    (fun i : Tail n m => fun v => (tailRows m (toMat v) * A) (σ i) i) (fun _ => 1)
    fun i _ => hentry (σ i) i
  refine degLE_mono ?_ this
  simpa using hcard

theorem detPart_mem_degLE (m : Fin n) (A : (Fin (h m) → Matrix (Fin n) (Tail n m) ℂ) ×
    (Fin (b m) → Matrix (Fin n) (Tail n m) ℂ)) :
    (fun v => detPart h b m A (toMat v)) ∈ degLE (Fin n × Fin n) ((h m + b m) * n) := by
  have e1 : (fun v => detPart h b m A (toMat v)) =
      (∏ j, fun v => levelDet m (A.1 j) (toMat v)) *
        ∏ j, fun v => conj (levelDet m (A.2 j) (toMat v)) := by
    funext v; simp [detPart, Finset.prod_apply]
  rw [e1, add_mul]
  refine mul_mem_degLE ?_ ?_
  · have := prod_mem_degLE (ι := Fin n × Fin n) Finset.univ
      (fun j : Fin (h m) => fun v => levelDet m (A.1 j) (toMat v)) (fun _ => n)
      fun j _ => levelDet_mem_degLE m (A.1 j)
    simpa using this
  · have := prod_mem_degLE (ι := Fin n × Fin n) Finset.univ
      (fun j : Fin (b m) => fun v => conj (levelDet m (A.2 j) (toMat v))) (fun _ => n)
      fun j _ => conj_mem_degLE (levelDet_mem_degLE m (A.2 j))
    simpa using this

/-- The total degree of the determinant parts. -/
def detDegree (n : ℕ) (h b : ℕ → ℕ) : ℕ := ∑ m : Fin n, (h m + b m) * n

/-- The Gram weight common to all level products. -/
def levelWeight (g : Langlands.GeneralLinear n ℂ) : ℂ :=
  ∏ m : Fin n, gramPart h b dτ m (g : Matrix (Fin n) (Fin n) ℂ)

/-- Multiplication by the Gram weight, on functions of the entries. -/
def weightMap : ((Fin n × Fin n → ℂ) → ℂ) →ₗ[ℂ] (Langlands.GeneralLinear n ℂ → ℂ) where
  toFun P g := levelWeight h b dτ g * P (ofMat (g : Matrix (Fin n) (Fin n) ℂ))
  map_add' P Q := by funext g; simp [mul_add]
  map_smul' c P := by funext g; simp [mul_left_comm]

theorem levelProduct_eq_weightMap (A : LevelMatrices n h b) :
    levelProduct h b dτ A = weightMap h b dτ (fun v => ∏ m : Fin n, detPart h b m (A m) (toMat v)) := by
  funext g
  simp only [levelProduct, levelProductExt, weightMap, LinearMap.coe_mk, AddHom.coe_mk,
    levelWeight, toMat_ofMat, Finset.prod_mul_distrib]

theorem levelSpan_le_map :
    levelSpan (n := n) h b dτ ≤ (degLE (Fin n × Fin n) (detDegree n h b)).map (weightMap h b dτ) := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨A, rfl⟩
  rw [levelProduct_eq_weightMap]
  refine Submodule.mem_map_of_mem ?_
  have hP := prod_mem_degLE (ι := Fin n × Fin n) Finset.univ
    (fun m : Fin n => fun v => detPart h b m (A m) (toMat v)) (fun m => (h m + b m) * n)
    fun m _ => detPart_mem_degLE h b m (A m)
  have hf : (∏ m : Fin n, fun v => detPart h b m (A m) (toMat v)) =
      fun v => ∏ m : Fin n, detPart h b m (A m) (toMat v) := by
    funext v; simp [Finset.prod_apply]
  rw [hf] at hP
  exact hP

instance levelSpan_finiteDimensional : FiniteDimensional ℂ (levelSpan (n := n) h b dτ) :=
  Submodule.finiteDimensional_of_le (levelSpan_le_map h b dτ)

theorem rightTranslation_mem_levelSpan {f : Langlands.GeneralLinear n ℂ → ℂ}
    (hf : f ∈ levelSpan (n := n) h b dτ) {k : Langlands.GeneralLinear n ℂ}
    (hk : k ∈ unitaryCompact ℂ n) :
    Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℂ) k f ∈ levelSpan (n := n) h b dτ := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨A, rfl⟩ := hf
    have : Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℂ) k (levelProduct h b dτ A) =
        levelProduct h b dτ (unitaryAct h b (k : Matrix (Fin n) (Fin n) ℂ) A) := by
      funext g
      exact levelProduct_mul_unitary h b dτ A g hk
    rw [this]
    exact Submodule.subset_span ⟨_, rfl⟩
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul r x _ hx => rw [map_smul]; exact Submodule.smul_mem _ r hx

/-- All level matrices equal to the column selection. -/
def selectMatrices : LevelMatrices n h b := fun m => (fun _ => tailSelect m, fun _ => tailSelect m)

theorem levelProduct_tailSelect_one :
    levelProduct (n := n) h b dτ (selectMatrices h b) 1 = 1 := by
  unfold levelProduct levelProductExt
  refine Finset.prod_eq_one fun m _ => ?_
  have hG : gramMinor (m : ℕ) ((1 : Langlands.GeneralLinear n ℂ) : Matrix (Fin n) (Fin n) ℂ) = 1 := by
    simp [gramMinor, tailGram_one]
  have hD : detPart h b m (selectMatrices h b m)
      ((1 : Langlands.GeneralLinear n ℂ) : Matrix (Fin n) (Fin n) ℂ) = 1 := by
    unfold detPart selectMatrices
    simp only [Units.val_one, levelDet_tailSelect_one, map_one, Finset.prod_const_one, mul_one]
  rw [hD, mul_one, gramPart, hG, Complex.ofReal_one, Complex.one_cpow]

theorem levelSpan_ne_bot : levelSpan (n := n) h b dτ ≠ ⊥ := by
  intro hbot
  have hmem : levelProduct h b dτ (selectMatrices h b) ∈ levelSpan (n := n) h b dτ :=
    Submodule.subset_span ⟨_, rfl⟩
  rw [hbot, Submodule.mem_bot] at hmem
  have := congrFun hmem 1
  rw [levelProduct_tailSelect_one] at this
  exact one_ne_zero this

/-- The level span lies in the `U(n)`-finite principal series of `χ`. -/
theorem levelSpan_le_kFiniteFunctions {χ : ℕ → ℂˣ → ℂ} (l : ℕ → ℤ) (t : ℕ → ℂ)
    (hχ : ∀ k z, χ k z = phase z ^ l k * ((‖(z : ℂ)‖ : ℂ)) ^ (2 * t k))
    (hl : ∀ k : Fin n, ∑ m ∈ Finset.univ.filter (fun m : Fin n => m.val ≤ k.val),
      ((h m : ℤ) - b m) = l k)
    (hτ : ∀ k : Fin n, ∑ m ∈ Finset.univ.filter (fun m : Fin n => m.val ≤ k.val), dτ m =
      t k + ((n : ℂ) - 1) / 2 - (k : ℕ)) :
    levelSpan (n := n) h b dτ ≤ kFiniteFunctions (principalSeries ℂ n χ) (unitaryCompact ℂ n) := by
  intro f hf
  refine Submodule.mem_inf.2 ⟨?_, ?_⟩
  · refine (Submodule.span_le.2 ?_) hf
    rintro _ ⟨A, rfl⟩
    exact levelProduct_mem_principalSeries h b dτ l t hχ hl hτ A
  · rw [mem_kFiniteVectors_iff]
    refine Submodule.finiteDimensional_of_le (Submodule.span_le.2 ?_ :
      Submodule.span ℂ _ ≤ levelSpan (n := n) h b dτ)
    rintro _ ⟨k, rfl⟩
    exact rightTranslation_mem_levelSpan h b dτ hf k.2

end Langlands.Archimedean.LevelFunctions
