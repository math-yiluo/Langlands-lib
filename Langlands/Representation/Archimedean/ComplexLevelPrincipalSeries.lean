import Langlands.Representation.Archimedean.ComplexLevelFunctions

/-!
# Principal-series functions built from level factors

For level data `h b : ℕ → ℕ` (numbers of holomorphic and antiholomorphic determinant factors)
and `dτ : ℕ → ℂ` (modulus increments) and, for each level `m`, matrices `A m j` (`j < h m`) and
`B m j` (`j < b m`), `levelProduct h b dτ A` is the function
`g ↦ ∏_m R_m(g)^{dτ_m - (h_m + b_m)/2} ∏_j D_{m, A m j}(g) ∏_j conj D_{m, B m j}(g)` on
`GL_n(ℂ)`, where `R_m` is the Gram determinant of the rows `m, …, n-1` and
`D_{m, A}(g) = det (rows m.. of g · A)`. `levelProduct_mem_principalSeries`: if the level data add up to
the exponents of the characters `χ_k(z) = phase(z)^{l_k} |z|^{2 t_k}`, it lies in the smooth
principal series of `χ`. Right translation by `k ∈ U(n)` replaces `A` by `k A`
(`levelProduct_mul_unitary`).
-/

noncomputable section

open scoped Matrix Matrix.Norms.Operator ComplexConjugate ContDiff Manifold

set_option autoImplicit false

namespace Langlands.Archimedean.LevelFunctions

open Langlands.Archimedean.ComplexDuality Langlands.GeneralLinear

set_option backward.isDefEq.respectTransparency false

variable {n : ℕ} (h b : ℕ → ℕ) (dτ : ℕ → ℂ)

/-- Matrices for the determinant factors of every level. -/
abbrev LevelMatrices (n : ℕ) (h b : ℕ → ℕ) :=
  (m : Fin n) → (Fin (h m) → Matrix (Fin n) (Tail n m) ℂ) × (Fin (b m) → Matrix (Fin n) (Tail n m) ℂ)

/-- The determinant factor of one level: `∏_j D_{A j} ∏_j conj D_{B j}`. -/
def detPart (m : Fin n) (A : (Fin (h m) → Matrix (Fin n) (Tail n m) ℂ) ×
    (Fin (b m) → Matrix (Fin n) (Tail n m) ℂ)) (y : Matrix (Fin n) (Fin n) ℂ) : ℂ :=
  (∏ j, levelDet m (A.1 j) y) * ∏ j, conj (levelDet m (A.2 j) y)

/-- The Gram factor of one level. -/
def gramPart (m : Fin n) (y : Matrix (Fin n) (Fin n) ℂ) : ℂ :=
  ((gramMinor (m : ℕ) y : ℝ) : ℂ) ^ (dτ m - ((h m + b m : ℕ) : ℂ) / 2)

/-- The product of the level factors, as a function of matrices. -/
def levelProductExt (A : LevelMatrices n h b) (y : Matrix (Fin n) (Fin n) ℂ) : ℂ :=
  ∏ m : Fin n, gramPart h b dτ m y * detPart h b m (A m) y

/-- The product of the level factors on `GL_n(ℂ)`. -/
def levelProduct (A : LevelMatrices n h b) (g : Langlands.GeneralLinear n ℂ) : ℂ :=
  levelProductExt h b dτ A (g : Matrix (Fin n) (Fin n) ℂ)

theorem detPart_borel_mul (m : Fin n) (A : (Fin (h m) → Matrix (Fin n) (Tail n m) ℂ) ×
    (Fin (b m) → Matrix (Fin n) (Tail n m) ℂ))
    (a : Fin n → ℂˣ) (u : upperUnipotent n ℂ) (y : Matrix (Fin n) (Fin n) ℂ) :
    detPart h b m A ((((Iwasawa.diagonalUnits a : Langlands.GeneralLinear n ℂ) *
        (u : Langlands.GeneralLinear n ℂ) : Langlands.GeneralLinear n ℂ) :
          Matrix (Fin n) (Fin n) ℂ) * y) =
      ((∏ i : Tail n m, (a i : ℂ)) ^ h m * conj (∏ i : Tail n m, (a i : ℂ)) ^ b m) *
        detPart h b m A y := by
  unfold detPart
  simp_rw [levelDet_borel_mul, map_mul]
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_const,
    Finset.card_univ, Finset.card_univ, Fintype.card_fin, Fintype.card_fin]
  ring

theorem gramPart_borel_mul (m : Fin n) (a : Fin n → ℂˣ) (u : upperUnipotent n ℂ)
    (g : Langlands.GeneralLinear n ℂ) :
    gramPart h b dτ m ((((Iwasawa.diagonalUnits a : Langlands.GeneralLinear n ℂ) *
        (u : Langlands.GeneralLinear n ℂ) : Langlands.GeneralLinear n ℂ) :
          Matrix (Fin n) (Fin n) ℂ) * (g : Matrix (Fin n) (Fin n) ℂ)) =
      ((∏ i : Tail n m, Complex.normSq (a i : ℂ) : ℝ) : ℂ) ^ (dτ m - ((h m + b m : ℕ) : ℂ) / 2) *
        gramPart h b dτ m g := by
  unfold gramPart
  rw [gramMinor_borel_mul, Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg
    (Finset.prod_nonneg fun i _ => Complex.normSq_nonneg _) (gramMinor_pos _ g).le]

theorem levelProduct_borel_mul (A : LevelMatrices n h b) (a : Fin n → ℂˣ)
    (u : upperUnipotent n ℂ) (g : Langlands.GeneralLinear n ℂ) :
    levelProduct h b dτ A ((Iwasawa.diagonalUnits a : Langlands.GeneralLinear n ℂ) *
        (u : Langlands.GeneralLinear n ℂ) * g) =
      (∏ m : Fin n, levelChar m (h m) (b m) (dτ m) a) * levelProduct h b dτ A g := by
  unfold levelProduct levelProductExt
  rw [Units.val_mul, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun m _ => ?_
  rw [gramPart_borel_mul, detPart_borel_mul, levelChar]
  ring

/-- `levelProduct` lies in the principal series when the level data telescope to the
exponents of `χ`. -/
theorem levelProduct_mem_principalSeries {χ : ℕ → ℂˣ → ℂ} (l : ℕ → ℤ) (t : ℕ → ℂ)
    (hχ : ∀ k z, χ k z = phase z ^ l k * ((‖(z : ℂ)‖ : ℂ)) ^ (2 * t k))
    (hl : ∀ k : Fin n, ∑ m ∈ Finset.univ.filter (fun m : Fin n => m.val ≤ k.val),
      ((h m : ℤ) - b m) = l k)
    (hτ : ∀ k : Fin n, ∑ m ∈ Finset.univ.filter (fun m : Fin n => m.val ≤ k.val), dτ m =
      t k + ((n : ℂ) - 1) / 2 - (k : ℕ))
    (A : LevelMatrices n h b) : levelProduct h b dτ A ∈ principalSeries ℂ n χ := by
  refine ⟨?_, fun a u g => ?_⟩
  · refine contMDiff_of_contDiffOn (ψ := levelProductExt h b dτ A) ?_ (fun g => rfl)
    intro y hy
    obtain ⟨g, rfl⟩ := hy
    refine ContDiffAt.contDiffWithinAt ?_
    unfold levelProductExt
    refine contDiffAt_prod fun m _ => ContDiffAt.mul ?_ ?_
    · -- the Gram factor: `exp (σ log R)` near the unit `g`
      have hre : ContDiff ℝ ∞ (gramMinor (m : ℕ) : Matrix (Fin n) (Fin n) ℂ → ℝ) :=
        Complex.reCLM.contDiff.comp (contDiff_tailGram (m : ℕ))
      set σ : ℂ := dτ m - ((h m + b m : ℕ) : ℂ) / 2
      have hev : (fun y => gramPart h b dτ m y) =ᶠ[nhds (g : Matrix (Fin n) (Fin n) ℂ)]
          fun y => Complex.exp (((Real.log (gramMinor (m : ℕ) y) : ℝ) : ℂ) * σ) := by
        filter_upwards [isOpen_setOf_isUnit_matrix.mem_nhds g.isUnit] with y hy
        have hpos : 0 < gramMinor (m : ℕ) y := by
          simpa using gramMinor_pos (m : ℕ) hy.unit
        unfold gramPart
        rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hpos.ne'),
          Complex.ofReal_log hpos.le]
      refine ContDiffAt.congr_of_eventuallyEq ?_ hev
      refine Complex.contDiff_exp.contDiffAt.comp _ (ContDiffAt.mul ?_ contDiffAt_const)
      refine Complex.ofRealCLM.contDiff.contDiffAt.comp _ ?_
      exact (hre.contDiffAt).log (gramMinor_pos (m : ℕ) g).ne'
    · unfold detPart
      refine ContDiffAt.mul (contDiffAt_prod fun j _ => (contDiff_levelDet _ _).contDiffAt)
        (contDiffAt_prod fun j _ =>
          Complex.conjCLE.contDiff.contDiffAt.comp _ (contDiff_levelDet _ _).contDiffAt)
  · rw [levelProduct_borel_mul, prod_levelChar h b dτ l
      (fun k => t k + ((n : ℂ) - 1) / 2 - (k : ℕ)) hl hτ a]
    congr 1
    unfold principalSeriesCharacter
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [hχ, norm_cpow_two_mul, Complex.finrank_real_complex,
      show ((‖((a k : ℂˣ) : ℂ)‖ ^ 2 : ℝ) : ℂ) = ((Complex.normSq (a k : ℂ) : ℝ) : ℂ) by
        rw [Complex.normSq_eq_norm_sq], mul_assoc, ← Complex.cpow_add _ _ (normSq_ne_zero (a k))]
    congr 2
    ring

/-- Right translation by a unitary matrix replaces `A` by `k A`. -/
def unitaryAct (k : Matrix (Fin n) (Fin n) ℂ) (A : LevelMatrices n h b) : LevelMatrices n h b :=
  fun m => (fun j => k * (A m).1 j, fun j => k * (A m).2 j)

theorem levelProduct_mul_unitary (A : LevelMatrices n h b) (g : Langlands.GeneralLinear n ℂ)
    {k : Langlands.GeneralLinear n ℂ} (hk : (k : Matrix (Fin n) (Fin n) ℂ) ∈
      Matrix.unitaryGroup (Fin n) ℂ) :
    levelProduct h b dτ A (g * k) =
      levelProduct h b dτ (unitaryAct h b (k : Matrix (Fin n) (Fin n) ℂ) A) g := by
  unfold levelProduct levelProductExt gramPart detPart unitaryAct
  rw [Units.val_mul]
  refine Finset.prod_congr rfl fun m _ => ?_
  simp only [gramMinor, tailGram_mul_unitary _ _ hk, levelDet_mul]

end Langlands.Archimedean.LevelFunctions
