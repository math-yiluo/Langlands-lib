import Langlands.Global.RankinSelberg.RectangularIwasawaChart
import Mathlib.Topology.Algebra.Valued.NormedValued

/-! # Polynomial rectangular bounds from trailing simple roots -/

noncomputable section
universe u
open scoped NNReal
set_option autoImplicit false

namespace Langlands.GeneralLinear.RectangularIwasawa

/-- The polynomial radius supplied by the trailing simple-root bound. -/
def rectangularSupportRadius (d : ℕ) (R : ℝ) : ℝ :=
  R ^ (d * (d + 1))

section Norm

variable {𝕜 : Type u} [NormedField 𝕜] {a d n : ℕ}

/-- Bounded adjacent ratios and a final norm at most one bound a unit
diagonal tuple by powers of the common ratio bound. -/
theorem diagonal_norm_le_of_roots
    (b : Fin (n + 1) → 𝕜ˣ) (R : ℝ) (hR : 1 ≤ R)
    (hlast : ‖(b (Fin.last n) : 𝕜)‖ ≤ 1)
    (hroot : ∀ i : Fin n, ‖((b i.castSucc / b i.succ : 𝕜ˣ) : 𝕜)‖ ≤ R) :
    ∀ i, ‖(b i : 𝕜)‖ ≤ R ^ n := by
  have hp (i : Fin (n + 1)) : ‖(b i : 𝕜)‖ ≤ R ^ (n - i.val) := by
    induction i using Fin.reverseInduction with
    | last => simpa using hlast
    | @cast i ih =>
      have he : ‖(b i.castSucc : 𝕜)‖ =
          ‖((b i.castSucc / b i.succ : 𝕜ˣ) : 𝕜)‖ * ‖(b i.succ : 𝕜)‖ := by
        rw [← norm_mul, ← Units.val_mul, div_mul_cancel]
      rw [he]
      calc
        _ ≤ R * R ^ (n - i.succ.val) :=
          mul_le_mul (hroot i) ih (norm_nonneg _) (zero_le_one.trans hR)
        _ = R ^ (n - i.castSucc.val) := by
          rw [← pow_succ']
          congr 1
          simp only [Fin.val_succ, Fin.val_castSucc]
          omega
  intro i
  exact (hp i).trans (pow_le_pow_right₀ hR (Nat.sub_le _ _))

/-- The trailing diagonal product is polynomially bounded by a common
bound for its adjacent ratios. -/
theorem norm_trailingDiagonalProduct_le_of_roots
    (B : Langlands.GeneralLinear (a + (d + 1)) 𝕜)
    (hB : B.val.IsUpperTriangular) (R : ℝ) (hR : 1 ≤ R)
    (hlast : ‖B ((Fin.last d).natAdd a) ((Fin.last d).natAdd a)‖ ≤ 1)
    (hroot : ∀ i : Fin d,
      ‖B (i.castSucc.natAdd a) (i.castSucc.natAdd a) /
        B (i.succ.natAdd a) (i.succ.natAdd a)‖ ≤ R) :
    ‖trailingDiagonalProduct a (d + 1) B.val‖ ≤ rectangularSupportRadius d R := by
  let b : Fin (d + 1) → 𝕜ˣ := fun q =>
    Global.PrimitiveAdelicHeight.diagonalUnit B hB (q.natAdd a)
  have hb : ∀ q, ‖(b q : 𝕜)‖ ≤ R ^ d :=
    diagonal_norm_le_of_roots b R hR hlast (fun q => by
      rw [Units.val_div_eq_div_val]
      dsimp only [b, Global.PrimitiveAdelicHeight.diagonalUnit]
      exact hroot q)
  rw [trailingDiagonalProduct, norm_prod]
  calc
    _ ≤ ∏ _q : Fin (d + 1), R ^ d :=
      Finset.prod_le_prod₀ (fun q _ => norm_nonneg _) (fun q _ => hb q)
    _ = rectangularSupportRadius d R := by
      simp [rectangularSupportRadius, ← pow_mul]

private theorem final_diagonal_norm_le
    (g : Langlands.GeneralLinear a 𝕜) (x : Matrix (Fin d) (Fin a) 𝕜)
    (B K : Langlands.GeneralLinear (a + (d + 1)) 𝕜)
    (hfac : lowerBlockPair g (extendRectangle 1 x) 1 = B * K)
    (hKinv : ∀ i j, ‖K⁻¹ i j‖ ≤ 1) :
    ‖B ((Fin.last d).natAdd a) ((Fin.last d).natAdd a)‖ ≤ 1 := by
  have hlastIndex : (0 : Fin 1).natAdd d = Fin.last d := by
    apply Fin.ext
    simp
  have hrow :
      ∀ q, lowerBlockPair g (extendRectangle 1 x) 1 ((Fin.last d).natAdd a) q =
        (1 : Matrix (Fin (a + (d + 1))) (Fin (a + (d + 1))) 𝕜)
          ((Fin.last d).natAdd a) q := by
    intro q
    rw [← hlastIndex]
    exact lowerBlockPair_extendRectangle_final_row g x (0 : Fin 1) q
  rw [diagonal_eq_inverse_of_standard_row
    (lowerBlockPair g (extendRectangle 1 x) 1) B K
    ((Fin.last d).natAdd a) hrow hfac]
  exact hKinv _ _

/-- A common bound on the trailing simple roots gives a polynomial
coordinate bound in the three-block chart. -/
theorem norm_lowerBlockLocalization_coordinate_le_of_roots
    (g : Langlands.GeneralLinear a 𝕜) (x : Matrix (Fin d) (Fin a) 𝕜)
    (B K : Langlands.GeneralLinear (a + (d + 1)) 𝕜)
    (hB : B.val.IsUpperTriangular) (hK : ∀ i j, ‖K i j‖ ≤ 1)
    (hKinv : ∀ i j, ‖K⁻¹ i j‖ ≤ 1)
    (hfac : reindex (finCongr (Nat.add_assoc a d 1))
      (lowerBlockLocalization 1 g x 1) = B * K)
    (R : ℝ) (hR : 1 ≤ R)
    (hroot : ∀ i : Fin d,
      ‖B (i.castSucc.natAdd a) (i.castSucc.natAdd a) /
        B (i.succ.natAdd a) (i.succ.natAdd a)‖ ≤ R)
    (i : Fin d) (j : Fin a) :
    ‖x i j‖ ≤ rectangularSupportRadius d R * ((d + 1).factorial : ℝ) := by
  have hfac' : lowerBlockPair g (extendRectangle 1 x) 1 = B * K := by
    rwa [lowerBlockLocalization_reindex] at hfac
  have hprod := norm_trailingDiagonalProduct_le_of_roots B hB R hR
    (final_diagonal_norm_le g x B K hfac' hKinv) hroot
  have hx := norm_lowerBlockPair_coordinate_le g (extendRectangle 1 x)
    B.val K.val hB hK (congrArg Units.val hfac') (i.castAdd 1) j
  have hh := hx.trans (mul_le_mul_of_nonneg_right hprod (Nat.cast_nonneg _))
  simpa [extendRectangle] using hh

end Norm

section Ultrametric

variable {𝕜 : Type u} [NormedField 𝕜] [IsUltrametricDist 𝕜] {a d : ℕ}

/-- For an ultrametric norm the local minor bound has constant one. -/
theorem norm_lowerBlockPair_coordinate_le_ultrametric
    (g : Langlands.GeneralLinear a 𝕜) (x : Matrix (Fin d) (Fin a) 𝕜)
    (B K : Matrix (Fin (a + d)) (Fin (a + d)) 𝕜)
    (hB : B.IsUpperTriangular) (hK : ∀ i j, ‖K i j‖ ≤ 1)
    (hg : (lowerBlockPair g x 1).val = B * K) (i : Fin d) (j : Fin a) :
    ‖x i j‖ ≤ ‖trailingDiagonalProduct a d B‖ := by
  let w : Valuation 𝕜 ℝ≥0 := NormedField.valuation
  have hwK : ∀ p q, K p q ∈ w.integer := by
    intro p q
    apply (w.mem_integer_iff _).mpr
    change ‖K p q‖₊ ≤ 1
    exact_mod_cast hK p q
  have hx := valuation_lowerBlockPair_coordinate_le w g x B K hB hwK hg i j
  change ‖x i j‖₊ ≤ ‖trailingDiagonalProduct a d B‖₊ at hx
  exact_mod_cast hx

/-- The quantitative nonarchimedean rectangular bound keeps constant one;
in particular a root bound of one forces all coordinates into the unit ball. -/
theorem norm_lowerBlockLocalization_coordinate_le_of_roots_ultrametric
    (g : Langlands.GeneralLinear a 𝕜) (x : Matrix (Fin d) (Fin a) 𝕜)
    (B K : Langlands.GeneralLinear (a + (d + 1)) 𝕜)
    (hB : B.val.IsUpperTriangular) (hK : ∀ i j, ‖K i j‖ ≤ 1)
    (hKinv : ∀ i j, ‖K⁻¹ i j‖ ≤ 1)
    (hfac : reindex (finCongr (Nat.add_assoc a d 1))
      (lowerBlockLocalization 1 g x 1) = B * K)
    (R : ℝ) (hR : 1 ≤ R)
    (hroot : ∀ i : Fin d,
      ‖B (i.castSucc.natAdd a) (i.castSucc.natAdd a) /
        B (i.succ.natAdd a) (i.succ.natAdd a)‖ ≤ R)
    (i : Fin d) (j : Fin a) :
    ‖x i j‖ ≤ rectangularSupportRadius d R := by
  have hfac' : lowerBlockPair g (extendRectangle 1 x) 1 = B * K := by
    rwa [lowerBlockLocalization_reindex] at hfac
  have hprod := norm_trailingDiagonalProduct_le_of_roots B hB R hR
    (final_diagonal_norm_le g x B K hfac' hKinv) hroot
  have hx := norm_lowerBlockPair_coordinate_le_ultrametric g (extendRectangle 1 x)
    B.val K.val hB hK (congrArg Units.val hfac') (i.castAdd 1) j
  have hh := hx.trans hprod
  simpa [extendRectangle] using hh

end Ultrametric

end Langlands.GeneralLinear.RectangularIwasawa
