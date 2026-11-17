import Langlands.Global.RankinSelberg.RectangularCorrectionBounds

/-! # Integral multiples of rectangular diagonal corrections -/

noncomputable section
universe u v
set_option autoImplicit false

namespace Langlands.GeneralLinear.RectangularIwasawa

open Langlands.Global.PrimitiveAdelicHeight

variable {R : Type u} [CommRing R] {I : Type v} {a d n : ℕ}

/-- One scalar makes the values and inverse values of a unit tuple integral
in a specified subring. -/
def HasIntegralMultipleUnitTuple (O : Subring R) (s : R) (c : I → Rˣ) : Prop :=
  ∀ i, s * (c i : R) ∈ O ∧ s * (((c i)⁻¹ : Rˣ) : R) ∈ O

theorem HasIntegralMultipleUnitTuple.div_mem
    {O : Subring R} {s : R} {c : I → Rˣ}
    (hc : HasIntegralMultipleUnitTuple O s c) (i j : I) :
    s ^ 2 * ((c i / c j : Rˣ) : R) ∈ O := by
  have hh := O.mul_mem (hc i).1 (hc j).2
  convert hh using 1
  simp only [div_eq_mul_inv, Units.val_mul]
  ring

private theorem scaled_lowerBlockPair_entries
    (O : Subring R) (s : R) (hs : s ∈ O) (x : Matrix (Fin d) (Fin a) R)
    (hx : ∀ i j, s * x i j ∈ O) (i j : Fin (a + d)) :
    s * lowerBlockPair (1 : Langlands.GeneralLinear a R) x 1 i j ∈ O := by
  induction i using Fin.addCases with
  | left i =>
    induction j using Fin.addCases with
    | left j =>
      simp only [lowerBlockPair_11, Units.val_one, Matrix.one_apply]
      split_ifs <;> simp_all
    | right j => simp
  | right i =>
    induction j using Fin.addCases with
    | left j => simpa only [lowerBlockPair_21] using hx i j
    | right j =>
      simp only [lowerBlockPair_22, OneMemClass.coe_one, Units.val_one, Matrix.one_apply]
      split_ifs <;> simp_all

private theorem scaled_mul_entries
    (O : Subring R) (s : R) (M K : Matrix (Fin n) (Fin n) R)
    (hM : ∀ i j, s * M i j ∈ O) (hK : ∀ i j, K i j ∈ O) (i j : Fin n) :
    s * (M * K) i j ∈ O := by
  rw [Matrix.mul_apply, Finset.mul_sum]
  apply O.sum_mem
  intro k _
  rw [← mul_assoc]
  exact O.mul_mem (hM i k) (hK k j)

/-- Integral compact-factor entries preserve a common denominator for the
lower unipotent, its triangular factor and the inverse factor. -/
theorem integral_multiple_diagonal_correction
    (O : Subring R) (s : R) (hs : s ∈ O)
    (x : Matrix (Fin d) (Fin a) R) (U K : Langlands.GeneralLinear (a + d) R)
    (c : Fin (a + d) → Rˣ) (hU : IsUnitriangular U.val)
    (hK : ∀ i j, K i j ∈ O) (hKi : ∀ i j, K⁻¹ i j ∈ O)
    (hfac : lowerBlockPair 1 x 1 = U * diagonalGL c * K)
    (hx : ∀ i j, s * x i j ∈ O) :
    HasIntegralMultipleUnitTuple O s c := by
  let M := lowerBlockPair (1 : Langlands.GeneralLinear a R) x 1
  let B := U * diagonalGL c
  have hB : B.val.IsUpperTriangular :=
    hU.1.mul (Matrix.blockTriangular_diagonal _)
  have hBfac : B = M * K⁻¹ := by dsimp only [B, M]; rw [hfac]; group
  have hBifac : B⁻¹ = K * M⁻¹ := by dsimp only [B, M]; rw [hfac]; group
  have hM : ∀ i j, s * M i j ∈ O := scaled_lowerBlockPair_entries O s hs x hx
  have hMi : ∀ i j, s * M⁻¹ i j ∈ O := by
    dsimp only [M]
    rw [lowerBlockPair_one_inv]
    exact scaled_lowerBlockPair_entries O s hs (-x) (by
      intro i j
      simpa only [Matrix.neg_apply, mul_neg] using O.neg_mem (hx i j))
  have hBM : ∀ i j, s * B i j ∈ O := by
    rw [hBfac]
    exact scaled_mul_entries O s M.val (K⁻¹).val hM hKi
  have hBiM : ∀ i j, s * B⁻¹ i j ∈ O := by
    intro i j
    rw [hBifac]
    change s * (K.val * (M⁻¹).val) i j ∈ O
    rw [Matrix.mul_apply, Finset.mul_sum]
    apply O.sum_mem
    intro k _
    have hh := O.mul_mem (hK i k) (hMi k j)
    convert hh using 1
    ring
  intro i
  have hd : B i i = (c i : R) := by
    change (U.val * (diagonalGL c).val) i i = _
    rw [diagonalGL, Matrix.mul_diagonal, hU.2 i, one_mul]
  have hu : diagonalUnit B hB i = c i := Units.ext hd
  have hi := congrArg (fun z : Rˣ => ((z⁻¹ : Rˣ) : R)) hu
  change B⁻¹ i i = ((c i)⁻¹ : Rˣ) at hi
  exact ⟨hd ▸ hBM i i, hi ▸ hBiM i i⟩

/-- Diagonal matrix units commute with coefficient maps, including the
unit-valued diagonal and its inverse. -/
theorem map_diagonalGL_units {S : Type*} [CommRing S] (f : R →+* S)
    (c : Fin n → Rˣ) :
    Matrix.GeneralLinearGroup.map f (diagonalGL c) =
      diagonalGL (fun i => Units.map f.toMonoidHom (c i)) := by
  apply Units.ext
  exact map_diagonalGL f c

end Langlands.GeneralLinear.RectangularIwasawa
