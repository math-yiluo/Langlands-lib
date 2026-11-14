import Langlands.GroupScheme.SpecialLinearDynamicRoots
import Langlands.GroupScheme.SpecialLinearBinaryBigCell

/-! # Homomorphisms out of binary SL from big-cell relations -/

noncomputable section

universe u v w x

open Matrix

namespace Langlands.GroupScheme.SpecialLinear.BinaryPresentation

/-- Binary special linear group over a commutative ring. -/
local notation "SL2" A => Matrix.SpecialLinearGroup (Fin 2) A

section Matrices

variable {E : Type u} [Field E]

/-- The upper unipotent matrix with parameter `t`. -/
abbrev upper (t : E) : SL2 E :=
  Matrix.SpecialLinearGroup.transvection (by decide : (0 : Fin 2) ≠ 1) t

/-- The lower unipotent matrix with parameter `t`. -/
abbrev lower (t : E) : SL2 E :=
  Matrix.SpecialLinearGroup.transvection (by decide : (1 : Fin 2) ≠ 0) t

/-- The diagonal matrix `diag(u, u⁻¹)`. -/
abbrev diag (u : Eˣ) : SL2 E :=
  Root.contractingMatrix (by decide : (0 : Fin 2) ≠ 1) u

/-- The big-cell matrix `lower b * diag u * upper a`. -/
def cellMatrix (b : E) (u : Eˣ) (a : E) : SL2 E :=
  lower b * diag u * upper a

theorem coe_cellMatrix (b : E) (u : Eˣ) (a : E) :
    ((cellMatrix b u a : SL2 E) : Matrix (Fin 2) (Fin 2) E) =
      !![(u : E), (u : E) * a; b * u, b * u * a + (u : E)⁻¹] := by
  rw [cellMatrix, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Root.contractingMatrix, Matrix.SpecialLinearGroup.transvection_coe,
      Matrix.mul_apply, Fin.sum_univ_two, Matrix.single_apply, Matrix.one_apply,
      Matrix.diagonal_apply]

theorem cellMatrix_apply_zero_zero (b : E) (u : Eˣ) (a : E) :
    (cellMatrix b u a) 0 0 = u := by
  rw [coe_cellMatrix]
  simp

theorem eq_cellMatrix (g : SL2 E) (hg : g 0 0 ≠ 0) :
    g = cellMatrix (g 1 0 / g 0 0) (Units.mk0 _ hg) (g 0 1 / g 0 0) := by
  have hdet : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
    have := g.2
    rw [Matrix.det_fin_two] at this
    exact this
  apply Subtype.ext
  rw [coe_cellMatrix]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> field_simp
  linear_combination hdet

theorem cellMatrix_mul (b : E) (u : Eˣ) (a b' : E) (u' : Eˣ) (a' : E) (v : Eˣ)
    (hv : (v : E) = 1 + a * b') :
    cellMatrix b u a * cellMatrix b' u' a' =
      cellMatrix (b + (u : E)⁻¹ ^ 2 * ((v : E)⁻¹ * b')) (u * v * u')
        ((u' : E)⁻¹ ^ 2 * ((v : E)⁻¹ * a) + a') := by
  have hu : (u : E) ≠ 0 := u.ne_zero
  have hu' : (u' : E) ≠ 0 := u'.ne_zero
  have hv0 : (v : E) ≠ 0 := v.ne_zero
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_cellMatrix, coe_cellMatrix, coe_cellMatrix,
    Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> field_simp <;> rw [hv] <;> ring

theorem upper_eq_cellMatrix (t : E) : upper t = cellMatrix 0 1 t := by
  apply Subtype.ext
  rw [coe_cellMatrix]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.SpecialLinearGroup.transvection_coe]

theorem lower_eq_cellMatrix (t : E) : lower t = cellMatrix t 1 0 := by
  apply Subtype.ext
  rw [coe_cellMatrix]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.SpecialLinearGroup.transvection_coe]

theorem diag_eq_cellMatrix (u : Eˣ) : diag u = cellMatrix 0 u 0 := by
  apply Subtype.ext
  rw [coe_cellMatrix]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Root.contractingMatrix]

theorem one_eq_cellMatrix : (1 : SL2 E) = cellMatrix 0 1 0 := by
  apply Subtype.ext
  rw [coe_cellMatrix]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem mul_lower_apply_zero_zero (g : SL2 E) (c : E) :
    (g * lower c) 0 0 = g 0 0 + g 0 1 * c := by
  rw [Matrix.SpecialLinearGroup.coe_mul]
  simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.SpecialLinearGroup.transvection_coe,
    Matrix.single_apply, Matrix.one_apply]

theorem row_ne_zero (g : SL2 E) : g 0 0 ≠ 0 ∨ g 0 1 ≠ 0 := by
  have hdet : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
    have := g.2
    rw [Matrix.det_fin_two] at this
    exact this
  by_contra h
  rw [not_or, not_not, not_not] at h
  rw [h.1, h.2] at hdet
  simp at hdet

theorem exists_mul_lower_ne_zero (g : SL2 E) : ∃ c : E, (g * lower c) 0 0 ≠ 0 := by
  rcases row_ne_zero g with h | h
  · exact ⟨0, by rw [mul_lower_apply_zero_zero]; simpa using h⟩
  · refine ⟨(g 0 1)⁻¹ * (1 - g 0 0), ?_⟩
    rw [mul_lower_apply_zero_zero]
    field_simp
    ring_nf
    exact one_ne_zero

/-- Avoidance of two affine zero loci, given three distinct values. -/
theorem exists_affine_ne_zero (hE : ∀ a b : E, ∃ c, c ≠ a ∧ c ≠ b)
    {p₁ q₁ p₂ q₂ : E} (h₁ : p₁ ≠ 0 ∨ q₁ ≠ 0) (h₂ : p₂ ≠ 0 ∨ q₂ ≠ 0) :
    ∃ e : E, p₁ + q₁ * e ≠ 0 ∧ p₂ + q₂ * e ≠ 0 := by
  obtain ⟨e, he₁, he₂⟩ := hE (-p₁ / q₁) (-p₂ / q₂)
  have key : ∀ {p q : E}, (p ≠ 0 ∨ q ≠ 0) → e ≠ -p / q → p + q * e ≠ 0 := by
    intro p q hpq he hzero
    by_cases hq : q = 0
    · rw [hq, zero_mul, add_zero] at hzero
      rcases hpq with hp | hq'
      · exact hp hzero
      · exact hq' hq
    · apply he
      field_simp
      linear_combination hzero
  exact ⟨e, key h₁ he₁, key h₂ he₂⟩

omit [Field E] in
/-- Every infinite field has a value avoiding any two given values. -/
theorem exists_ne_ne_of_infinite [Infinite E] (a b : E) : ∃ c : E, c ≠ a ∧ c ≠ b := by
  classical
  obtain ⟨c, hc⟩ := Infinite.exists_notMem_finset ({a, b} : Finset E)
  refine ⟨c, ?_, ?_⟩
  · rintro rfl
    simp at hc
  · rintro rfl
    simp at hc

/-- The Weyl matrix is `upper (-1) * lower 1 * upper (-1)`. -/
theorem weylMatrix_eq :
    (BinaryUpper.weylMatrix : SL2 E) = upper (-1) * lower 1 * upper (-1) := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [BinaryUpper.weylMatrix, Matrix.SpecialLinearGroup.transvection_coe,
      Matrix.mul_apply, Fin.sum_univ_two, Matrix.single_apply, Matrix.one_apply]

end Matrices

variable (E : Type u) [Field E] (H : Type v) [Group H]

/-- Additive maps `x` and `y` and a multiplicative map `h` from the field to a group,
satisfying the torus conjugation laws and the big-cell relation of binary `SL`:
`x(a) y(b) = y(u⁻¹ b) h(u) x(u⁻¹ a)` whenever `u = 1 + a b` is a unit. -/
structure BigCellRelations where
  /-- The upper root map. -/
  x : E → H
  /-- The lower root map. -/
  y : E → H
  /-- The torus map. -/
  h : Eˣ →* H
  x_add : ∀ a a' : E, x (a + a') = x a * x a'
  y_add : ∀ b b' : E, y (b + b') = y b * y b'
  conj_x : ∀ (u : Eˣ) (a : E), h u * x a * (h u)⁻¹ = x ((u : E) ^ 2 * a)
  conj_y : ∀ (u : Eˣ) (b : E), h u * y b * (h u)⁻¹ = y ((u : E)⁻¹ ^ 2 * b)
  rel : ∀ (a b : E) (u : Eˣ), (u : E) = 1 + a * b →
    x a * y b = y ((u : E)⁻¹ * b) * h u * x ((u : E)⁻¹ * a)

namespace BigCellRelations

variable {E H} (R : BigCellRelations E H)

theorem x_zero : R.x 0 = 1 := by
  simpa using R.x_add 0 0

theorem y_zero : R.y 0 = 1 := by
  simpa using R.y_add 0 0

theorem h_mul_y (u : Eˣ) (c : E) : R.h u * R.y c = R.y ((u : E)⁻¹ ^ 2 * c) * R.h u := by
  rw [← R.conj_y u c]
  group

theorem x_mul_h (u : Eˣ) (c : E) : R.x c * R.h u = R.h u * R.x ((u : E)⁻¹ ^ 2 * c) := by
  have hc := R.conj_x u⁻¹ c
  rw [map_inv, inv_inv, Units.val_inv_eq_inv_val] at hc
  rw [← hc]
  group

/-- The value `y(b) h(u) x(a)` of a big-cell parameter. -/
def cell (b : E) (u : Eˣ) (a : E) : H := R.y b * R.h u * R.x a

theorem cell_mul_cell (b : E) (u : Eˣ) (a b' : E) (u' : Eˣ) (a' : E) (v : Eˣ)
    (hv : (v : E) = 1 + a * b') :
    R.cell b u a * R.cell b' u' a' =
      R.cell (b + (u : E)⁻¹ ^ 2 * ((v : E)⁻¹ * b')) (u * v * u')
        ((u' : E)⁻¹ ^ 2 * ((v : E)⁻¹ * a) + a') := by
  unfold cell
  rw [R.y_add, R.x_add, map_mul, map_mul]
  have e1 := R.rel a b' v hv
  have e2 := R.h_mul_y u ((v : E)⁻¹ * b')
  have e3 := R.x_mul_h u' ((v : E)⁻¹ * a)
  calc R.y b * R.h u * R.x a * (R.y b' * R.h u' * R.x a')
      = R.y b * R.h u * (R.x a * R.y b') * R.h u' * R.x a' := by group
    _ = R.y b * (R.h u * R.y ((v : E)⁻¹ * b')) * R.h v *
          (R.x ((v : E)⁻¹ * a) * R.h u') * R.x a' := by rw [e1]; group
    _ = _ := by rw [e2, e3]; group

open Classical in
/-- The big-cell function: `y(b) h(u) x(a)` on matrices with nonzero top-left entry. -/
def cellValue (g : SL2 E) : H :=
  if hg : g 0 0 = 0 then 1 else R.cell (g 1 0 / g 0 0) (Units.mk0 _ hg) (g 0 1 / g 0 0)

theorem cellValue_cellMatrix (b : E) (u : Eˣ) (a : E) :
    R.cellValue (cellMatrix b u a) = R.cell b u a := by
  have hu : (u : E) ≠ 0 := u.ne_zero
  have h00 : (cellMatrix b u a) 0 0 = u := cellMatrix_apply_zero_zero b u a
  have h10 : (cellMatrix b u a) 1 0 = b * u := by
    rw [coe_cellMatrix]; simp
  have h01 : (cellMatrix b u a) 0 1 = u * a := by
    rw [coe_cellMatrix]; simp
  unfold cellValue
  split_ifs with h0
  · exact absurd (h00 ▸ h0) hu
  · have hunit : Units.mk0 ((cellMatrix b u a) 0 0) h0 = u := by
      ext; simp [h00]
    rw [hunit, h10, h01, h00, mul_div_cancel_right₀ _ hu, mul_div_cancel_left₀ _ hu]

theorem cellValue_mul {g g' : SL2 E} (hg : g 0 0 ≠ 0) (hg' : g' 0 0 ≠ 0)
    (hgg' : (g * g') 0 0 ≠ 0) :
    R.cellValue (g * g') = R.cellValue g * R.cellValue g' := by
  obtain ⟨b, u, a, rfl⟩ : ∃ b u a, g = cellMatrix b u a := ⟨_, _, _, eq_cellMatrix g hg⟩
  obtain ⟨b', u', a', rfl⟩ : ∃ b u a, g' = cellMatrix b u a := ⟨_, _, _, eq_cellMatrix g' hg'⟩
  have hv : (1 + a * b' : E) ≠ 0 := by
    intro hzero
    apply hgg'
    rw [Matrix.SpecialLinearGroup.coe_mul, coe_cellMatrix, coe_cellMatrix,
      Matrix.mul_fin_two]
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.empty_val',
      Matrix.cons_val_fin_one]
    linear_combination (u : E) * u' * hzero
  rw [cellMatrix_mul b u a b' u' a' (Units.mk0 _ hv) rfl, cellValue_cellMatrix,
    cellValue_cellMatrix, cellValue_cellMatrix, R.cell_mul_cell b u a b' u' a'
      (Units.mk0 _ hv) rfl]

theorem cellValue_lower (t : E) : R.cellValue (lower t) = R.y t := by
  rw [lower_eq_cellMatrix, cellValue_cellMatrix]
  simp [cell, R.x_zero]

theorem cellValue_upper (t : E) : R.cellValue (upper t) = R.x t := by
  rw [upper_eq_cellMatrix, cellValue_cellMatrix]
  simp [cell, R.y_zero]

theorem cellValue_diag (u : Eˣ) : R.cellValue (diag u) = R.h u := by
  rw [diag_eq_cellMatrix, cellValue_cellMatrix]
  simp [cell, R.x_zero, R.y_zero]

theorem cellValue_one : R.cellValue 1 = 1 := by
  rw [one_eq_cellMatrix, cellValue_cellMatrix]
  simp [cell, R.x_zero, R.y_zero]

theorem lower_apply_zero_zero (t : E) : (lower t) 0 0 = 1 := by
  rw [lower_eq_cellMatrix, cellMatrix_apply_zero_zero]
  simp

theorem cellValue_mul_lower {g : SL2 E} (hg : g 0 0 ≠ 0) {d : E}
    (hgd : (g * lower d) 0 0 ≠ 0) :
    R.cellValue (g * lower d) = R.cellValue g * R.y d := by
  rw [R.cellValue_mul hg (by rw [lower_apply_zero_zero]; exact one_ne_zero) hgd,
    R.cellValue_lower]

theorem cellValue_lower_mul {g : SL2 E} (hg : g 0 0 ≠ 0) (d : E) :
    R.cellValue (lower d * g) = R.y d * R.cellValue g := by
  have hdg : (lower d * g) 0 0 ≠ 0 := by
    obtain ⟨b, u, a, rfl⟩ : ∃ b u a, g = cellMatrix b u a := ⟨_, _, _, eq_cellMatrix g hg⟩
    rw [lower_eq_cellMatrix, cellMatrix_mul d 1 0 b u a 1 (by simp), cellMatrix_apply_zero_zero]
    simp
  rw [R.cellValue_mul (by rw [lower_apply_zero_zero]; exact one_ne_zero) hg hdg,
    R.cellValue_lower]

/-- The function underlying the lifted homomorphism. -/
def liftFun (g : SL2 E) : H :=
  R.cellValue (g * lower (exists_mul_lower_ne_zero g).choose) *
    R.y (-(exists_mul_lower_ne_zero g).choose)

theorem liftFun_eq (g : SL2 E) (c : E) (hc : (g * lower c) 0 0 ≠ 0) :
    R.liftFun g = R.cellValue (g * lower c) * R.y (-c) := by
  set c₀ := (exists_mul_lower_ne_zero g).choose with hc₀def
  have hc₀ : (g * lower c₀) 0 0 ≠ 0 := (exists_mul_lower_ne_zero g).choose_spec
  have hsplit : g * lower c = g * lower c₀ * lower (c - c₀) := by
    rw [mul_assoc, ← Matrix.SpecialLinearGroup.transvection_add]
    congr 2
    ring
  have hmul : R.cellValue (g * lower c) = R.cellValue (g * lower c₀) * R.y (c - c₀) := by
    rw [hsplit]
    exact R.cellValue_mul_lower hc₀ (by rw [← hsplit]; exact hc)
  unfold liftFun
  rw [← hc₀def, hmul, mul_assoc, ← R.y_add]
  congr 2
  ring

theorem liftFun_of_ne_zero {g : SL2 E} (hg : g 0 0 ≠ 0) : R.liftFun g = R.cellValue g := by
  rw [R.liftFun_eq g 0 (by simpa using hg)]
  simp [R.y_zero]

theorem liftFun_mul_lower (g : SL2 E) (d : E) :
    R.liftFun (g * lower d) = R.liftFun g * R.y d := by
  obtain ⟨c, hc⟩ := exists_mul_lower_ne_zero (g * lower d)
  have hgd : g * lower d * lower c = g * lower (d + c) := by
    rw [mul_assoc, ← Matrix.SpecialLinearGroup.transvection_add]
  rw [R.liftFun_eq _ c hc, R.liftFun_eq g (d + c) (by rw [← hgd]; exact hc), hgd, mul_assoc,
    ← R.y_add]
  congr 2
  ring

theorem liftFun_mul_cell (hE : ∀ a b : E, ∃ c, c ≠ a ∧ c ≠ b) (g : SL2 E) {ω : SL2 E}
    (hω : ω 0 0 ≠ 0) : R.liftFun (g * ω) = R.liftFun g * R.cellValue ω := by
  obtain ⟨e, he₁, he₂⟩ := exists_affine_ne_zero hE (Or.inl hω) (row_ne_zero (g * ω))
  rw [← mul_lower_apply_zero_zero] at he₁ he₂
  -- Replace `ω` by `ω * lower e`.
  have hω' : R.cellValue (ω * lower e) = R.cellValue ω * R.y e :=
    R.cellValue_mul_lower hω he₁
  have hleft : R.liftFun (g * ω) * R.y e = R.cellValue (g * ω * lower e) := by
    rw [← R.liftFun_mul_lower, R.liftFun_of_ne_zero he₂]
  obtain ⟨c, hc⟩ := exists_mul_lower_ne_zero g
  have hright : R.liftFun g * R.cellValue (ω * lower e) =
      R.cellValue (g * ω * lower e) := by
    rw [R.liftFun_eq g c hc, mul_assoc, ← R.cellValue_lower_mul he₁ (-c)]
    have hω'' : (lower (-c) * (ω * lower e)) 0 0 ≠ 0 := by
      have := R.cellValue_lower_mul he₁ (-c)
      obtain ⟨b, u, a, hba⟩ : ∃ b u a, ω * lower e = cellMatrix b u a :=
        ⟨_, _, _, eq_cellMatrix _ he₁⟩
      rw [hba, lower_eq_cellMatrix, cellMatrix_mul (-c) 1 0 b u a 1 (by simp),
        cellMatrix_apply_zero_zero]
      simp
    have hprod : g * lower c * (lower (-c) * (ω * lower e)) = g * ω * lower e := by
      rw [← mul_assoc, mul_assoc g, ← Matrix.SpecialLinearGroup.transvection_add]
      simp [mul_assoc]
    rw [← R.cellValue_mul hc hω'' (by rw [hprod]; exact he₂), hprod]
  have key : R.liftFun (g * ω) * R.y e = R.liftFun g * R.cellValue ω * R.y e := by
    rw [hleft, ← hright, hω', mul_assoc]
  exact mul_right_cancel key

theorem liftFun_mul (hE : ∀ a b : E, ∃ c, c ≠ a ∧ c ≠ b) (g g' : SL2 E) :
    R.liftFun (g * g') = R.liftFun g * R.liftFun g' := by
  obtain ⟨c, hc⟩ := exists_mul_lower_ne_zero g'
  have hsplit : g * g' = g * (g' * lower c) * lower (-c) := by
    rw [mul_assoc, mul_assoc, ← Matrix.SpecialLinearGroup.transvection_add]
    simp
  rw [hsplit, R.liftFun_mul_lower, R.liftFun_mul_cell hE g hc, R.liftFun_eq g' c hc, mul_assoc]

theorem liftFun_one : R.liftFun 1 = 1 := by
  rw [R.liftFun_of_ne_zero (by simp), R.cellValue_one]

/-- The homomorphism from binary `SL` determined by big-cell relations, over a field
with at least three elements. -/
def lift (hE : ∀ a b : E, ∃ c, c ≠ a ∧ c ≠ b) : (SL2 E) →* H where
  toFun := R.liftFun
  map_one' := R.liftFun_one
  map_mul' := R.liftFun_mul hE

variable (hE : ∀ a b : E, ∃ c, c ≠ a ∧ c ≠ b)

theorem lift_upper (t : E) : R.lift hE (upper t) = R.x t := by
  change R.liftFun _ = _
  rw [R.liftFun_of_ne_zero (by rw [upper_eq_cellMatrix, cellMatrix_apply_zero_zero]; simp),
    R.cellValue_upper]

theorem lift_lower (t : E) : R.lift hE (lower t) = R.y t := by
  change R.liftFun _ = _
  rw [R.liftFun_of_ne_zero (by rw [lower_apply_zero_zero]; exact one_ne_zero),
    R.cellValue_lower]

theorem lift_diag (u : Eˣ) : R.lift hE (diag u) = R.h u := by
  change R.liftFun _ = _
  have hd : (diag u) 0 0 ≠ 0 := by
    rw [diag_eq_cellMatrix, cellMatrix_apply_zero_zero]
    exact u.ne_zero
  rw [R.liftFun_of_ne_zero hd, R.cellValue_diag]

theorem lift_weylMatrix :
    R.lift hE BinaryUpper.weylMatrix = R.x (-1) * R.y 1 * R.x (-1) := by
  rw [weylMatrix_eq, map_mul, map_mul, R.lift_upper, R.lift_lower]

end BigCellRelations

section Uniqueness

variable {E : Type u} [Field E] {H : Type v} [Group H]

/-- Homomorphisms from binary `SL` over a field agree when they agree on both families
of elementary unipotent matrices. -/
theorem hom_ext {φ ψ : (SL2 E) →* H} (hx : ∀ t, φ (upper t) = ψ (upper t))
    (hy : ∀ t, φ (lower t) = ψ (lower t)) : φ = ψ := by
  ext g
  induction g using Matrix.SL2.transvection_induction with
  | htransvec i j hij c =>
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · exact hx c
    · exact hy c
    · exact absurd rfl hij
  | hmul A B hA hB => rw [map_mul, map_mul, hA, hB]

end Uniqueness

section MatrixRelations

variable (E : Type u) [Field E]

/-- The elementary matrices of binary `SL` satisfy the big-cell relations. -/
def matrixRelations : BigCellRelations E (SL2 E) where
  x := upper
  y := lower
  h := Root.contractingMatrixHom (by decide : (0 : Fin 2) ≠ 1)
  x_add a a' := Matrix.SpecialLinearGroup.transvection_add _ a a'
  y_add b b' := Matrix.SpecialLinearGroup.transvection_add _ b b'
  conj_x u a := by
    change diag u * upper a * (diag u)⁻¹ = upper _
    rw [mul_inv_eq_iff_eq_mul]
    have hu : (u : E) ≠ 0 := u.ne_zero
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Root.contractingMatrix, Matrix.SpecialLinearGroup.transvection_coe,
        Matrix.mul_apply, Fin.sum_univ_two]
    field_simp
  conj_y u b := by
    change diag u * lower b * (diag u)⁻¹ = lower _
    rw [mul_inv_eq_iff_eq_mul]
    have hu : (u : E) ≠ 0 := u.ne_zero
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Root.contractingMatrix, Matrix.SpecialLinearGroup.transvection_coe,
        Matrix.mul_apply, Fin.sum_univ_two]
    field_simp
  rel a b u hu := by
    change upper a * lower b = lower _ * diag u * upper _
    have hu0 : (u : E) ≠ 0 := u.ne_zero
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul]
    change _ = ((cellMatrix _ u _ : SL2 E) : Matrix (Fin 2) (Fin 2) E)
    rw [coe_cellMatrix]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.SpecialLinearGroup.transvection_coe, Matrix.mul_apply,
        Fin.sum_univ_two] <;> field_simp <;>
      first
        | linear_combination hu
        | linear_combination (-1 : E) * hu

variable {E}

/-- The lift of the matrix relations is the identity of binary `SL`. -/
theorem lift_matrixRelations (hE : ∀ a b : E, ∃ c, c ≠ a ∧ c ≠ b) :
    (matrixRelations E).lift hE = MonoidHom.id _ :=
  hom_ext (fun t => (matrixRelations E).lift_upper hE t)
    (fun t => (matrixRelations E).lift_lower hE t)

end MatrixRelations

section Descent

variable {E : Type u} [Field E] {H : Type v} [Group H]
  {E' : Type w} [Field E'] {H' : Type x} [Group H']

theorem map_upper (ι : E →+* E') (t : E) :
    Matrix.SpecialLinearGroup.map ι (upper t) = upper (ι t) := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.map_apply_coe, Matrix.SpecialLinearGroup.transvection_coe,
    Matrix.SpecialLinearGroup.transvection_coe, map_add, map_one, RingHom.mapMatrix_apply,
    Matrix.map_single _ _ _ ι]

theorem map_lower (ι : E →+* E') (t : E) :
    Matrix.SpecialLinearGroup.map ι (lower t) = lower (ι t) := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.map_apply_coe, Matrix.SpecialLinearGroup.transvection_coe,
    Matrix.SpecialLinearGroup.transvection_coe, map_add, map_one, RingHom.mapMatrix_apply,
    Matrix.map_single _ _ _ ι]

theorem map_diag (ι : E →+* E') (u : Eˣ) :
    Matrix.SpecialLinearGroup.map ι (diag u) = diag (Units.map ι.toMonoidHom u) := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Root.contractingMatrix]

/-- Big-cell relations over a larger field and in a larger group give a homomorphism over
the original field into the original group, when the root maps already take values there.
No size condition is imposed on the original field. -/
theorem exists_hom_of_embedding (R' : BigCellRelations E' H')
    (hE' : ∀ a b : E', ∃ c, c ≠ a ∧ c ≠ b) (ι : E →+* E') (j : H →* H')
    (hj : Function.Injective j) (x y : E → H) (h : Eˣ → H)
    (hx : ∀ t, j (x t) = R'.x (ι t)) (hy : ∀ t, j (y t) = R'.y (ι t))
    (hh : ∀ u, j (h u) = R'.h (Units.map ι.toMonoidHom u)) :
    ∃ φ : (SL2 E) →* H, (∀ t, φ (upper t) = x t) ∧ (∀ t, φ (lower t) = y t) ∧
      ∀ u, φ (diag u) = h u := by
  let ψ : (SL2 E) →* H' := (R'.lift hE').comp (Matrix.SpecialLinearGroup.map ι)
  have hψx : ∀ t, ψ (upper t) = j (x t) := by
    intro t
    simp only [ψ, MonoidHom.comp_apply, map_upper, R'.lift_upper, hx]
  have hψy : ∀ t, ψ (lower t) = j (y t) := by
    intro t
    simp only [ψ, MonoidHom.comp_apply, map_lower, R'.lift_lower, hy]
  have hrange : ∀ g, ψ g ∈ j.range := by
    intro g
    induction g using Matrix.SL2.transvection_induction with
    | htransvec i k hik c =>
      fin_cases i <;> fin_cases k
      · exact absurd rfl hik
      · exact ⟨x c, (hψx c).symm⟩
      · exact ⟨y c, (hψy c).symm⟩
      · exact absurd rfl hik
    | hmul A B hA hB => rw [map_mul]; exact j.range.mul_mem hA hB
  let φ : (SL2 E) →* H :=
    (MonoidHom.ofInjective hj).symm.toMonoidHom.comp (ψ.codRestrict j.range hrange)
  have hφ : ∀ g, j (φ g) = ψ g := by
    intro g
    have := (MonoidHom.ofInjective hj).apply_symm_apply ⟨ψ g, hrange g⟩
    exact congrArg Subtype.val this
  refine ⟨φ, fun t => hj ?_, fun t => hj ?_, fun u => hj ?_⟩
  · rw [hφ, hψx]
  · rw [hφ, hψy]
  · rw [hφ, hh]
    have hmap : Matrix.SpecialLinearGroup.map ι (diag u) = diag (Units.map ι.toMonoidHom u) :=
      map_diag ι u
    change R'.lift hE' (Matrix.SpecialLinearGroup.map ι (diag u)) = _
    rw [hmap, R'.lift_diag]

end Descent

end Langlands.GroupScheme.SpecialLinear.BinaryPresentation
