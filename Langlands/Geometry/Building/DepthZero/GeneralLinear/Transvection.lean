import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.LinearAlgebra.Matrix.Permutation

/-!
# Normal subgroups of `GL_n(F)` containing a transvection

For a field `F` and a finite index type `n`, a normal subgroup of `GL_n(F)` that contains one
nontrivial elementary transvection `1 + c E_{ij}` contains every elementary transvection and the
whole special linear group. The proof conjugates by diagonal and permutation matrices, writes
`diag(a, a⁻¹)` in the coordinates `(i, j)` as a commutator of a diagonal matrix with a product of
three transvections, and then applies Mathlib's
`Matrix.SpecialLinearGroup.diagonal_transvection_induction'`.
-/

noncomputable section

open Matrix

namespace Langlands.Geometry.Building.GeneralLinearParahoric

variable {n : Type*} [Fintype n] [DecidableEq n] {F : Type*} [Field F]

/-- The elementary transvection `1 + c E_{ij}` as an element of `GL_n(F)`. -/
def transvectionGL {i j : n} (hij : i ≠ j) (c : F) : GL n F :=
  Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.transvection hij c)

theorem coe_transvectionGL {i j : n} (hij : i ≠ j) (c : F) :
    (transvectionGL hij c : Matrix n n F) = 1 + single i j c :=
  rfl

theorem transvectionGL_zero {i j : n} (hij : i ≠ j) : transvectionGL hij (0 : F) = 1 := by
  ext : 1
  simp [coe_transvectionGL]

/-- The invertible diagonal matrix with diagonal `d`. -/
def diagGL (d : n → Fˣ) : GL n F where
  val := diagonal fun k => (d k : F)
  inv := diagonal fun k => ((d k)⁻¹ : Fˣ)
  val_inv := by
    rw [diagonal_mul_diagonal]
    simp
  inv_val := by
    rw [diagonal_mul_diagonal]
    simp

theorem coe_diagGL (d : n → Fˣ) : (diagGL d : Matrix n n F) = diagonal fun k => (d k : F) :=
  rfl

theorem coe_diagGL_inv (d : n → Fˣ) :
    ((diagGL d)⁻¹ : GL n F) = diagGL d⁻¹ := by
  ext : 1
  rfl

theorem diagGL_mul (d e : n → Fˣ) : diagGL d * diagGL e = (diagGL (d * e) : GL n F) := by
  ext : 1
  simp [coe_diagGL, diagonal_mul_diagonal]

theorem det_diagGL (d : n → Fˣ) : (diagGL d : Matrix n n F).det = ∏ k, (d k : F) := by
  rw [coe_diagGL, det_diagonal]

/-- Conjugating `1 + c E_{ij}` by `diag(d)` gives `1 + d_i c d_j⁻¹ E_{ij}`. -/
theorem diagGL_conj_transvectionGL (d : n → Fˣ) {i j : n} (hij : i ≠ j) (c : F) :
    diagGL d * transvectionGL hij c * (diagGL d)⁻¹ =
      transvectionGL hij ((d i : F) * c * ((d j)⁻¹ : Fˣ)) := by
  ext p q : 2
  rw [coe_diagGL_inv]
  simp only [Units.val_mul, coe_diagGL, coe_transvectionGL, mul_add, add_mul, mul_one,
    Matrix.add_apply, diagonal_mul, mul_diagonal]
  by_cases hpq : p = q
  · subst hpq
    have hne : ¬(i = p ∧ j = p) := fun h => hij (h.1.trans h.2.symm)
    simp [hne]
  · simp only [diagonal_apply_ne _ hpq, single_apply, one_apply_ne hpq]
    split_ifs with h
    · obtain ⟨rfl, rfl⟩ := h
      simp [Pi.inv_apply]
    · simp

/-- The permutation matrix of `σ` as an element of `GL_n(F)`. -/
def permGL (σ : Equiv.Perm n) : GL n F where
  val := σ.permMatrix F
  inv := (σ⁻¹).permMatrix F
  val_inv := by rw [← permMatrix_mul, inv_mul_cancel, permMatrix_one]
  inv_val := by rw [← permMatrix_mul, mul_inv_cancel, permMatrix_one]

theorem permMatrix_mul_single_mul (σ : Equiv.Perm n) (a b : n) (c : F) :
    σ.permMatrix F * single a b c * (σ⁻¹).permMatrix F = single (σ⁻¹ a) (σ⁻¹ b) c := by
  rw [Equiv.Perm.permMatrix, Equiv.Perm.permMatrix, PEquiv.toMatrix_toPEquiv_mul,
    PEquiv.mul_toMatrix_toPEquiv]
  ext p q
  have e1 : ∀ x y : n, (x = σ y) ↔ (σ⁻¹ x = y) := fun x y => by
    constructor
    · rintro rfl
      simp
    · rintro rfl
      simp
  have e2 : ∀ y : n, (σ⁻¹).symm y = σ y := fun y => rfl
  simp only [submatrix_apply, id_eq, single_apply, e2, e1]

/-- Conjugating `1 + c E_{ab}` by the permutation matrix of `σ` gives
`1 + c E_{σ⁻¹ a, σ⁻¹ b}`. -/
theorem permGL_conj_transvectionGL (σ : Equiv.Perm n) {a b : n} (hab : a ≠ b) (c : F) :
    permGL σ * transvectionGL hab c * (permGL σ)⁻¹ =
      transvectionGL (σ⁻¹.injective.ne hab) c := by
  ext : 1
  change σ.permMatrix F * (1 + single a b c) * (σ⁻¹).permMatrix F = 1 + single _ _ c
  rw [mul_add, add_mul, mul_one, permMatrix_mul_single_mul, ← permMatrix_mul, inv_mul_cancel,
    permMatrix_one]

omit [Fintype n] in
/-- For `i ≠ j` and `p ≠ q` there is a permutation sending `p, q` to `i, j`. -/
theorem exists_perm_apply_eq_apply_eq {i j p q : n} (hij : i ≠ j) (hpq : p ≠ q) :
    ∃ σ : Equiv.Perm n, σ p = i ∧ σ q = j := by
  classical
  let τ₁ := Equiv.swap p i
  let q' := τ₁ q
  have hq' : q' ≠ i := by
    intro h
    apply hpq
    have := congrArg τ₁ h
    simp only [q', τ₁, Equiv.swap_apply_self, Equiv.swap_apply_right] at this
    exact this.symm
  let τ₂ := Equiv.swap q' j
  refine ⟨τ₂ * τ₁, ?_, ?_⟩
  · change τ₂ (τ₁ p) = i
    simp only [τ₁, Equiv.swap_apply_left, τ₂]
    exact Equiv.swap_apply_of_ne_of_ne hq'.symm hij
  · change τ₂ q' = j
    exact Equiv.swap_apply_left _ _

variable {H : Subgroup (GL n F)}

/-- A normal subgroup containing one nontrivial transvection contains all transvections. -/
theorem transvectionGL_mem_of_normal (hH : H.Normal) {i j : n} (hij : i ≠ j) {c : F}
    (hc : c ≠ 0) (hmem : transvectionGL hij c ∈ H) {p q : n} (hpq : p ≠ q) (b : F) :
    transvectionGL hpq b ∈ H := by
  by_cases hb : b = 0
  · subst hb
    rw [transvectionGL_zero]
    exact H.one_mem
  -- First scale the coefficient at the position `(i, j)`.
  have hscale : transvectionGL hij b ∈ H := by
    let d : n → Fˣ := Pi.mulSingle i (Units.mk0 (b * c⁻¹) (mul_ne_zero hb (inv_ne_zero hc)))
    have h := hH.conj_mem _ hmem (diagGL d)
    rw [diagGL_conj_transvectionGL] at h
    have hdi : (d i : F) = b * c⁻¹ := by simp [d]
    have hdj : (((d j)⁻¹ : Fˣ) : F) = 1 := by simp [d, Pi.mulSingle_eq_of_ne hij.symm]
    rw [hdi, hdj, mul_one, mul_assoc, inv_mul_cancel₀ hc, mul_one] at h
    exact h
  -- Then move `(i, j)` to `(p, q)`.
  obtain ⟨σ, hσp, hσq⟩ := exists_perm_apply_eq_apply_eq hij hpq
  have h := hH.conj_mem _ hscale (permGL σ)
  rw [permGL_conj_transvectionGL] at h
  convert h using 2 <;> simp [← hσp, ← hσq]

/-- `w = (1 + E_{ij})(1 - E_{ji})(1 + E_{ij})` in coordinates. -/
theorem transvection_rotation_coe {i j : n} (hij : i ≠ j) :
    ((transvectionGL hij (1 : F) * transvectionGL hij.symm (-1) * transvectionGL hij 1 :
        GL n F) : Matrix n n F) =
      1 + single i j 1 - single j i 1 - single i i 1 - single j j 1 := by
  simp only [Units.val_mul, coe_transvectionGL]
  have h1 : single i j (1 : F) * single i j 1 = 0 := single_mul_single_of_ne _ _ _ _ hij.symm _
  have h2 : single j i (-1 : F) * single j i (-1) = 0 :=
    single_mul_single_of_ne _ _ _ _ hij _
  have hneg : ∀ a b : n, single a b (-1 : F) = -single a b 1 := fun a b => by
    rw [← single_neg]
  simp only [mul_add, add_mul, mul_one, one_mul, single_mul_single_same, h1, add_zero]
  simp only [hneg]
  abel

/-- `diag(a, a⁻¹)` in the coordinates `(i, j)` is the commutator of `diag(a)` at `i` with
`w = (1 + E_{ij})(1 - E_{ji})(1 + E_{ij})`. -/
theorem diag2n_toGL_eq_commutator {i j : n} (hij : i ≠ j) {a : F} (ha : a ≠ 0) :
    Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.diag2n hij a ha) =
      diagGL (Pi.mulSingle i (Units.mk0 a ha)) *
        (transvectionGL hij (1 : F) * transvectionGL hij.symm (-1) * transvectionGL hij 1) *
        (diagGL (Pi.mulSingle i (Units.mk0 a ha)))⁻¹ *
        (transvectionGL hij (1 : F) * transvectionGL hij.symm (-1) * transvectionGL hij 1)⁻¹ := by
  set w : GL n F := transvectionGL hij (1 : F) * transvectionGL hij.symm (-1) *
    transvectionGL hij 1 with hw
  set g : GL n F := diagGL (Pi.mulSingle i (Units.mk0 a ha)) with hg
  have hw' : (w : Matrix n n F) =
      1 + single i j 1 - single j i 1 - single i i 1 - single j j 1 := by
    rw [hw]
    exact transvection_rotation_coe hij
  clear_value w g
  rw [eq_mul_inv_iff_mul_eq, eq_comm, mul_inv_eq_iff_eq_mul]
  ext p q : 2
  rw [Units.val_mul, Units.val_mul, Units.val_mul, hw']
  simp only [hg, coe_diagGL,
    Matrix.SpecialLinearGroup.coe_GL_coe_matrix, Matrix.SpecialLinearGroup.diag2n_coe]
  simp only [diagonal_mul, mul_diagonal, Matrix.add_apply, Matrix.sub_apply, one_apply,
    single_apply]
  by_cases hpi : p = i <;> by_cases hpj : p = j <;> by_cases hqi : q = i <;>
    by_cases hqj : q = j <;>
    simp_all [Ne.symm hij, @eq_comm _ i, @eq_comm _ j]

/-- A normal subgroup of `GL_n(F)` containing one nontrivial elementary transvection contains
the image of `SL_n(F)`. -/
theorem specialLinear_le_of_normal (hH : H.Normal) {i j : n} (hij : i ≠ j) {c : F}
    (hc : c ≠ 0) (hmem : transvectionGL hij c ∈ H) (M : Matrix.SpecialLinearGroup n F) :
    Matrix.SpecialLinearGroup.toGL M ∈ H := by
  have htr : ∀ {p q : n} (hpq : p ≠ q) (b : F), transvectionGL hpq b ∈ H :=
    fun hpq b => transvectionGL_mem_of_normal hH hij hc hmem hpq b
  have : Nontrivial n := ⟨⟨i, j, hij⟩⟩
  refine Matrix.SpecialLinearGroup.diagonal_transvection_induction'
    (fun A => Matrix.SpecialLinearGroup.toGL A ∈ H) M ?_ ?_ ?_
  · intro p q hpq a ha
    rw [diag2n_toGL_eq_commutator hpq ha]
    have hw := H.mul_mem (H.mul_mem (htr hpq 1) (htr hpq.symm (-1))) (htr hpq 1)
    exact H.mul_mem (hH.conj_mem _ hw _) (H.inv_mem hw)
  · intro p q hpq a
    exact htr hpq a
  · intro A B hA hB
    rw [map_mul]
    exact H.mul_mem hA hB

/-- Every invertible matrix is a matrix of determinant one times `diag(det, 1, …, 1)`. -/
theorem eq_toGL_mul_diagGL (g : GL n F) (i : n) :
    ∃ M : Matrix.SpecialLinearGroup n F,
      g = Matrix.SpecialLinearGroup.toGL M *
        diagGL (Pi.mulSingle i (Units.mk0 (g : Matrix n n F).det
          (g.isUnit.map Matrix.detMonoidHom).ne_zero)) := by
  set u : Fˣ := Units.mk0 (g : Matrix n n F).det (g.isUnit.map Matrix.detMonoidHom).ne_zero
  set h : GL n F := g * (diagGL (Pi.mulSingle i u))⁻¹
  have hdet : (h : Matrix n n F).det = 1 := by
    simp only [h, Units.val_mul, det_mul, coe_diagGL_inv, det_diagGL]
    rw [Finset.prod_eq_single i]
    · simp only [Pi.inv_apply, Pi.mulSingle_eq_same, u, Units.val_inv_eq_inv_val]
      exact mul_inv_cancel₀ (g.isUnit.map Matrix.detMonoidHom).ne_zero
    · intro b _ hb
      simp [Pi.mulSingle_eq_of_ne hb]
    · simp
  refine ⟨⟨h, hdet⟩, ?_⟩
  have hh : Matrix.SpecialLinearGroup.toGL ⟨(h : Matrix n n F), hdet⟩ = h := Units.ext rfl
  rw [hh]
  simp [h]

end Langlands.Geometry.Building.GeneralLinearParahoric
