import Langlands.BushnellKutzko.SimpleTypes

/-! # Averages of cuspidal representations over unipotent radicals -/

open Matrix

noncomputable section

namespace Langlands.BushnellKutzko.LevelZero

universe uR uk uW

open Langlands.GeneralLinear

section Shapes

variable {m r : ℕ}

/-- The block shape `(r, m - r)` of `m`, with two blocks. -/
def twoBlockShape (hr0 : 0 < r) (hrm : r < m) : BlockShape m where
  length := 2
  size := ![r, m - r]
  positive := by
    intro i
    fin_cases i
    · simpa using hr0
    · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one]
      omega
  sum_eq := by
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one]
    omega

theorem twoBlockShape_length (hr0 : 0 < r) (hrm : r < m) :
    (twoBlockShape hr0 hrm).length = 2 := rfl

theorem twoBlockShape_indexEquiv_val (hr0 : 0 < r) (hrm : r < m)
    (s : (twoBlockShape hr0 hrm).Index) :
    ((twoBlockShape hr0 hrm).indexEquiv s : ℕ) = if (s.1 : ℕ) = 0 then (s.2 : ℕ) else r + s.2 := by
  obtain ⟨i, a⟩ := s
  have hi : (i : ℕ) < 2 := i.isLt
  simp only [BlockShape.indexEquiv, Equiv.trans_apply, finCongr_apply, Fin.val_cast,
    finSigmaFinEquiv_apply]
  rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h0 | h1
  · have h0' : (i : ℕ) = 0 := by omega
    simp only [h0', ite_true]
    rw [Finset.sum_eq_zero, zero_add]
    intro j _
    exact absurd j.isLt (by omega)
  · have h1' : ¬ (i : ℕ) = 0 := by omega
    simp only [h1', ite_false]
    congr 1
    have hfin : ∀ j : Fin (i : ℕ), (j : ℕ) = 0 := fun j => by have := j.isLt; omega
    rw [Finset.sum_eq_single ⟨0, by omega⟩]
    · rfl
    · intro j _ hj
      exact absurd (Fin.ext (hfin j)) hj
    · simp

theorem twoBlockShape_lt_iff (hr0 : 0 < r) (hrm : r < m) (s : (twoBlockShape hr0 hrm).Index) :
    ((twoBlockShape hr0 hrm).indexEquiv s : ℕ) < r ↔ (s.1 : ℕ) = 0 := by
  rw [twoBlockShape_indexEquiv_val]
  obtain ⟨i, a⟩ := s
  by_cases h : (i : ℕ) = 0
  · simp only [h, ite_true, iff_true]
    have hi : i = ⟨0, by rw [twoBlockShape_length]; omega⟩ := Fin.ext h
    have hsz : (twoBlockShape hr0 hrm).size i = r := by rw [hi]; rfl
    exact lt_of_lt_of_eq a.isLt hsz
  · simp only [h, ite_false, iff_false]
    omega

variable {R : Type uR} [CommRing R]

/-- Entries of an element of a block unipotent radical outside the blocks strictly above the
diagonal are those of the identity matrix. -/
theorem BlockShape.unipotent_entry {n : ℕ} (B : BlockShape n) {u : GeneralLinear n R}
    (hu : u ∈ B.unipotentSubgroup R) (s t : B.Index) (h : ¬ s.1 < t.1) :
    (u : Matrix (Fin n) (Fin n) R) (B.indexEquiv s) (B.indexEquiv t) =
      (1 : Matrix (Fin n) (Fin n) R) (B.indexEquiv s) (B.indexEquiv t) := by
  rw [BlockShape.mem_unipotentSubgroup_iff] at hu
  obtain ⟨hpar, hdiag⟩ := hu
  rw [BlockShape.mem_parabolic_iff] at hpar
  obtain ⟨i, a⟩ := s
  obtain ⟨j, c⟩ := t
  rcases lt_or_eq_of_le (not_lt.mp h) with hji | hij
  · have h0 := hpar i j a c hji
    rw [Matrix.one_apply_ne]
    · exact h0
    · intro heq
      have := congrArg Sigma.fst (B.indexEquiv.injective heq)
      exact hji.ne this.symm
  · clear h
    cases hij
    have h0 := hdiag i a c
    change (u : Matrix (Fin n) (Fin n) R) (B.index i a) (B.index i c) = _
    rw [h0]
    by_cases hac : a = c
    · subst hac
      simp
    · rw [ite_eq_right hac, Matrix.one_apply_ne]
      intro heq
      exact hac ((B.index i).injective heq)

/-- In the shape `(r, m - r)`, the entries of an element of the unipotent radical outside the
upper right corner are those of the identity matrix. -/
theorem twoBlock_unipotent_entry (hr0 : 0 < r) (hrm : r < m) {u : GeneralLinear m R}
    (hu : u ∈ (twoBlockShape hr0 hrm).unipotentSubgroup R) (x y : Fin m)
    (h : ¬ ((x : ℕ) < r ∧ r ≤ (y : ℕ))) :
    (u : Matrix (Fin m) (Fin m) R) x y = (1 : Matrix (Fin m) (Fin m) R) x y := by
  set B := twoBlockShape hr0 hrm
  have hx := B.indexEquiv.apply_symm_apply x
  have hy := B.indexEquiv.apply_symm_apply y
  have key := BlockShape.unipotent_entry B hu (B.indexEquiv.symm x) (B.indexEquiv.symm y) ?_
  · rw [hx, hy] at key
    exact key
  · intro hlt
    have hlt' : ((B.indexEquiv.symm x).1 : ℕ) < ((B.indexEquiv.symm y).1 : ℕ) := hlt
    have hy2 : ((B.indexEquiv.symm y).1 : ℕ) < 2 := (B.indexEquiv.symm y).1.isLt
    have hx' := (twoBlockShape_lt_iff hr0 hrm (B.indexEquiv.symm x)).mpr (by omega)
    rw [hx] at hx'
    have hy' : ¬ (y : ℕ) < r := fun hy0 => by
      have := (twoBlockShape_lt_iff hr0 hrm (B.indexEquiv.symm y)).mp (by rw [hy]; exact hy0)
      omega
    exact h ⟨hx', by omega⟩

/-- The standard upper parabolic of a two-block shape is proper. -/
theorem twoBlockShape_parabolic_ne_top [Nontrivial R] (hr0 : 0 < r) (hrm : r < m) :
    (twoBlockShape hr0 hrm).parabolic R ≠ ⊤ := by
  classical
  intro htop
  set B := twoBlockShape hr0 hrm
  let i1 : Fin B.length := ⟨1, by rw [twoBlockShape_length]; omega⟩
  let i0 : Fin B.length := ⟨0, by rw [twoBlockShape_length]; omega⟩
  let x : Fin m := B.index i1 ⟨0, B.positive i1⟩
  let y : Fin m := B.index i0 ⟨0, B.positive i0⟩
  have hxy : x ≠ y := by
    intro h
    have := congrArg Sigma.fst (B.indexEquiv.injective h)
    simp [i1, i0] at this
  let T : Matrix (Fin m) (Fin m) R := Matrix.single x y 1
  have hT : T * T = 0 := by simp [T, Ne.symm hxy]
  let u : GeneralLinear m R := ⟨1 + T, 1 - T, by rw [mul_sub, add_mul, add_mul, hT]; simp,
    by rw [sub_mul, mul_add, mul_add, hT]; simp⟩
  have hu : u ∈ B.parabolic R := htop ▸ Subgroup.mem_top u
  rw [BlockShape.mem_parabolic_iff] at hu
  have h0 := hu i1 i0 ⟨0, B.positive i1⟩ ⟨0, B.positive i0⟩ (by simp [i1, i0, Fin.lt_def])
  change (1 + T) x y = 0 at h0
  simp [T, Matrix.one_apply_ne hxy] at h0

end Shapes

section Corner

variable {k : Type uk} [Field k] {f : ℕ}

/-- The matrix with the upper right `r × (f - r)` corner of `Z` and zeros elsewhere. -/
def cornerMat (r : ℕ) (Z : Matrix (Fin f) (Fin f) k) : Matrix (Fin f) (Fin f) k :=
  Matrix.of fun a b => if (a : ℕ) < r ∧ r ≤ (b : ℕ) then Z a b else 0

theorem cornerMat_apply (r : ℕ) (Z : Matrix (Fin f) (Fin f) k) (a b : Fin f) :
    cornerMat r Z a b = if (a : ℕ) < r ∧ r ≤ (b : ℕ) then Z a b else 0 := rfl

theorem cornerMat_mul (r : ℕ) (Z Z' : Matrix (Fin f) (Fin f) k) :
    cornerMat r Z * cornerMat r Z' = 0 := by
  ext a c
  simp only [Matrix.mul_apply, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun b _ => ?_
  rw [cornerMat_apply, cornerMat_apply]
  split_ifs with h1 h2 <;> first | (exfalso; omega) | simp

theorem cornerMat_add (r : ℕ) (Z Z' : Matrix (Fin f) (Fin f) k) :
    cornerMat r (Z + Z') = cornerMat r Z + cornerMat r Z' := by
  ext a b
  rw [Matrix.add_apply, cornerMat_apply, cornerMat_apply, cornerMat_apply]
  split_ifs <;> simp

/-- The unipotent element `1 + cornerMat r Z`. -/
def cornerU (r : ℕ) (Z : Matrix (Fin f) (Fin f) k) : GeneralLinear f k :=
  ⟨1 + cornerMat r Z, 1 - cornerMat r Z,
    by rw [mul_sub, add_mul, add_mul, cornerMat_mul]; simp,
    by rw [sub_mul, mul_add, mul_add, cornerMat_mul]; simp⟩

theorem coe_cornerU (r : ℕ) (Z : Matrix (Fin f) (Fin f) k) :
    ((cornerU r Z : GeneralLinear f k) : Matrix (Fin f) (Fin f) k) = 1 + cornerMat r Z := rfl

theorem cornerU_mul (r : ℕ) (Z Z' : Matrix (Fin f) (Fin f) k) :
    cornerU r Z * cornerU r Z' = cornerU r (Z + Z') := by
  ext1
  rw [Units.val_mul, coe_cornerU, coe_cornerU, coe_cornerU, cornerMat_add, add_mul, mul_add,
    mul_add, cornerMat_mul]
  simp only [one_mul, mul_one, add_zero]
  abel

/-- Every element of the unipotent radical of the shape `(r, f - r)` is a corner unipotent. -/
theorem eq_cornerU_of_mem {r : ℕ} (hr0 : 0 < r) (hrf : r < f) {u : GeneralLinear f k}
    (hu : u ∈ (twoBlockShape hr0 hrf).unipotentSubgroup k) :
    u = cornerU r (u : Matrix (Fin f) (Fin f) k) := by
  ext a b
  rw [coe_cornerU, Matrix.add_apply, cornerMat_apply]
  split_ifs with h
  · rw [Matrix.one_apply_ne (by intro hab; subst hab; omega), zero_add]
  · rw [add_zero]
    exact twoBlock_unipotent_entry hr0 hrf hu a b h

variable [Fintype k] [DecidableEq k]

omit [DecidableEq k] in
/-- For a cuspidal representation, summing the operators of the corner unipotents of a
proper two-block parabolic over all square matrices gives zero. -/
theorem sum_cornerU_eq_zero {W : Type uW} [AddCommGroup W] [Module ℂ W]
    {σ : Representation ℂ (GeneralLinear f k) W} (hσ : FiniteGeneralLinear.IsCuspidal σ)
    {r : ℕ} (hr0 : 0 < r) (hrf : r < f) :
    ∑ Z : Matrix (Fin f) (Fin f) k, σ (cornerU r Z) = 0 := by
  refine LinearMap.ext fun w => ?_
  rw [LinearMap.sum_apply, LinearMap.zero_apply]
  refine hσ (twoBlockShape hr0 hrf) (twoBlockShape_parabolic_ne_top hr0 hrf) _ fun u hu => ?_
  rw [eq_cornerU_of_mem hr0 hrf hu, map_sum]
  simp only [← Module.End.mul_apply, ← map_mul, cornerU_mul]
  exact Fintype.sum_equiv (Equiv.addLeft _) _ _ (fun Z => rfl)

omit [Fintype k] [DecidableEq k] in
theorem tensorPowerRepresentation_apply {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (σ : Representation ℂ (GeneralLinear f k) W) (e : ℕ) (g : Fin e → GeneralLinear f k) :
    tensorPowerRepresentation σ e g = PiTensorProduct.map (fun i => σ (g i)) := rfl

omit [Fintype k] [DecidableEq k] in
theorem comp_mulSingle {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (σ : Representation ℂ (GeneralLinear f k) W) {e : ℕ} (i₀ : Fin e) (u : GeneralLinear f k) :
    (fun i => σ ((Pi.mulSingle i₀ u : Fin e → GeneralLinear f k) i)) = Function.update (fun _ => (1 : W →ₗ[ℂ] W)) i₀ (σ u) := by
  funext i
  by_cases hi : i = i₀
  · subst hi
    rw [Pi.mulSingle_eq_same, Function.update_self]
  · rw [Pi.mulSingle_eq_of_ne hi, Function.update_of_ne hi, map_one]

omit [DecidableEq k] in
/-- The same vanishing for the tensor power, in one tensor factor. -/
theorem sum_tensorPower_cornerU_eq_zero {W : Type uW} [AddCommGroup W] [Module ℂ W]
    {σ : Representation ℂ (GeneralLinear f k) W} (hσ : FiniteGeneralLinear.IsCuspidal σ)
    {r : ℕ} (hr0 : 0 < r) (hrf : r < f) {e : ℕ} (i₀ : Fin e) :
    ∑ Z : Matrix (Fin f) (Fin f) k,
      tensorPowerRepresentation σ e (Pi.mulSingle i₀ (cornerU r Z)) = 0 := by
  have h : ∀ Z : Matrix (Fin f) (Fin f) k,
      tensorPowerRepresentation σ e (Pi.mulSingle i₀ (cornerU r Z)) =
        PiTensorProduct.mapMultilinear ℂ (fun _ : Fin e => W) (fun _ : Fin e => W)
          (Function.update (fun _ => (1 : W →ₗ[ℂ] W)) i₀ (σ (cornerU r Z))) := by
    intro Z
    rw [tensorPowerRepresentation_apply, comp_mulSingle, PiTensorProduct.mapMultilinear_apply]
  simp only [h]
  rw [← MultilinearMap.map_update_sum, sum_cornerU_eq_zero hσ hr0 hrf,
    MultilinearMap.map_update_zero]

end Corner

end Langlands.BushnellKutzko.LevelZero
