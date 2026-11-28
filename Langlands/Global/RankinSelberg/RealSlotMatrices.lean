import Langlands.Global.RankinSelberg.RealIwasawa
import Langlands.Group.GL.Maps
import Langlands.Representation.Archimedean.RealBlockRotation

/-! # Block diagonal matrices along disjoint two-by-two slots -/

noncomputable section

open Matrix

set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.RealLeviStages

/-- A finite set of slot starts `p`: each slot `{p, p + 1}` lies in `Fin N`, and no two
slots meet. -/
structure SlotSet (N : ℕ) where
  starts : Finset ℕ
  lt : ∀ p ∈ starts, p + 1 < N
  sep : ∀ p ∈ starts, p + 1 ∉ starts

variable {N : ℕ} (S : SlotSet N)

namespace SlotSet

theorem not_mem_pred {p : ℕ} (hp : p + 1 ∈ S.starts) : p ∉ S.starts :=
  fun h => S.sep p h hp

/-- The block diagonal matrix with the block `A p` on the slot `{p, p + 1}` and the
identity elsewhere. -/
def diag (A : ℕ → Matrix (Fin 2) (Fin 2) ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  Matrix.of fun i j =>
    if i.val ∈ S.starts then
      (if j.val = i.val then A i.val 0 0 else if j.val = i.val + 1 then A i.val 0 1 else 0)
    else if i.val ≠ 0 ∧ i.val - 1 ∈ S.starts then
      (if j.val + 1 = i.val then A (i.val - 1) 1 0
        else if j.val = i.val then A (i.val - 1) 1 1 else 0)
    else if j.val = i.val then 1 else 0

variable {S}

/-- The position `i` is the entry `o` of the slot starting at `p`. -/
def InSlot (i : Fin N) (p : ℕ) (o : Fin 2) : Prop := p ∈ S.starts ∧ i.val = p + o.val

theorem diag_row (A : ℕ → Matrix (Fin 2) (Fin 2) ℝ) {i : Fin N} {p : ℕ} {o : Fin 2}
    (h : S.InSlot i p o) (k : Fin N) :
    S.diag A i k = if k.val = p then A p o 0 else if k.val = p + 1 then A p o 1 else 0 := by
  obtain ⟨hp, hi⟩ := h
  have hsep := S.sep p hp
  obtain rfl | rfl : o = 0 ∨ o = 1 := by fin_cases o <;> simp
  · have hi' : i.val = p := by simpa using hi
    have h1 : i.val ∈ S.starts := by rw [hi']; exact hp
    simp only [diag, Matrix.of_apply, h1, ite_true]
    rw [hi']
  · have hi' : i.val = p + 1 := by simpa using hi
    have h1 : i.val ∉ S.starts := by rw [hi']; exact hsep
    have h2 : i.val ≠ 0 ∧ i.val - 1 ∈ S.starts := ⟨by omega, by rw [hi']; simpa using hp⟩
    simp only [diag, Matrix.of_apply]
    have e : i.val - 1 = p := by omega
    rw [ite_eq_right_of_eq_false _ _ (eq_false h1), ite_eq_left_of_eq_true _ _ (eq_true h2), e]
    split_ifs <;> first | rfl | omega

theorem diag_row_other (A : ℕ → Matrix (Fin 2) (Fin 2) ℝ) {i : Fin N}
    (h : ∀ p o, ¬ S.InSlot i p o) (k : Fin N) :
    S.diag A i k = if k = i then 1 else 0 := by
  have h1 : i.val ∉ S.starts := fun hi => h i.val 0 ⟨hi, by simp⟩
  have h2 : ¬ (i.val ≠ 0 ∧ i.val - 1 ∈ S.starts) := by
    rintro ⟨h0, hp⟩
    exact h (i.val - 1) 1 ⟨hp, by simp; omega⟩
  simp only [diag, Matrix.of_apply, h1, h2, ite_false, Fin.ext_iff]

theorem inSlot_or (i : Fin N) : (∃ p o, S.InSlot i p o) ∨ ∀ p o, ¬ S.InSlot i p o := by
  by_cases h : ∃ p o, S.InSlot i p o
  · exact Or.inl h
  · exact Or.inr fun p o hpo => h ⟨p, o, hpo⟩

/-- The first index of a slot as an element of `Fin N`. -/
def first {p : ℕ} (hp : p ∈ S.starts) : Fin N := ⟨p, by have := S.lt p hp; omega⟩

/-- The second index of a slot as an element of `Fin N`. -/
def second {p : ℕ} (hp : p ∈ S.starts) : Fin N := ⟨p + 1, S.lt p hp⟩

theorem inSlot_first {p : ℕ} (hp : p ∈ S.starts) : S.InSlot (first hp) p 0 := ⟨hp, rfl⟩

theorem inSlot_second {p : ℕ} (hp : p ∈ S.starts) : S.InSlot (second hp) p 1 := ⟨hp, rfl⟩

theorem sum_two {f : Fin N → ℝ} (a b : Fin N) (hab : a ≠ b)
    (h : ∀ k, k ≠ a → k ≠ b → f k = 0) : ∑ k, f k = f a + f b := by
  rw [Fintype.sum_eq_add a b hab]
  intro k ⟨hka, hkb⟩
  exact h k hka hkb

theorem diag_mul (A B : ℕ → Matrix (Fin 2) (Fin 2) ℝ) :
    S.diag A * S.diag B = S.diag (fun p => A p * B p) := by
  ext i j
  rw [Matrix.mul_apply]
  rcases S.inSlot_or i with ⟨p, o, h⟩ | h
  · have hp := h.1
    have hne : first hp ≠ second hp := by
      intro e; have := congrArg Fin.val e; simp [first, second] at this
    rw [sum_two (first hp) (second hp) hne]
    · rw [diag_row A h, diag_row A h, diag_row B (inSlot_first hp), diag_row B (inSlot_second hp),
        diag_row _ h]
      simp only [first, second, Fin.val_mk, ite_true, show ¬ (p + 1 = p) by omega, ite_false,
        Matrix.mul_apply, Fin.sum_univ_two]
      split_ifs <;> ring
    · intro k hk1 hk2
      rw [diag_row A h k]
      have h1 : k.val ≠ p := fun e => hk1 (Fin.ext (by simp [first, e]))
      have h2 : k.val ≠ p + 1 := fun e => hk2 (Fin.ext (by simp [second, e]))
      simp [h1, h2]
  · rw [Fintype.sum_eq_single i]
    · rw [diag_row_other A h, diag_row_other B h, diag_row_other _ h, ite_eq_left (rfl : i = i),
        one_mul]
    · intro k hk
      rw [diag_row_other A h, ite_eq_right hk, zero_mul]

theorem diag_one : S.diag (fun _ => (1 : Matrix (Fin 2) (Fin 2) ℝ)) = 1 := by
  ext i j
  rw [Matrix.one_apply]
  rcases S.inSlot_or i with ⟨p, o, h⟩ | h
  · rw [diag_row _ h]
    obtain ⟨hp, hi⟩ := h
    obtain rfl | rfl : o = 0 ∨ o = 1 := by fin_cases o <;> simp
    · have hi' : i.val = p := by simpa using hi
      simp only [Matrix.one_apply, Fin.ext_iff, hi']
      split_ifs <;> first | rfl | omega
    · have hi' : i.val = p + 1 := by simpa using hi
      simp only [Matrix.one_apply, Fin.ext_iff, hi']
      split_ifs <;> first | rfl | omega
  · rw [diag_row_other _ h]
    simp only [eq_comm]

/-- The block diagonal invertible matrix of a family of invertible two-by-two blocks. -/
def diagGL (A : ℕ → Matrix.GeneralLinearGroup (Fin 2) ℝ) : Langlands.GeneralLinear N ℝ where
  val := S.diag fun p => (A p : Matrix (Fin 2) (Fin 2) ℝ)
  inv := S.diag fun p => ((A p)⁻¹ : Matrix.GeneralLinearGroup (Fin 2) ℝ)
  val_inv := by
    rw [diag_mul]
    simp only [Units.mul_inv]
    exact diag_one
  inv_val := by
    rw [diag_mul]
    simp only [Units.inv_mul]
    exact diag_one

@[simp] theorem diagGL_val (A : ℕ → Matrix.GeneralLinearGroup (Fin 2) ℝ) :
    ((S.diagGL A : Langlands.GeneralLinear N ℝ) : Matrix (Fin N) (Fin N) ℝ) =
      S.diag fun p => (A p : Matrix (Fin 2) (Fin 2) ℝ) := rfl

theorem diagGL_mul (A B : ℕ → Matrix.GeneralLinearGroup (Fin 2) ℝ) :
    S.diagGL A * S.diagGL B = S.diagGL (fun p => A p * B p) := by
  apply Units.ext
  rw [Units.val_mul, diagGL_val, diagGL_val, diagGL_val, diag_mul]
  rfl


theorem inSlot_val {i : Fin N} {p : ℕ} {o : Fin 2} (h : S.InSlot i p o) : i.val = p + o.val := h.2

theorem inSlot_unique {i : Fin N} {p q : ℕ} {o o' : Fin 2} (h : S.InSlot i p o)
    (h' : S.InSlot i q o') : p = q ∧ o = o' := by
  obtain ⟨hp, hi⟩ := h
  obtain ⟨hq, hi'⟩ := h'
  have hpo := o.isLt
  have hqo := o'.isLt
  have hsp := S.sep p hp
  have hsq := S.sep q hq
  have hpq : p = q := by
    by_contra hne
    have : (p = q + 1 ∧ o.val = 0 ∧ o'.val = 1) ∨ (q = p + 1 ∧ o'.val = 0 ∧ o.val = 1) := by omega
    rcases this with ⟨e, _, _⟩ | ⟨e, _, _⟩
    · exact hsq (e ▸ hp)
    · exact hsp (e ▸ hq)
  subst hpq
  exact ⟨rfl, Fin.ext (by omega)⟩

/-! ## The slot permutation -/

/-- The value of the position obtained by swapping the two entries of its slot. -/
def swapVal (i : Fin N) : ℕ :=
  if i.val ∈ S.starts then i.val + 1
  else if i.val ≠ 0 ∧ i.val - 1 ∈ S.starts then i.val - 1 else i.val

theorem swapVal_of_inSlot {i : Fin N} {p : ℕ} {o : Fin 2} (h : S.InSlot i p o) :
    S.swapVal i = p + (1 - o.val) := by
  obtain ⟨hp, hi⟩ := h
  have hsep := S.sep p hp
  obtain rfl | rfl : o = 0 ∨ o = 1 := by fin_cases o <;> simp
  · have hi' : i.val = p := by simpa using hi
    have h1 : i.val ∈ S.starts := by rw [hi']; exact hp
    simp only [swapVal, hi', hp, ite_true, Fin.val_zero]
  · have hi' : i.val = p + 1 := by simpa using hi
    have h1 : i.val ∉ S.starts := by rw [hi']; exact hsep
    have h2 : i.val ≠ 0 ∧ i.val - 1 ∈ S.starts := ⟨by omega, by rw [hi']; simpa using hp⟩
    simp only [swapVal]
    rw [ite_eq_right_of_eq_false _ _ (eq_false h1), ite_eq_left_of_eq_true _ _ (eq_true h2)]
    simp only [Fin.val_one]
    omega

theorem swapVal_of_not_inSlot {i : Fin N} (h : ∀ p o, ¬ S.InSlot i p o) : S.swapVal i = i.val := by
  have h1 : i.val ∉ S.starts := fun hi => h i.val 0 ⟨hi, by simp⟩
  have h2 : ¬ (i.val ≠ 0 ∧ i.val - 1 ∈ S.starts) := by
    rintro ⟨h0, hp⟩
    exact h (i.val - 1) 1 ⟨hp, by simp; omega⟩
  simp only [swapVal, h1, h2, ite_false]

theorem swapVal_lt (i : Fin N) : S.swapVal i < N := by
  rcases S.inSlot_or i with ⟨p, o, h⟩ | h
  · rw [S.swapVal_of_inSlot h]
    have := S.lt p h.1
    omega
  · rw [S.swapVal_of_not_inSlot h]
    exact i.isLt

/-- Swap the two entries of every slot. -/
def swapFun (i : Fin N) : Fin N := ⟨S.swapVal i, S.swapVal_lt i⟩

theorem inSlot_swapFun {i : Fin N} {p : ℕ} {o : Fin 2} (h : S.InSlot i p o) :
    S.InSlot (S.swapFun i) p (1 - o) := by
  refine ⟨h.1, ?_⟩
  change S.swapVal i = _
  rw [S.swapVal_of_inSlot h]
  obtain rfl | rfl : o = 0 ∨ o = 1 := by fin_cases o <;> simp
  · simp
  · simp

theorem not_inSlot_swapFun {i : Fin N} (h : ∀ p o, ¬ S.InSlot i p o) : S.swapFun i = i :=
  Fin.ext (S.swapVal_of_not_inSlot h)

theorem swapFun_swapFun (i : Fin N) : S.swapFun (S.swapFun i) = i := by
  rcases S.inSlot_or i with ⟨p, o, h⟩ | h
  · apply Fin.ext
    have h' := S.inSlot_swapFun h
    change S.swapVal (S.swapFun i) = i.val
    rw [S.swapVal_of_inSlot h', h.2]
    have := o.isLt
    obtain rfl | rfl : o = 0 ∨ o = 1 := by fin_cases o <;> simp
    · simp
    · simp
  · rw [S.not_inSlot_swapFun h, S.not_inSlot_swapFun h]

/-- The permutation swapping the two entries of every slot. -/
def perm : Equiv.Perm (Fin N) :=
  Function.Involutive.toPerm S.swapFun S.swapFun_swapFun

@[simp] theorem perm_apply (i : Fin N) : S.perm i = S.swapFun i := rfl

@[simp] theorem perm_symm : S.perm.symm = S.perm :=
  Equiv.ext fun _ => rfl

@[simp] theorem perm_inv : S.perm⁻¹ = S.perm := S.perm_symm

theorem perm_perm (i : Fin N) : S.perm (S.perm i) = i := S.swapFun_swapFun i

/-- The permutation preserves the order of two positions that are not the two entries of one
slot. -/
theorem perm_lt_perm {i j : Fin N} (hij : i < j)
    (hslot : ∀ p, ¬ (S.InSlot i p 0 ∧ S.InSlot j p 1)) : S.perm i < S.perm j := by
  change S.swapVal i < S.swapVal j
  have hij' : i.val < j.val := hij
  rcases S.inSlot_or i with ⟨p, o, h⟩ | h <;> rcases S.inSlot_or j with ⟨q, o', h'⟩ | h'
  · rw [S.swapVal_of_inSlot h, S.swapVal_of_inSlot h']
    have hi := h.2
    have hj := h'.2
    have ho := o.isLt
    have ho' := o'.isLt
    by_cases hpq : p = q
    · subst hpq
      have e1 : o = 0 := Fin.ext (by omega)
      have e2 : o' = 1 := Fin.ext (by omega)
      subst e1; subst e2
      exact absurd ⟨h, h'⟩ (hslot p)
    · have hsp := S.sep p h.1
      have hsq := S.sep q h'.1
      have : p + 1 < q ∨ q + 1 < p := by
        rcases Nat.lt_or_gt_of_ne hpq with hlt | hlt
        · by_contra hc
          have : q = p + 1 := by omega
          exact hsp (this ▸ h'.1)
        · by_contra hc
          have : p = q + 1 := by omega
          exact hsq (this ▸ h.1)
      omega
  · rw [S.swapVal_of_inSlot h, S.swapVal_of_not_inSlot h']
    have hi := h.2
    have ho := o.isLt
    by_contra hc
    -- then `j = p + 1` and `o = 0`, so `j` lies in the slot `p`
    have hj : j.val = p + 1 := by omega
    exact h' p 1 ⟨h.1, by simp [hj]⟩
  · rw [S.swapVal_of_not_inSlot h, S.swapVal_of_inSlot h']
    have hj := h'.2
    have ho' := o'.isLt
    by_contra hc
    have hi : i.val = q := by omega
    exact h q 0 ⟨h'.1, by simp [hi]⟩
  · rw [S.swapVal_of_not_inSlot h, S.swapVal_of_not_inSlot h']
    exact hij'


end SlotSet

/-! ## Two-by-two blocks -/

/-- The upper unipotent block `[[1, x], [0, 1]]`. -/
def upper2 (x : ℝ) : Matrix.GeneralLinearGroup (Fin 2) ℝ where
  val := !![1, x; 0, 1]
  inv := !![1, -x; 0, 1]
  val_inv := by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply]
  inv_val := by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply]

/-- The permutation block `[[0, 1], [1, 0]]`. -/
def swap2 : Matrix.GeneralLinearGroup (Fin 2) ℝ where
  val := !![0, 1; 1, 0]
  inv := !![0, 1; 1, 0]
  val_inv := by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply]
  inv_val := by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply]

/-- The rotation block `[[cos θ, -sin θ], [sin θ, cos θ]]`. -/
def rot2 (θ : ℝ) : Matrix.GeneralLinearGroup (Fin 2) ℝ where
  val := !![Real.cos θ, -Real.sin θ; Real.sin θ, Real.cos θ]
  inv := !![Real.cos θ, Real.sin θ; -Real.sin θ, Real.cos θ]
  val_inv := by
    have h := Real.sin_sq_add_cos_sq θ
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply] <;> nlinarith
  inv_val := by
    have h := Real.sin_sq_add_cos_sq θ
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply] <;> nlinarith

/-- The positive diagonal block `[[exp u, 0], [0, exp v]]`. -/
def diag2 (u v : ℝ) : Matrix.GeneralLinearGroup (Fin 2) ℝ where
  val := !![Real.exp u, 0; 0, Real.exp v]
  inv := !![Real.exp (-u), 0; 0, Real.exp (-v)]
  val_inv := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, ← Real.exp_add]
  inv_val := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, ← Real.exp_add]

/-- The norm `√(1 + x²)` of the second column of the open cell `[[0, 1], [1, x]]`. -/
def cellNorm (x : ℝ) : ℝ := Real.sqrt (1 + x ^ 2)

theorem cellNorm_pos (x : ℝ) : 0 < cellNorm x := Real.sqrt_pos.2 (by positivity)

theorem cellNorm_sq (x : ℝ) : cellNorm x ^ 2 = 1 + x ^ 2 :=
  Real.sq_sqrt (by positivity)

/-- The Iwasawa decomposition of the two-by-two open cell:
`[[0, 1], [1, x]] = diag(1/ρ, ρ) [[1, x], [0, 1]] r(arctan x) [[0, 1], [1, 0]]` with
`ρ = √(1 + x²)`. -/
theorem swap2_mul_upper2 (x : ℝ) :
    swap2 * upper2 x =
      diag2 (-Real.log (cellNorm x)) (Real.log (cellNorm x)) * upper2 x *
        rot2 (Real.arctan x) * swap2 := by
  have hρ := cellNorm_pos x
  have hρ2 := cellNorm_sq x
  have he1 : Real.exp (-Real.log (cellNorm x)) = (cellNorm x)⁻¹ := by
    rw [Real.exp_neg, Real.exp_log hρ]
  have he2 : Real.exp (Real.log (cellNorm x)) = cellNorm x := Real.exp_log hρ
  have hc : Real.cos (Real.arctan x) = (cellNorm x)⁻¹ := by
    rw [Real.cos_arctan]; simp [cellNorm]
  have hs : Real.sin (Real.arctan x) = x / cellNorm x := by
    rw [Real.sin_arctan]; simp [cellNorm]
  apply Units.ext
  simp only [Units.val_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [swap2, upper2, rot2, diag2, Matrix.mul_apply, he1, he2, hc, hs] <;>
    field_simp <;> nlinarith [hρ2]

namespace SlotSet

variable {S}

/-- The upper unipotent matrix with the entry `x p` at each slot `(p, p + 1)`. -/
def unip (S : SlotSet N) (x : ℕ → ℝ) : Langlands.GeneralLinear N ℝ := S.diagGL fun p => upper2 (x p)

/-- The permutation matrix of the slot swap, as a block diagonal matrix. -/
def swapGL (S : SlotSet N) : Langlands.GeneralLinear N ℝ := S.diagGL fun _ => swap2

/-- The rotation by `θ p` in each slot `p`. -/
def rot (S : SlotSet N) (θ : ℕ → ℝ) : Langlands.GeneralLinear N ℝ := S.diagGL fun p => rot2 (θ p)

/-- The positive diagonal matrix with `exp (u p), exp (v p)` on the slot `p`. -/
def diagE (S : SlotSet N) (u v : ℕ → ℝ) : Langlands.GeneralLinear N ℝ :=
  S.diagGL fun p => diag2 (u p) (v p)

theorem unip_mul (x y : ℕ → ℝ) : S.unip x * S.unip y = S.unip (x + y) := by
  rw [unip, unip, unip, diagGL_mul]
  congr 1
  funext p
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [upper2, Matrix.mul_apply, add_comm]

theorem unip_zero : S.unip 0 = 1 := by
  apply Units.ext
  rw [unip, diagGL_val, Units.val_one]
  have h : (fun p => ((upper2 ((0 : ℕ → ℝ) p) : Matrix.GeneralLinearGroup (Fin 2) ℝ) :
      Matrix (Fin 2) (Fin 2) ℝ)) = fun _ => 1 := by
    funext p
    ext i j
    fin_cases i <;> fin_cases j <;> simp [upper2]
  rw [h, diag_one]

theorem unip_mem (x : ℕ → ℝ) : S.unip x ∈ Langlands.GeneralLinear.upperUnipotent N ℝ := by
  refine ⟨?_, fun i => ?_⟩
  · intro i j hij
    show S.diag (fun p => ((upper2 (x p) : Matrix.GeneralLinearGroup (Fin 2) ℝ) :
      Matrix (Fin 2) (Fin 2) ℝ)) i j = 0
    rcases S.inSlot_or i with ⟨p, o, h⟩ | h
    · rw [diag_row _ h]
      have hi := h.2
      have hlt : j.val < i.val := hij
      obtain rfl | rfl : o = 0 ∨ o = 1 := by fin_cases o <;> simp
      · simp at hi
        have : j.val ≠ p := by omega
        have : j.val ≠ p + 1 := by omega
        simp [*]
      · simp at hi
        have : j.val ≠ p + 1 := by omega
        by_cases hjp : j.val = p
        · simp [hjp, upper2]
        · simp [*]
    · rw [diag_row_other _ h]
      exact ite_eq_right_of_eq_false _ _ (eq_false (ne_of_lt hij))
  · show S.diag (fun p => ((upper2 (x p) : Matrix.GeneralLinearGroup (Fin 2) ℝ) :
      Matrix (Fin 2) (Fin 2) ℝ)) i i = 1
    rcases S.inSlot_or i with ⟨p, o, h⟩ | h
    · rw [diag_row _ h]
      have hi := h.2
      obtain rfl | rfl : o = 0 ∨ o = 1 := by fin_cases o <;> simp
      · simp at hi
        simp [hi, upper2]
      · simp at hi
        simp [hi, upper2]
    · rw [diag_row_other _ h, ite_eq_left_of_eq_true _ _ (eq_true rfl)]


/-- The slot swap is the permutation matrix of `S.perm`. -/
theorem swapGL_eq_permutation :
    S.swapGL = Langlands.GeneralLinear.permutation N ℝ S.perm := by
  apply Units.ext
  ext i j
  rw [Langlands.GeneralLinear.permutation_entry]
  change S.diag (fun _ => ((swap2 : Matrix.GeneralLinearGroup (Fin 2) ℝ) :
    Matrix (Fin 2) (Fin 2) ℝ)) i j = _
  rcases S.inSlot_or i with ⟨p, o, h⟩ | h
  · rw [diag_row _ h]
    have hσ : S.perm i = S.swapFun i := rfl
    have hj : S.perm j = i ↔ j = S.perm i := by
      constructor
      · intro e; rw [← e, perm_perm]
      · intro e; rw [e, perm_perm]
    simp only [hj]
    have hsw := S.inSlot_swapFun h
    rw [← hσ] at hsw
    have hv := hsw.2
    have hi := h.2
    obtain rfl | rfl : o = 0 ∨ o = 1 := by fin_cases o <;> simp
    · simp at hv hi
      rw [← hσ] at hv
      by_cases h1 : j.val = p
      · have hn : ¬ j = S.perm i := fun e => by rw [e] at h1; omega
        rw [ite_eq_right_of_eq_false _ _ (eq_false hn)]
        simp [h1, swap2]
      · by_cases h2 : j.val = p + 1
        · have hn : j = S.perm i := Fin.ext (by omega)
          rw [ite_eq_left_of_eq_true _ _ (eq_true hn)]
          simp [h2, swap2]
        · have hn : ¬ j = S.perm i := fun e => by rw [e] at h2; omega
          rw [ite_eq_right_of_eq_false _ _ (eq_false hn)]
          simp [h1, h2]
    · simp at hv hi
      rw [← hσ] at hv
      by_cases h1 : j.val = p
      · have hn : j = S.perm i := Fin.ext (by omega)
        rw [ite_eq_left_of_eq_true _ _ (eq_true hn)]
        simp [h1, swap2]
      · by_cases h2 : j.val = p + 1
        · have hn : ¬ j = S.perm i := fun e => by rw [e] at h1; omega
          rw [ite_eq_right_of_eq_false _ _ (eq_false hn)]
          simp [h2, swap2]
        · have hn : ¬ j = S.perm i := fun e => by rw [e] at h1; omega
          rw [ite_eq_right_of_eq_false _ _ (eq_false hn)]
          simp [h1, h2]
  · rw [diag_row_other _ h]
    have hσ : S.perm i = i := S.not_inSlot_swapFun h
    have hj : S.perm j = i ↔ j = i := by
      constructor
      · intro e
        have := congrArg S.perm e
        rwa [perm_perm, hσ] at this
      · intro e; rw [e, hσ]
    simp only [hj]


/-- A vector on the positions, extended by zero to all natural numbers. -/
def natVec (α : Fin N → ℝ) (k : ℕ) : ℝ := if h : k < N then α ⟨k, h⟩ else 0

omit S in
theorem natVec_val (α : Fin N → ℝ) (i : Fin N) : natVec α i.val = α i := by
  simp [natVec, i.isLt]

/-- The torus commutes past the slot unipotent, rescaling its entries. -/
theorem unip_mul_torus (x : ℕ → ℝ) (α : Fin N → ℝ) :
    S.unip x * RealIwasawa.torus α =
      RealIwasawa.torus α * S.unip (fun p => x p * Real.exp (natVec α (p + 1) - natVec α p)) := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, unip, unip, diagGL_val, diagGL_val, RealIwasawa.torus_val]
  ext i j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  rcases S.inSlot_or i with ⟨p, o, h⟩ | h
  · rw [diag_row _ h, diag_row _ h]
    have hi := h.2
    obtain rfl | rfl : o = 0 ∨ o = 1 := by fin_cases o <;> simp
    · simp at hi
      by_cases h1 : j.val = p
      · have : j = i := Fin.ext (by omega)
        subst this
        simp [h1, upper2]
      · by_cases h2 : j.val = p + 1
        · have e1 : natVec α (p + 1) = α j := by rw [← h2, natVec_val]
          have e2 : natVec α p = α i := by rw [← hi, natVec_val]
          have hne : ¬ (p + 1 = p) := by omega
          simp only [h2, hne, ite_false, ite_true, upper2, e1, e2]
          simp only [Fin.isValue, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
            Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
          rw [Real.exp_sub]
          field_simp
        · simp [h1, h2]
    · simp at hi
      by_cases h1 : j.val = p
      · simp [h1, upper2]
      · by_cases h2 : j.val = p + 1
        · have : j = i := Fin.ext (by omega)
          subst this
          simp [h2, upper2]
        · simp [h1, h2]
  · rw [diag_row_other _ h, diag_row_other _ h]
    by_cases hji : j = i
    · subst hji; simp
    · simp [hji]

/-- The slot swap commutes past the torus, permuting its entries. -/
theorem swapGL_mul_torus (α : Fin N → ℝ) :
    S.swapGL * RealIwasawa.torus α = RealIwasawa.torus (α ∘ S.perm) * S.swapGL := by
  rw [swapGL_eq_permutation]
  apply Units.ext
  ext i j
  rw [Langlands.GeneralLinear.permutation_mul_entry, Langlands.GeneralLinear.mul_permutation_entry]
  simp only [perm_inv]
  change (Matrix.diagonal fun k => Real.exp (α k)) (S.perm i) j =
    (Matrix.diagonal fun k => Real.exp ((α ∘ S.perm) k)) i (S.perm j)
  rw [Matrix.diagonal_apply, Matrix.diagonal_apply]
  by_cases hij : S.perm i = j
  · have : i = S.perm j := by rw [← hij, perm_perm]
    rw [ite_eq_left_of_eq_true _ _ (eq_true hij), ite_eq_left_of_eq_true _ _ (eq_true this)]
    simp [Function.comp]
  · have : ¬ i = S.perm j := fun e => hij (by rw [e, perm_perm])
    rw [ite_eq_right_of_eq_false _ _ (eq_false hij), ite_eq_right_of_eq_false _ _ (eq_false this)]

/-- The vector with `u p, v p` on the slot `p` and zero elsewhere. -/
def slotVec (u v : ℕ → ℝ) (i : Fin N) : ℝ :=
  if i.val ∈ S.starts then u i.val
  else if i.val ≠ 0 ∧ i.val - 1 ∈ S.starts then v (i.val - 1) else 0

theorem slotVec_of_inSlot (u v : ℕ → ℝ) {i : Fin N} {p : ℕ} {o : Fin 2} (h : S.InSlot i p o) :
    S.slotVec u v i = if o = 0 then u p else v p := by
  obtain ⟨hp, hi⟩ := h
  have hsep := S.sep p hp
  obtain rfl | rfl : o = 0 ∨ o = 1 := by fin_cases o <;> simp
  · have hi' : i.val = p := by simpa using hi
    simp [slotVec, hi', hp]
  · have hi' : i.val = p + 1 := by simpa using hi
    have h1 : i.val ∉ S.starts := by rw [hi']; exact hsep
    have h2 : i.val ≠ 0 ∧ i.val - 1 ∈ S.starts := ⟨by omega, by rw [hi']; simpa using hp⟩
    simp only [slotVec]
    rw [ite_eq_right_of_eq_false _ _ (eq_false h1), ite_eq_left_of_eq_true _ _ (eq_true h2)]
    simp only [show (1 : Fin 2) ≠ 0 by decide, ite_false]
    congr 1
    omega

theorem slotVec_of_not_inSlot (u v : ℕ → ℝ) {i : Fin N} (h : ∀ p o, ¬ S.InSlot i p o) :
    S.slotVec u v i = 0 := by
  have h1 : i.val ∉ S.starts := fun hi => h i.val 0 ⟨hi, by simp⟩
  have h2 : ¬ (i.val ≠ 0 ∧ i.val - 1 ∈ S.starts) := by
    rintro ⟨h0, hp⟩
    exact h (i.val - 1) 1 ⟨hp, by simp; omega⟩
  simp only [slotVec, h1, h2, ite_false]

theorem diagE_eq_torus (u v : ℕ → ℝ) : S.diagE u v = RealIwasawa.torus (S.slotVec u v) := by
  apply Units.ext
  rw [diagE, diagGL_val, RealIwasawa.torus_val]
  ext i j
  rw [Matrix.diagonal_apply]
  rcases S.inSlot_or i with ⟨p, o, h⟩ | h
  · rw [diag_row _ h, S.slotVec_of_inSlot u v h]
    have hi := h.2
    obtain rfl | rfl : o = 0 ∨ o = 1 := by fin_cases o <;> simp
    · simp at hi
      by_cases h1 : j.val = p
      · have : i = j := Fin.ext (by omega)
        subst this
        simp [h1, diag2]
      · have : i ≠ j := fun e => h1 (by rw [← e, hi])
        by_cases h2 : j.val = p + 1
        · simp [h2, this, diag2]
        · simp [h1, h2, this]
    · simp at hi
      by_cases h1 : j.val = p
      · have : i ≠ j := fun e => by rw [← e] at h1; omega
        simp [h1, this, diag2]
      · by_cases h2 : j.val = p + 1
        · have : i = j := Fin.ext (by omega)
          subst this
          simp [h2, diag2]
        · have : i ≠ j := fun e => h2 (by rw [← e, hi])
          simp [h1, h2, this]
  · rw [diag_row_other _ h, S.slotVec_of_not_inSlot u v h]
    by_cases hij : i = j
    · subst hij; simp
    · simp [hij, Ne.symm hij]

/-- Block form of the open cell in every slot. -/
theorem swapGL_mul_unip (y : ℕ → ℝ) :
    S.swapGL * S.unip y =
      S.diagE (fun p => -Real.log (cellNorm (y p))) (fun p => Real.log (cellNorm (y p))) *
        S.unip y * S.rot (fun p => Real.arctan (y p)) * S.swapGL := by
  simp only [swapGL, unip, diagE, rot, diagGL_mul]
  congr 1
  funext p
  exact swap2_mul_upper2 (y p)


theorem diag_transpose (A : ℕ → Matrix (Fin 2) (Fin 2) ℝ) :
    (S.diag A)ᵀ = S.diag (fun p => (A p)ᵀ) := by
  ext i j
  rw [Matrix.transpose_apply]
  rcases S.inSlot_or i with ⟨p, o, h⟩ | h
  · rw [diag_row _ h]
    have hi := h.2
    have ho := o.isLt
    by_cases hj : j.val = p ∨ j.val = p + 1
    · have hj' : S.InSlot j p ⟨j.val - p, by omega⟩ := ⟨h.1, by simp; omega⟩
      rw [diag_row _ hj']
      rcases hj with hj | hj
      · have e : (⟨j.val - p, by omega⟩ : Fin 2) = 0 := Fin.ext (by simp; omega)
        rw [e]
        obtain rfl | rfl : o = 0 ∨ o = 1 := by fin_cases o <;> simp
        · simp at hi; simp [hi, hj]
        · simp at hi; simp [hi, hj]
      · have e : (⟨j.val - p, by omega⟩ : Fin 2) = 1 := Fin.ext (by simp; omega)
        rw [e]
        obtain rfl | rfl : o = 0 ∨ o = 1 := by fin_cases o <;> simp
        · simp at hi; simp [hi, hj]
        · simp at hi; simp [hi, hj]
    · push Not at hj
      rw [ite_eq_right_of_eq_false _ _ (eq_false hj.1), ite_eq_right_of_eq_false _ _ (eq_false hj.2)]
      rcases S.inSlot_or j with ⟨q, o', h'⟩ | h'
      · rw [diag_row _ h']
        have hqj := h'.2
        have ho' := o'.isLt
        have hpq : p ≠ q := by
          rintro rfl; omega
        have hsp := S.sep p h.1
        have hsq := S.sep q h'.1
        have hiq : i.val ≠ q ∧ i.val ≠ q + 1 := by
          constructor <;> intro e
          · rcases Nat.lt_or_gt_of_ne hpq with hlt | hlt
            · have : q = p + 1 := by omega
              exact hsp (this ▸ h'.1)
            · omega
          · rcases Nat.lt_or_gt_of_ne hpq with hlt | hlt
            · omega
            · have : p = q + 1 := by omega
              exact hsq (this ▸ h.1)
        rw [ite_eq_right_of_eq_false _ _ (eq_false hiq.1),
          ite_eq_right_of_eq_false _ _ (eq_false hiq.2)]
      · rw [diag_row_other _ h']
        have : ¬ i = j := fun e => h' p o (e ▸ h)
        rw [ite_eq_right_of_eq_false _ _ (eq_false this)]
  · rw [diag_row_other _ h]
    rcases S.inSlot_or j with ⟨q, o', h'⟩ | h'
    · rw [diag_row _ h']
      have hj : ¬ j = i := fun e => h q o' (e ▸ h')
      rw [ite_eq_right_of_eq_false _ _ (eq_false hj)]
      have hiq : i.val ≠ q ∧ i.val ≠ q + 1 := by
        constructor <;> intro e
        · exact h q 0 ⟨h'.1, by simp [e]⟩
        · exact h q 1 ⟨h'.1, by simp [e]⟩
      rw [ite_eq_right_of_eq_false _ _ (eq_false hiq.1),
        ite_eq_right_of_eq_false _ _ (eq_false hiq.2)]
    · rw [diag_row_other _ h']
      by_cases hij : i = j
      · subst hij; rfl
      · rw [ite_eq_right_of_eq_false _ _ (eq_false hij),
          ite_eq_right_of_eq_false _ _ (eq_false (Ne.symm hij))]

theorem diagGL_mem_unitaryCompact (A : ℕ → Matrix.GeneralLinearGroup (Fin 2) ℝ)
    (hA : ∀ p, (A p : Matrix (Fin 2) (Fin 2) ℝ) * (A p : Matrix (Fin 2) (Fin 2) ℝ)ᵀ = 1) :
    S.diagGL A ∈ Langlands.Archimedean.unitaryCompact ℝ N := by
  change (S.diagGL A : Matrix (Fin N) (Fin N) ℝ) ∈ Matrix.unitaryGroup (Fin N) ℝ
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial,
    diagGL_val, diag_transpose, diag_mul]
  simp only [hA]
  exact diag_one

theorem swapGL_mem : S.swapGL ∈ Langlands.Archimedean.unitaryCompact ℝ N :=
  diagGL_mem_unitaryCompact _ fun _ => by
    ext i j; fin_cases i <;> fin_cases j <;> simp [swap2, Matrix.mul_apply]

theorem rot_mem (θ : ℕ → ℝ) : S.rot θ ∈ Langlands.Archimedean.unitaryCompact ℝ N :=
  diagGL_mem_unitaryCompact _ fun p => by
    have h := Real.sin_sq_add_cos_sq (θ p)
    ext i j; fin_cases i <;> fin_cases j <;> simp [rot2, Matrix.mul_apply] <;> nlinarith

/-- Adjacent upper entries add under multiplication of unipotent matrices. -/
theorem unipotent_mul_adjacent (g h : Langlands.GeneralLinear.upperUnipotent N ℝ) (a b : Fin N)
    (hab : b.val = a.val + 1) :
    (g * h).val a b = g.val a b + h.val a b := by
  change (g.val.val * h.val.val) a b = _
  rw [Matrix.mul_apply]
  have hne : a ≠ b := fun e => by rw [e] at hab; omega
  rw [Finset.sum_eq_add_of_mem a b (Finset.mem_univ _) (Finset.mem_univ _) hne]
  · rw [Langlands.GeneralLinear.UpperUnipotent.entry_diag,
      Langlands.GeneralLinear.UpperUnipotent.entry_diag, one_mul, mul_one, add_comm]
  · rintro k _ ⟨hka, hkb⟩
    by_cases hk : k < a
    · rw [Langlands.GeneralLinear.UpperUnipotent.entry_eq_zero g hk, zero_mul]
    · have hbk : b < k := by
        have h1 : k.val ≠ a.val := fun e => hka (Fin.ext e)
        have h2 : k.val ≠ b.val := fun e => hkb (Fin.ext e)
        rw [Fin.lt_def] at hk ⊢
        omega
      rw [Langlands.GeneralLinear.UpperUnipotent.entry_eq_zero h hbk, mul_zero]

theorem unip_slot_entry (x : ℕ → ℝ) {p : ℕ} (hp : p ∈ S.starts) :
    (S.unip x : Matrix (Fin N) (Fin N) ℝ) (first hp) (second hp) = x p := by
  rw [unip, diagGL_val, diag_row _ (inSlot_first hp)]
  simp [second, upper2]

/-- Conjugation by the slot swap keeps a unipotent matrix with zero slot entries unipotent. -/
theorem swapGL_conj_mem {u : Langlands.GeneralLinear N ℝ}
    (hu : u ∈ Langlands.GeneralLinear.upperUnipotent N ℝ)
    (hslot : ∀ p (hp : p ∈ S.starts), (u : Matrix (Fin N) (Fin N) ℝ) (first hp) (second hp) = 0) :
    S.swapGL * u * S.swapGL⁻¹ ∈ Langlands.GeneralLinear.upperUnipotent N ℝ := by
  rw [swapGL_eq_permutation]
  refine ⟨?_, fun i => ?_⟩
  · intro i j hji
    change (Langlands.GeneralLinear.permutation N ℝ S.perm * u *
      (Langlands.GeneralLinear.permutation N ℝ S.perm)⁻¹) i j = 0
    rw [Langlands.GeneralLinear.permutation_conjugate_entry, perm_inv]
    by_cases hs : ∃ p, S.InSlot j p 0 ∧ S.InSlot i p 1
    · obtain ⟨p, hj, hi⟩ := hs
      have e1 : S.perm j = second hj.1 := Fin.ext (by
        have := (S.inSlot_swapFun hj).2; simpa [second] using this)
      have e2 : S.perm i = first hj.1 := Fin.ext (by
        have := (S.inSlot_swapFun hi).2; simpa [first] using this)
      rw [e1, e2]
      exact hslot p hj.1
    · push Not at hs
      have hlt : S.perm j < S.perm i := S.perm_lt_perm hji (fun p hh => hs p hh.1 hh.2)
      exact hu.1 hlt
  · change (Langlands.GeneralLinear.permutation N ℝ S.perm * u *
      (Langlands.GeneralLinear.permutation N ℝ S.perm)⁻¹) i i = 1
    rw [Langlands.GeneralLinear.permutation_conjugate_entry, perm_inv]
    exact hu.2 _


/-- The slot unipotent entries rescaled by the torus `torus α` moved through them. -/
def shifted (x : ℕ → ℝ) (α : Fin N → ℝ) (p : ℕ) : ℝ :=
  x p * Real.exp (natVec α (p + 1) - natVec α p)

/-- The logarithmic diagonal of the triangular factors of the open cells in the slots. -/
def cellExponent (y : ℕ → ℝ) : Fin N → ℝ :=
  S.slotVec (fun p => -Real.log (cellNorm (y p))) (fun p => Real.log (cellNorm (y p)))

/-- Iwasawa form of `w_M n_M(x) a` for a positive diagonal `a`. -/
theorem swapGL_unip_torus (x : ℕ → ℝ) (α : Fin N → ℝ) :
    S.swapGL * S.unip x * RealIwasawa.torus α =
      (RealIwasawa.torus (α ∘ S.perm + S.cellExponent (shifted x α)) * S.unip (shifted x α) *
          RealIwasawa.torus (-(α ∘ S.perm + S.cellExponent (shifted x α)))) *
        RealIwasawa.torus (α ∘ S.perm + S.cellExponent (shifted x α)) *
        (S.rot (fun p => Real.arctan (shifted x α p)) * S.swapGL) := by
  have h1 : S.swapGL * S.unip x * RealIwasawa.torus α =
      RealIwasawa.torus (α ∘ S.perm) * (S.swapGL * S.unip (shifted x α)) := by
    rw [mul_assoc, unip_mul_torus, ← mul_assoc, swapGL_mul_torus, mul_assoc]
    rfl
  rw [h1, swapGL_mul_unip, diagE_eq_torus, RealIwasawa.torus_neg, RealIwasawa.torus_add]
  unfold cellExponent
  group

/-- The slot coordinates of a matrix: its entries at the positions `(p, p + 1)`. -/
def slotCoord (u : Langlands.GeneralLinear N ℝ) (p : ℕ) : ℝ :=
  if h : p + 1 < N then (u : Matrix (Fin N) (Fin N) ℝ) ⟨p, by omega⟩ ⟨p + 1, h⟩ else 0

theorem slotCoord_eq (u : Langlands.GeneralLinear N ℝ) {p : ℕ} (hp : p ∈ S.starts) :
    slotCoord u p = (u : Matrix (Fin N) (Fin N) ℝ) (first hp) (second hp) := by
  simp [slotCoord, S.lt p hp, first, second]

/-- A slot unipotent followed by a unipotent element: move the part of the latter outside
the slots to the left. -/
theorem unip_mul_unipotent (x : ℕ → ℝ) (n : Langlands.GeneralLinear.upperUnipotent N ℝ) :
    ∃ u ∈ Langlands.GeneralLinear.upperUnipotent N ℝ,
      (∀ p (hp : p ∈ S.starts), (u : Matrix (Fin N) (Fin N) ℝ) (first hp) (second hp) = 0) ∧
      S.unip x * (n : Langlands.GeneralLinear N ℝ) = u * S.unip (x + slotCoord (n : Langlands.GeneralLinear N ℝ)) := by
  let a : Langlands.GeneralLinear.upperUnipotent N ℝ := ⟨S.unip x, S.unip_mem x⟩
  let b : Langlands.GeneralLinear.upperUnipotent N ℝ :=
    ⟨S.unip (-(x + slotCoord (n : Langlands.GeneralLinear N ℝ))), S.unip_mem _⟩
  refine ⟨(a * n * b : Langlands.GeneralLinear.upperUnipotent N ℝ), (a * n * b).property, ?_, ?_⟩
  · intro p hp
    have hab : (second hp).val = (first hp).val + 1 := rfl
    rw [unipotent_mul_adjacent _ _ _ _ hab, unipotent_mul_adjacent _ _ _ _ hab]
    change (S.unip x : Matrix (Fin N) (Fin N) ℝ) (first hp) (second hp) +
      ((n : Langlands.GeneralLinear N ℝ) : Matrix (Fin N) (Fin N) ℝ) (first hp) (second hp) +
      (S.unip (-(x + slotCoord (n : Langlands.GeneralLinear N ℝ))) : Matrix (Fin N) (Fin N) ℝ) (first hp) (second hp) = 0
    rw [unip_slot_entry, unip_slot_entry, Pi.neg_apply, Pi.add_apply, slotCoord_eq _ hp]
    ring
  · change S.unip x * (n : Langlands.GeneralLinear N ℝ) =
      S.unip x * (n : Langlands.GeneralLinear N ℝ) * S.unip (-(x + slotCoord (n : Langlands.GeneralLinear N ℝ))) *
        S.unip (x + slotCoord (n : Langlands.GeneralLinear N ℝ))
    rw [mul_assoc (S.unip x * _), unip_mul, neg_add_cancel, unip_zero, mul_one]

/-- The Iwasawa decomposition of `w_M n_M(x) g` in terms of that of `g`. -/
theorem swapGL_unip_mul (x : ℕ → ℝ) (g : Langlands.GeneralLinear N ℝ) :
    ∃ v ∈ Langlands.GeneralLinear.upperUnipotent N ℝ,
      S.swapGL * S.unip x * g =
        v * RealIwasawa.torus (RealIwasawa.alpha g ∘ S.perm +
            S.cellExponent (shifted (x + slotCoord (RealIwasawa.npart g : Langlands.GeneralLinear N ℝ)) (RealIwasawa.alpha g))) *
          (S.rot (fun p => Real.arctan
              (shifted (x + slotCoord (RealIwasawa.npart g : Langlands.GeneralLinear N ℝ)) (RealIwasawa.alpha g) p)) *
            S.swapGL * (RealIwasawa.kpart g : Langlands.GeneralLinear N ℝ)) := by
  obtain ⟨u, hu, hslot, he⟩ := S.unip_mul_unipotent x (RealIwasawa.npart g)
  set c := x + slotCoord (RealIwasawa.npart g : Langlands.GeneralLinear N ℝ)
  set α := RealIwasawa.alpha g
  set γ := α ∘ S.perm + S.cellExponent (shifted c α)
  have hconj := S.swapGL_conj_mem hu hslot
  have hc : RealIwasawa.torus γ * S.unip (shifted c α) * RealIwasawa.torus (-γ) ∈
      Langlands.GeneralLinear.upperUnipotent N ℝ :=
    RealIwasawa.conjTorus_mem γ ⟨S.unip (shifted c α), S.unip_mem _⟩
  refine ⟨(S.swapGL * u * S.swapGL⁻¹) *
      (RealIwasawa.torus γ * S.unip (shifted c α) * RealIwasawa.torus (-γ)),
    Subgroup.mul_mem _ hconj hc, ?_⟩
  conv_lhs => rw [← RealIwasawa.npart_mul_torus_mul_kpart g]
  have key : S.swapGL * S.unip c * RealIwasawa.torus α =
      (RealIwasawa.torus γ * S.unip (shifted c α) * RealIwasawa.torus (-γ)) *
        RealIwasawa.torus γ * (S.rot (fun p => Real.arctan (shifted c α p)) * S.swapGL) :=
    S.swapGL_unip_torus c α
  calc S.swapGL * S.unip x * ((RealIwasawa.npart g : Langlands.GeneralLinear N ℝ) *
        RealIwasawa.torus α * (RealIwasawa.kpart g : Langlands.GeneralLinear N ℝ))
      = (S.swapGL * u * S.swapGL⁻¹) * (S.swapGL * S.unip c * RealIwasawa.torus α) *
          (RealIwasawa.kpart g : Langlands.GeneralLinear N ℝ) := by
        have : S.swapGL * S.unip x * ((RealIwasawa.npart g : Langlands.GeneralLinear N ℝ) *
            RealIwasawa.torus α * (RealIwasawa.kpart g : Langlands.GeneralLinear N ℝ)) =
            S.swapGL * (S.unip x * (RealIwasawa.npart g : Langlands.GeneralLinear N ℝ)) *
            RealIwasawa.torus α * (RealIwasawa.kpart g : Langlands.GeneralLinear N ℝ) := by group
        rw [this, he]
        group
    _ = _ := by
        rw [key]
        simp only [mul_assoc]


theorem alpha_swapGL_unip_mul (x : ℕ → ℝ) (g : Langlands.GeneralLinear N ℝ) :
    RealIwasawa.alpha (S.swapGL * S.unip x * g) =
      RealIwasawa.alpha g ∘ S.perm + S.cellExponent
        (shifted (x + slotCoord (RealIwasawa.npart g : Langlands.GeneralLinear N ℝ))
          (RealIwasawa.alpha g)) := by
  obtain ⟨v, hv, he⟩ := S.swapGL_unip_mul x g
  rw [he]
  have hk : S.rot (fun p => Real.arctan
      (shifted (x + slotCoord (RealIwasawa.npart g : Langlands.GeneralLinear N ℝ))
        (RealIwasawa.alpha g) p)) * S.swapGL * (RealIwasawa.kpart g : Langlands.GeneralLinear N ℝ) ∈
      Langlands.Archimedean.unitaryCompact ℝ N :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (S.rot_mem _) S.swapGL_mem) (RealIwasawa.kpart g).property
  exact RealIwasawa.alpha_iwasawa ⟨v, hv⟩ _ ⟨_, hk⟩

theorem kpart_swapGL_unip_mul (x : ℕ → ℝ) (g : Langlands.GeneralLinear N ℝ) :
    (RealIwasawa.kpart (S.swapGL * S.unip x * g) : Langlands.GeneralLinear N ℝ) =
      S.rot (fun p => Real.arctan
          (shifted (x + slotCoord (RealIwasawa.npart g : Langlands.GeneralLinear N ℝ))
            (RealIwasawa.alpha g) p)) *
        S.swapGL * (RealIwasawa.kpart g : Langlands.GeneralLinear N ℝ) := by
  obtain ⟨v, hv, he⟩ := S.swapGL_unip_mul x g
  rw [he]
  have hk : S.rot (fun p => Real.arctan
      (shifted (x + slotCoord (RealIwasawa.npart g : Langlands.GeneralLinear N ℝ))
        (RealIwasawa.alpha g) p)) * S.swapGL * (RealIwasawa.kpart g : Langlands.GeneralLinear N ℝ) ∈
      Langlands.Archimedean.unitaryCompact ℝ N :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (S.rot_mem _) S.swapGL_mem) (RealIwasawa.kpart g).property
  exact congrArg Subtype.val (RealIwasawa.kpart_iwasawa ⟨v, hv⟩ _ ⟨_, hk⟩)

theorem slotVec_perm (u : ℕ → ℝ) (j : Fin N) :
    S.slotVec u (-u) (S.perm j) = -S.slotVec u (-u) j := by
  rcases S.inSlot_or j with ⟨p, o, h⟩ | h
  · have h' := S.inSlot_swapFun h
    rw [perm_apply, S.slotVec_of_inSlot _ _ h', S.slotVec_of_inSlot _ _ h]
    obtain rfl | rfl : o = 0 ∨ o = 1 := by fin_cases o <;> simp
    · simp
    · simp
  · rw [perm_apply, S.not_inSlot_swapFun h, S.slotVec_of_not_inSlot _ _ h, neg_zero]

/-- A weight invariant under the slot swap does not see the cell exponents, and sees
permuted exponents as the original ones. -/
theorem sum_mul_perm_add_cellExponent {w : Fin N → ℝ} (hw : ∀ j, w (S.perm j) = w j)
    (α : Fin N → ℝ) (y : ℕ → ℝ) :
    ∑ j, w j * (α ∘ S.perm + S.cellExponent y) j = ∑ j, w j * α j := by
  simp only [Pi.add_apply, Function.comp, mul_add, Finset.sum_add_distrib]
  have h1 : ∑ j, w j * α (S.perm j) = ∑ j, w j * α j := by
    calc ∑ j, w j * α (S.perm j) = ∑ j, w (S.perm j) * α (S.perm j) := by simp only [hw]
      _ = ∑ j, w j * α j := Equiv.sum_comp S.perm (fun j => w j * α j)
  have h2 : ∑ j, w j * S.cellExponent y j = 0 := by
    have hc : S.cellExponent y = S.slotVec (fun p => -Real.log (cellNorm (y p)))
        (-(fun p => -Real.log (cellNorm (y p)))) := by
      unfold cellExponent
      congr 1
      funext p
      simp
    rw [hc]
    set s := S.slotVec (fun p => -Real.log (cellNorm (y p))) (-(fun p => -Real.log (cellNorm (y p))))
    have hs : ∑ j, w j * s j = -∑ j, w j * s j := by
      calc ∑ j, w j * s j = ∑ j, w (S.perm j) * s (S.perm j) :=
            (Equiv.sum_comp S.perm (fun j => w j * s j)).symm
        _ = ∑ j, w j * (-s j) := by simp only [hw, s, slotVec_perm]
        _ = -∑ j, w j * s j := by simp [Finset.sum_neg_distrib]
    linarith
  rw [h1, h2, add_zero]

end SlotSet

end Langlands.Global.RankinSelbergGlobal.RealLeviStages
