import Langlands.GroupScheme.Composition.CayleyFrameGrading

/-! # The Peirce frame of an isotropic Cayley datum and its `ℤ²`-grading -/

noncomputable section

universe u v w

open Matrix

namespace Langlands.GroupScheme.CayleyDatum

variable {K : Type u} [Field K] (c : CayleyDatum K)

local notation "μ" => c.multiplication

/-- A nonzero vector of norm zero yields a vector of norm zero and trace one. -/
theorem exists_norm_eq_zero_trace_eq_one {x : CayleyVector K} (hx : x ≠ 0)
    (hN : c.norm x = 0) : ∃ e, c.norm e = 0 ∧ c.trace e = 1 := by
  have hy : ∃ y, c.trace (μ x y) ≠ 0 := by
    by_contra h
    push_neg at h
    have h1 : c.trace x • c.unit - x = 0 := by
      apply c.eq_zero_of_forall_form_eq_zero
      intro w
      have hw := h w
      rw [c.trace_mul] at hw
      rw [map_sub, map_smul, smul_eq_mul, c.form_comm w x]
      exact hw
    have h2 : x = c.trace x • c.unit := (sub_eq_zero.mp h1).symm
    have h3 : c.trace x * c.trace x = 0 := by
      have h4 := congrArg c.norm h2
      rw [QuadraticMap.map_smul, c.norm_unit, hN, smul_eq_mul, mul_one] at h4
      exact h4.symm
    have h5 : c.trace x = 0 := mul_self_eq_zero.mp h3
    apply hx
    rw [h2, h5, zero_smul]
  obtain ⟨y, hy⟩ := hy
  refine ⟨μ x ((c.trace (μ x y))⁻¹ • y), ?_, ?_⟩
  · rw [c.norm_mul, hN, zero_mul]
  · rw [map_smul, c.trace_smul, inv_mul_cancel₀ hy]

/-- `z` lies in the Peirce space `U(e) = {z : ez = z, T(z) = 0, b(z, e) = 0}`. -/
def InPeirce (e z : CayleyVector K) : Prop :=
  μ e z = z ∧ c.trace z = 0 ∧ c.form z e = 0

/-- A pair of vectors `e + f = 1` with `N(e) = 0` and `T(e) = 1`. -/
structure IsPeircePair (e f : CayleyVector K) : Prop where
  norm_left : c.norm e = 0
  trace_left : c.trace e = 1
  add_eq : e + f = c.unit

section Repeated

variable {c}

/-- `b(zz, w) = 0` when `N(z) = T(z) = 0`. -/
theorem form_mul_self_eq_zero {z : CayleyVector K} (hN : c.norm z = 0) (hT : c.trace z = 0)
    (w : CayleyVector K) : c.form (μ z z) w = 0 := by
  simp [c.mul_self, hT, hN]

/-- `b(zw, z) = 0` when `N(z) = 0`. -/
theorem form_mul_left_self_eq_zero {z : CayleyVector K} (hN : c.norm z = 0)
    (w : CayleyVector K) : c.form (μ z w) z = 0 := by
  have h := c.form_mul_mul_left z w c.unit
  rw [c.mul_unit, hN, zero_mul] at h
  exact h

/-- `b(wz, z) = 0` when `N(z) = 0`. -/
theorem form_mul_right_self_eq_zero {z : CayleyVector K} (hN : c.norm z = 0)
    (w : CayleyVector K) : c.form (μ w z) z = 0 := by
  have h := c.form_mul_mul_right z w c.unit
  rw [c.unit_mul, hN, zero_mul] at h
  exact h

end Repeated

namespace IsPeircePair

variable {c} {e f : CayleyVector K} (P : c.IsPeircePair e f)
include P

theorem eq_sub : f = c.unit - e := eq_sub_iff_add_eq'.mpr P.add_eq

theorem form_left_left : c.form e e = 0 := by
  rw [c.form_self, P.norm_left, mul_zero]

theorem trace_right : c.trace f = 1 := by
  rw [P.eq_sub, c.trace_sub, c.trace_unit, P.trace_left]
  norm_num

theorem norm_right : c.norm f = 0 := by
  have h : c.form c.unit (-e) = -1 := by
    rw [map_neg, c.form_comm]
    exact congrArg Neg.neg P.trace_left
  rw [P.eq_sub, sub_eq_add_neg, c.norm_add, QuadraticMap.map_neg, c.norm_unit, P.norm_left, h]
  ring

theorem symm : c.IsPeircePair f e :=
  ⟨P.norm_right, P.trace_right, by rw [add_comm, P.add_eq]⟩

theorem mul_left_left : μ e e = e := by
  rw [c.mul_self, P.trace_left, P.norm_left, one_smul, zero_smul, sub_zero]

theorem mul_left_right : μ e f = 0 := by
  rw [P.eq_sub, map_sub, c.mul_unit, P.mul_left_left, sub_self]

theorem form_left_right : c.form e f = 1 := by
  rw [P.eq_sub, map_sub, P.form_left_left, sub_zero]
  exact P.trace_left

theorem mul_right_apply (w : CayleyVector K) : μ f w = w - μ e w := by
  rw [P.eq_sub, map_sub, LinearMap.sub_apply, c.unit_mul]

theorem form_right_apply (w : CayleyVector K) : c.form w f = c.trace w - c.form w e := by
  rw [P.eq_sub, map_sub]
  rfl

/-- Membership in the Peirce space of `f = 1 - e`, expressed through `e`. -/
theorem inPeirce_right_iff {w : CayleyVector K} :
    c.InPeirce f w ↔ μ e w = 0 ∧ c.trace w = 0 ∧ c.form w e = 0 := by
  unfold InPeirce
  rw [P.mul_right_apply, P.form_right_apply]
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨by simpa using h1, h2, ?_⟩
    rw [h2, zero_sub, neg_eq_zero] at h3
    exact h3
  · rintro ⟨h1, h2, h3⟩
    exact ⟨by rw [h1, sub_zero], h2, by rw [h2, h3, sub_zero]⟩

variable {z z' w : CayleyVector K}

theorem norm_eq_zero (hz : c.InPeirce e z) : c.norm z = 0 := by
  rw [← hz.1, c.norm_mul, P.norm_left, zero_mul]

theorem mul_right_left (hz : c.InPeirce e z) : μ z e = 0 := by
  have h := c.mul_add_mul_comm e z
  simp only [hz.1, P.trace_left, hz.2.1, c.form_comm e z, hz.2.2, one_smul, zero_smul,
    add_zero, sub_zero] at h
  simpa using h

theorem mul_right_right (hz : c.InPeirce e z) : μ z f = z := by
  rw [P.eq_sub, map_sub, c.mul_unit, P.mul_right_left hz, sub_zero]

theorem mul_left_of (hz : c.InPeirce e z) : μ f z = 0 := by
  rw [P.mul_right_apply, hz.1, sub_self]

theorem form_right (hz : c.InPeirce e z) : c.form z f = 0 := by
  rw [P.form_right_apply, hz.2.1, hz.2.2, sub_zero]

/-- The Peirce space `U(e)` is totally isotropic. -/
theorem form_eq_zero (hz : c.InPeirce e z) (hz' : c.InPeirce e z') : c.form z z' = 0 := by
  have h := c.form_mul_mul_left e z z'
  rw [hz.1, hz'.1, P.norm_left, zero_mul] at h
  exact h

/-- `U(e) U(e) ⊆ U(1 - e)`. -/
theorem mul_mem (hz : c.InPeirce e z) (hz' : c.InPeirce e z') : c.InPeirce f (μ z z') := by
  rw [P.inPeirce_right_iff]
  refine ⟨?_, ?_, ?_⟩
  · have h := c.mul_mul_left₂ e z z'
    rw [P.trace_left, hz.2.1, hz'.1, c.form_comm e z, hz.2.2] at h
    calc μ e (μ z z') = (0 : K) • z' -
          ((1 : K) • μ z z' - μ e (μ z z') + ((0 : K) • z' - μ z z')) := by
            simp only [one_smul, zero_smul]
            abel
      _ = 0 := by rw [h, sub_self]
  · rw [c.trace_mul, hz.2.1, P.form_eq_zero hz hz', zero_mul, sub_zero]
  · have h := c.form_mul_left z z' e
    rw [P.mul_right_left hz, map_zero, add_zero, hz.2.1, zero_mul] at h
    exact h

theorem form_mul_mul_mem (hz : c.InPeirce e z) (hz' : c.InPeirce e z') (hw : c.InPeirce f w) :
    c.form (μ z z') w = 0 :=
  P.symm.form_eq_zero (P.mul_mem hz hz') hw

theorem form_mul_mem_mul (hz : c.InPeirce e z) (hz' : c.InPeirce e z') (hw : c.InPeirce f w) :
    c.form (μ z w) z' = 0 := by
  have h := c.form_mul_left z w z'
  rw [hz.2.1, zero_mul, P.symm.form_eq_zero hw (P.mul_mem hz hz'), add_zero] at h
  exact h

theorem form_mem_mul_mul (hz : c.InPeirce e z) (hz' : c.InPeirce e z') (hw : c.InPeirce f w) :
    c.form (μ w z) z' = 0 := by
  have h := c.form_mul_right z w z'
  rw [hz.2.1, zero_mul, P.symm.form_eq_zero hw (P.mul_mem hz' hz), add_zero] at h
  exact h

end IsPeircePair

theorem eq_not_of_ne_bool {s t : Bool} (h : t ≠ s) : t = !s := by
  cases s <;> cases t <;> simp_all

/-- A Peirce frame: a vector `e` of norm zero and trace one, three vectors `u a` in the
Peirce space `U(e)`, and three vectors `v a` in `U(1 - e)` with `b(u a, v b) = δ_ab`. -/
structure PeirceFrame where
  /-- The vector of norm zero and trace one. -/
  e : CayleyVector K
  /-- Three vectors in the Peirce space `U(e)`. -/
  u : Fin 3 → CayleyVector K
  /-- Three vectors in the Peirce space `U(1 - e)`, dual to `u` under `b`. -/
  v : Fin 3 → CayleyVector K
  norm_e : c.norm e = 0
  trace_e : c.trace e = 1
  mem_u : ∀ a, μ e (u a) = u a ∧ c.trace (u a) = 0 ∧ c.form (u a) e = 0
  mem_v : ∀ a, μ e (v a) = 0 ∧ c.trace (v a) = 0 ∧ c.form (v a) e = 0
  form_uv : ∀ a b, c.form (u a) (v b) = if a = b then 1 else 0

/-- The index type `Bool ⊕ (Bool × Fin 3)` of a Peirce frame. -/
abbrev PeirceIndex := Bool ⊕ (Bool × Fin 3)

/-- The involution of the Peirce index: `e ↔ 1 - e` and `u a ↔ v a`. -/
def peirceDual : PeirceIndex → PeirceIndex
  | Sum.inl s => Sum.inl (!s)
  | Sum.inr p => Sum.inr (!p.1, p.2)

/-- The weights of a Peirce frame: zero on `e` and `1 - e`, `ε a` on `u a`, `-ε a` on `v a`. -/
def peirceWeight {M : Type v} [AddCommGroup M] (ε : Fin 3 → M) : PeirceIndex → M
  | Sum.inl _ => 0
  | Sum.inr (true, a) => ε a
  | Sum.inr (false, a) => -ε a

/-- The Peirce space side of a frame index. -/
def peirceSide : PeirceIndex → Bool
  | Sum.inl s => s
  | Sum.inr p => p.1

/-- The right Peirce side of a frame index. -/
def peirceRightSide : PeirceIndex → Bool
  | Sum.inl s => s
  | Sum.inr p => !p.1

theorem peirceDual_dual (i : PeirceIndex) : peirceDual (peirceDual i) = i := by
  rcases i with s | ⟨s, a⟩ <;> simp [peirceDual]

theorem peirceWeight_dual {M : Type v} [AddCommGroup M] (ε : Fin 3 → M) (i : PeirceIndex) :
    peirceWeight ε (peirceDual i) = -peirceWeight ε i := by
  rcases i with s | ⟨s, a⟩
  · simp [peirceDual, peirceWeight]
  · cases s <;> simp [peirceDual, peirceWeight]

theorem sum_eps_eq_zero {M : Type v} [AddCommGroup M] {ε : Fin 3 → M}
    (hε : ε 0 + ε 1 + ε 2 = 0) {a b d : Fin 3} (hab : a ≠ b) (had : a ≠ d) (hbd : b ≠ d) :
    ε a + ε b + ε d = 0 := by
  have hna : a ∉ ({b, d} : Finset (Fin 3)) := by simp [hab, had]
  have h1 : ({a, b, d} : Finset (Fin 3)) = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [Finset.card_insert_of_notMem hna, Finset.card_pair hbd]
    rfl
  have h2 : ∑ i ∈ ({a, b, d} : Finset (Fin 3)), ε i = ε a + ε b + ε d := by
    rw [Finset.sum_insert hna, Finset.sum_pair hbd, add_assoc]
  rw [← h2, h1, Fin.sum_univ_three, hε]

namespace PeirceFrame

variable {c} (D : c.PeirceFrame)

/-- The two complementary vectors `e` and `1 - e`. -/
def E : Bool → CayleyVector K
  | true => D.e
  | false => c.unit - D.e

/-- The Peirce vectors: `u` in `U(e)` and `v` in `U(1 - e)`. -/
def F : Bool → Fin 3 → CayleyVector K
  | true => D.u
  | false => D.v

theorem pair_true : c.IsPeircePair D.e (c.unit - D.e) :=
  ⟨D.norm_e, D.trace_e, by abel⟩

theorem pair : ∀ s, c.IsPeircePair (D.E s) (D.E (!s))
  | true => D.pair_true
  | false => D.pair_true.symm

theorem pair' (s : Bool) : c.IsPeircePair (D.E (!s)) (D.E s) := by
  cases s
  · exact D.pair_true
  · exact D.pair_true.symm

theorem mem : ∀ s a, c.InPeirce (D.E s) (D.F s a)
  | true, a => D.mem_u a
  | false, a => D.pair_true.inPeirce_right_iff.mpr (D.mem_v a)

theorem trace_F (s : Bool) (a : Fin 3) : c.trace (D.F s a) = 0 := (D.mem s a).2.1

theorem E_mul_E (s t : Bool) : μ (D.E s) (D.E t) = if t = s then D.E s else 0 := by
  by_cases h : t = s
  · subst h
    rw [if_pos rfl]
    exact (D.pair t).mul_left_left
  · obtain rfl := eq_not_of_ne_bool h
    rw [if_neg h]
    exact (D.pair s).mul_left_right

theorem E_mul_F (s t : Bool) (a : Fin 3) :
    μ (D.E s) (D.F t a) = if t = s then D.F t a else 0 := by
  by_cases h : t = s
  · subst h
    rw [if_pos rfl]
    exact (D.mem t a).1
  · obtain rfl := eq_not_of_ne_bool h
    rw [if_neg h]
    exact (D.pair' s).mul_left_of (D.mem (!s) a)

theorem F_mul_E (s t : Bool) (a : Fin 3) :
    μ (D.F t a) (D.E s) = if t = s then 0 else D.F t a := by
  by_cases h : t = s
  · subst h
    rw [if_pos rfl]
    exact (D.pair t).mul_right_left (D.mem t a)
  · obtain rfl := eq_not_of_ne_bool h
    rw [if_neg h]
    exact (D.pair' s).mul_right_right (D.mem (!s) a)

theorem form_E_E (s t : Bool) : c.form (D.E s) (D.E t) = if t = !s then 1 else 0 := by
  by_cases h : t = s
  · subst h
    rw [if_neg (by cases t <;> simp)]
    exact (D.pair t).form_left_left
  · obtain rfl := eq_not_of_ne_bool h
    rw [if_pos rfl]
    exact (D.pair s).form_left_right

theorem form_F_E (s t : Bool) (a : Fin 3) : c.form (D.F t a) (D.E s) = 0 := by
  by_cases h : t = s
  · subst h
    exact (D.mem t a).2.2
  · obtain rfl := eq_not_of_ne_bool h
    exact (D.pair' s).form_right (D.mem (!s) a)

theorem form_E_F (s t : Bool) (a : Fin 3) : c.form (D.E s) (D.F t a) = 0 := by
  rw [c.form_comm]
  exact D.form_F_E s t a

theorem form_F_F (s t : Bool) (a b : Fin 3) :
    c.form (D.F s a) (D.F t b) = if t = !s ∧ b = a then 1 else 0 := by
  cases s <;> cases t
  · rw [if_neg (by simp)]
    exact (D.pair false).form_eq_zero (D.mem false a) (D.mem false b)
  · change c.form (D.v a) (D.u b) = _
    rw [c.form_comm, D.form_uv]
    by_cases h : b = a
    · subst h
      simp
    · simp [h]
  · change c.form (D.u a) (D.v b) = _
    rw [D.form_uv]
    by_cases h : a = b
    · subst h
      simp
    · simp [h, Ne.symm h]
  · rw [if_neg (by simp)]
    exact (D.pair true).form_eq_zero (D.mem true a) (D.mem true b)

/-- The trilinear form `b(xy, z)` on Peirce vectors vanishes unless all three lie in the
same Peirce space and have pairwise distinct indices. -/
theorem form_F_F_F (s t r : Bool) (a b d : Fin 3) :
    c.form (μ (D.F s a) (D.F t b)) (D.F r d) = 0 ∨
      (s = t ∧ t = r ∧ a ≠ b ∧ a ≠ d ∧ b ≠ d) := by
  by_cases hst : s = t
  · subst hst
    by_cases hsr : s = r
    · subst hsr
      have hN : ∀ x, c.norm (D.F s x) = 0 := fun x => (D.pair s).norm_eq_zero (D.mem s x)
      by_cases hab : a = b
      · subst hab
        exact Or.inl (form_mul_self_eq_zero (hN a) (D.trace_F s a) _)
      by_cases had : a = d
      · subst had
        exact Or.inl (form_mul_left_self_eq_zero (hN a) _)
      by_cases hbd : b = d
      · subst hbd
        exact Or.inl (form_mul_right_self_eq_zero (hN b) _)
      exact Or.inr ⟨rfl, rfl, hab, had, hbd⟩
    · obtain rfl := eq_not_of_ne_bool (Ne.symm hsr)
      exact Or.inl ((D.pair s).form_mul_mul_mem (D.mem s a) (D.mem s b) (D.mem (!s) d))
  · by_cases htr : t = r
    · subst htr
      obtain rfl := eq_not_of_ne_bool hst
      exact Or.inl ((D.pair t).form_mem_mul_mul (D.mem t b) (D.mem t d) (D.mem (!t) a))
    · have hrs : r = s := by cases r <;> cases s <;> cases t <;> simp_all
      subst hrs
      obtain rfl := eq_not_of_ne_bool (Ne.symm hst)
      exact Or.inl ((D.pair r).form_mul_mem_mul (D.mem r a) (D.mem r d) (D.mem (!r) b))

/-- The eight frame vectors. -/
def vec : PeirceIndex → CayleyVector K
  | Sum.inl s => D.E s
  | Sum.inr p => D.F p.1 p.2

theorem mul_vec_left (s : Bool) (j : PeirceIndex) :
    μ (D.E s) (D.vec j) = if peirceSide j = s then D.vec j else 0 := by
  rcases j with t | ⟨t, a⟩
  · change μ (D.E s) (D.E t) = if t = s then D.E t else 0
    rw [D.E_mul_E]
    split_ifs with h
    · rw [h]
    · rfl
  · change μ (D.E s) (D.F t a) = if t = s then D.F t a else 0
    exact D.E_mul_F s t a

theorem mul_vec_right (s : Bool) (j : PeirceIndex) :
    μ (D.vec j) (D.E s) = if peirceRightSide j = s then D.vec j else 0 := by
  rcases j with t | ⟨t, a⟩
  · change μ (D.E t) (D.E s) = if t = s then D.E t else 0
    rw [D.E_mul_E]
    cases t <;> cases s <;> simp
  · change μ (D.F t a) (D.E s) = if (!t) = s then D.F t a else 0
    rw [D.F_mul_E]
    cases t <;> cases s <;> simp

theorem form_vec (i j : PeirceIndex) :
    c.form (D.vec i) (D.vec j) = if j = peirceDual i then 1 else 0 := by
  rcases i with s | ⟨s, a⟩ <;> rcases j with t | ⟨t, b⟩
  · change c.form (D.E s) (D.E t) = _
    rw [D.form_E_E]
    simp [peirceDual]
  · change c.form (D.E s) (D.F t b) = _
    rw [D.form_E_F]
    simp [peirceDual]
  · change c.form (D.F s a) (D.E t) = _
    rw [D.form_F_E]
    simp [peirceDual]
  · change c.form (D.F s a) (D.F t b) = _
    rw [D.form_F_F]
    simp [peirceDual]

theorem trace_vec_of_weight {M : Type v} [AddCommGroup M] (ε : Fin 3 → M) (i : PeirceIndex)
    (hi : peirceWeight ε i ≠ 0) : c.form c.unit (D.vec i) = 0 := by
  rcases i with s | ⟨s, a⟩
  · exact absurd rfl hi
  · rw [c.form_comm]
    exact D.trace_F s a

theorem form_mul_vec {M : Type v} [AddCommGroup M] {ε : Fin 3 → M} (hε : ε 0 + ε 1 + ε 2 = 0)
    (i j l : PeirceIndex)
    (h : peirceWeight ε i + peirceWeight ε j + peirceWeight ε l ≠ 0) :
    c.form (μ (D.vec i) (D.vec j)) (D.vec l) = 0 := by
  rcases i with s | ⟨s, a⟩
  · change c.form (μ (D.E s) (D.vec j)) (D.vec l) = 0
    rw [D.mul_vec_left]
    split_ifs
    · rw [D.form_vec]
      split_ifs with hl
      · exfalso
        apply h
        rw [hl, peirceWeight_dual]
        simp [peirceWeight]
      · rfl
    · rw [map_zero, LinearMap.zero_apply]
  · rcases j with t | ⟨t, b⟩
    · change c.form (μ (D.vec (Sum.inr (s, a))) (D.E t)) (D.vec l) = 0
      rw [D.mul_vec_right]
      split_ifs
      · rw [D.form_vec]
        split_ifs with hl
        · exfalso
          apply h
          rw [hl, peirceWeight_dual]
          simp [peirceWeight]
        · rfl
      · rw [map_zero, LinearMap.zero_apply]
    · rcases l with r | ⟨r, d⟩
      · have h3 := c.form_mul_right (D.F t b) (D.F s a) (D.E r)
        rw [D.trace_F, zero_mul] at h3
        change c.form (μ (D.F s a) (D.F t b)) (D.E r) = 0
        rw [eq_neg_of_add_eq_zero_left h3]
        change -c.form (D.vec (Sum.inr (s, a))) (μ (D.E r) (D.vec (Sum.inr (t, b)))) = 0
        rw [D.mul_vec_left]
        split_ifs
        · rw [D.form_vec]
          split_ifs with hl
          · exfalso
            apply h
            rw [hl, peirceWeight_dual]
            simp [peirceWeight]
          · rw [neg_zero]
        · rw [map_zero, neg_zero]
      · rcases D.form_F_F_F s t r a b d with h0 | ⟨rfl, rfl, hab, had, hbd⟩
        · exact h0
        · exfalso
          apply h
          have hs := sum_eps_eq_zero hε hab had hbd
          cases s
          · change -ε a + -ε b + -ε d = 0
            rw [← neg_add, ← neg_add, hs, neg_zero]
          · exact hs

/-- **The weighted frame of a Peirce frame**, with weights given by `ε` summing to zero. -/
def weightedFrame {M : Type v} [AddCommGroup M] (ε : Fin 3 → M) (hε : ε 0 + ε 1 + ε 2 = 0) :
    c.WeightedFrame PeirceIndex M where
  vec := D.vec
  dual := peirceDual
  weight := peirceWeight ε
  dual_dual := peirceDual_dual
  card_eq := rfl
  form_vec := D.form_vec
  weight_dual := peirceWeight_dual ε
  form_unit := D.trace_vec_of_weight ε
  form_mul := D.form_mul_vec hε

/-- The two standard weights and their negative sum, in `ℤ²` indexed by `ULift (Fin 2)`. -/
def stdEps : Fin 3 → (ULift.{w} (Fin 2) → ℤ) :=
  ![Pi.single ⟨0⟩ 1, Pi.single ⟨1⟩ 1, -(Pi.single ⟨0⟩ 1 + Pi.single ⟨1⟩ 1)]

theorem stdEps_sum : stdEps.{w} 0 + stdEps 1 + stdEps 2 = 0 := by
  simp [stdEps]

include D in
/-- **A Peirce frame gives a `ℤ²`-grading whose degrees generate `ℤ²`.** -/
theorem exists_grading :
    ∃ g : c.Grading (ULift.{w} (Fin 2) → ℤ),
      AddSubgroup.closure (g.support : Set (ULift.{w} (Fin 2) → ℤ)) = ⊤ := by
  classical
  refine ⟨(D.weightedFrame stdEps stdEps_sum).toGrading, ?_⟩
  rw [eq_top_iff]
  rintro f -
  have hs : ∀ i : ULift.{w} (Fin 2),
      (Pi.single i 1 : ULift.{w} (Fin 2) → ℤ) ∈
        AddSubgroup.closure (((D.weightedFrame stdEps stdEps_sum).toGrading.support :
          Finset (ULift.{w} (Fin 2) → ℤ)) : Set (ULift.{w} (Fin 2) → ℤ)) := by
    rintro ⟨i⟩
    apply AddSubgroup.subset_closure
    rw [WeightedFrame.toGrading_support, Finset.coe_image, Finset.coe_univ, Set.image_univ]
    fin_cases i
    · exact ⟨Sum.inr (true, 0), rfl⟩
    · exact ⟨Sum.inr (true, 1), rfl⟩
  have hf : f = ∑ i, f i • (Pi.single i 1 : ULift.{w} (Fin 2) → ℤ) := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  rw [hf]
  exact AddSubgroup.sum_mem _ fun i _ => AddSubgroup.zsmul_mem _ (hs i) _

end PeirceFrame

end Langlands.GroupScheme.CayleyDatum
