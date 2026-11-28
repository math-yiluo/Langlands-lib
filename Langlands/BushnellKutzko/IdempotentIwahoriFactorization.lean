import Langlands.BushnellKutzko.UnitFiltration
import Langlands.BushnellKutzko.SplittingBasis

/-! # Block decompositions attached to an idempotent -/

open ValuativeRel

noncomputable section

namespace Langlands.BushnellKutzko.BlockIdempotent

universe uA uF uV

section Ring

variable {A : Type uA} [Ring A]

/-- The unipotent radical `{g : g e = e, (1 - e) g = 1 - e}` attached to `e`: in a
decomposition `1 = e + (1 - e)`, the units `1 + y` with `y = e y (1 - e)`. -/
def upperGroup (e : A) : Subgroup Aˣ where
  carrier := {g | (g : A) * e = e ∧ (1 - e) * (g : A) = 1 - e}
  one_mem' := ⟨one_mul e, mul_one _⟩
  mul_mem' := by
    rintro g h ⟨hg1, hg2⟩ ⟨hh1, hh2⟩
    refine ⟨?_, ?_⟩
    · rw [Units.val_mul, mul_assoc, hh1, hg1]
    · rw [Units.val_mul, ← mul_assoc, hg2, hh2]
  inv_mem' := by
    rintro g ⟨hg1, hg2⟩
    refine ⟨?_, ?_⟩
    · calc ((g⁻¹ : Aˣ) : A) * e = ((g⁻¹ : Aˣ) : A) * ((g : A) * e) := by rw [hg1]
        _ = e := by rw [← mul_assoc, Units.inv_mul, one_mul]
    · calc (1 - e) * ((g⁻¹ : Aˣ) : A) = (1 - e) * (g : A) * ((g⁻¹ : Aˣ) : A) := by rw [hg2]
        _ = 1 - e := by rw [mul_assoc, Units.mul_inv, mul_one]

/-- The opposite unipotent radical, attached to `1 - e`. -/
abbrev lowerGroup (e : A) : Subgroup Aˣ := upperGroup (1 - e)

/-- The Levi subgroup: the units commuting with `e`. -/
def leviGroup (e : A) : Subgroup Aˣ where
  carrier := {g | (g : A) * e = e * (g : A)}
  one_mem' := by simp
  mul_mem' := by
    rintro g h hg hh
    change (g : A) * (h : A) * e = e * ((g : A) * (h : A))
    rw [mul_assoc, hh, ← mul_assoc, hg, mul_assoc]
  inv_mem' := by
    rintro g hg
    change ((g⁻¹ : Aˣ) : A) * e = e * ((g⁻¹ : Aˣ) : A)
    calc ((g⁻¹ : Aˣ) : A) * e = ((g⁻¹ : Aˣ) : A) * (e * (g : A)) * ((g⁻¹ : Aˣ) : A) := by
          rw [mul_assoc, mul_assoc, Units.mul_inv, mul_one]
      _ = ((g⁻¹ : Aˣ) : A) * ((g : A) * e) * ((g⁻¹ : Aˣ) : A) := by
          rw [show e * (g : A) = (g : A) * e from hg.symm]
      _ = e * ((g⁻¹ : Aˣ) : A) := by rw [← mul_assoc, Units.inv_mul, one_mul]

theorem mem_upperGroup {e : A} {g : Aˣ} :
    g ∈ upperGroup e ↔ (g : A) * e = e ∧ (1 - e) * (g : A) = 1 - e := Iff.rfl

theorem mem_leviGroup {e : A} {g : Aˣ} :
    g ∈ leviGroup e ↔ (g : A) * e = e * (g : A) := Iff.rfl

variable {e : A}

theorem mul_one_sub_eq_zero (he : IsIdempotentElem e) : e * (1 - e) = 0 := by
  rw [mul_sub, mul_one, he.eq, sub_self]

theorem one_sub_mul_eq_zero (he : IsIdempotentElem e) : (1 - e) * e = 0 := by
  rw [sub_mul, one_mul, he.eq, sub_self]

/-- For `g` in the unipotent radical, `g - 1 = e (g - 1) (1 - e)`. -/
theorem sub_one_eq_of_mem_upperGroup {g : Aˣ} (hg : g ∈ upperGroup e) :
    (g : A) - 1 = e * ((g : A) - 1) ∧ ((g : A) - 1) * e = 0 := by
  obtain ⟨h1, h2⟩ := hg
  refine ⟨?_, ?_⟩
  · have : (1 - e) * ((g : A) - 1) = 0 := by rw [mul_sub, h2, mul_one, sub_self]
    calc (g : A) - 1 = e * ((g : A) - 1) + (1 - e) * ((g : A) - 1) := by noncomm_ring
      _ = e * ((g : A) - 1) := by rw [this, add_zero]
  · rw [sub_mul, h1, one_mul, sub_self]

theorem sub_one_mul_sub_one_of_mem_upperGroup {g : Aˣ} (hg : g ∈ upperGroup e) :
    ((g : A) - 1) * ((g : A) - 1) = 0 := by
  obtain ⟨h1, h2⟩ := sub_one_eq_of_mem_upperGroup hg
  calc ((g : A) - 1) * ((g : A) - 1) = ((g : A) - 1) * (e * ((g : A) - 1)) := by rw [← h1]
    _ = ((g : A) - 1) * e * ((g : A) - 1) := by rw [mul_assoc]
    _ = 0 := by rw [h2, zero_mul]

theorem val_inv_of_mem_upperGroup {g : Aˣ} (hg : g ∈ upperGroup e) :
    ((g⁻¹ : Aˣ) : A) = 1 - ((g : A) - 1) := by
  have hsq := sub_one_mul_sub_one_of_mem_upperGroup hg
  have hmul : (g : A) * (1 - ((g : A) - 1)) = 1 := by
    calc (g : A) * (1 - ((g : A) - 1)) = 1 - ((g : A) - 1) * ((g : A) - 1) := by noncomm_ring
      _ = 1 := by rw [hsq, sub_zero]
  calc ((g⁻¹ : Aˣ) : A) = ((g⁻¹ : Aˣ) : A) * ((g : A) * (1 - ((g : A) - 1))) := by
        rw [hmul, mul_one]
    _ = 1 - ((g : A) - 1) := by rw [← mul_assoc, Units.inv_mul, one_mul]

/-- A central unit commutes, together with its inverse, with every element. -/
theorem inv_comm_of_comm (c : Aˣ) (hc : ∀ a : A, (c : A) * a = a * c) (a : A) :
    ((c⁻¹ : Aˣ) : A) * a = a * ((c⁻¹ : Aˣ) : A) := by
  calc ((c⁻¹ : Aˣ) : A) * a = ((c⁻¹ : Aˣ) : A) * (a * ((c : A) * ((c⁻¹ : Aˣ) : A))) := by
        rw [Units.mul_inv, mul_one]
    _ = ((c⁻¹ : Aˣ) : A) * ((a * c) * ((c⁻¹ : Aˣ) : A)) := by rw [mul_assoc]
    _ = ((c⁻¹ : Aˣ) : A) * (((c : A) * a) * ((c⁻¹ : Aˣ) : A)) := by rw [hc]
    _ = (((c⁻¹ : Aˣ) : A) * c) * a * ((c⁻¹ : Aˣ) : A) := by noncomm_ring
    _ = a * ((c⁻¹ : Aˣ) : A) := by rw [Units.inv_mul, one_mul]

/-- The contraction `ζ = c e + (1 - e)` attached to an idempotent `e` and a central unit `c`. -/
def contraction (he : IsIdempotentElem e) (c : Aˣ) (hc : ∀ a : A, (c : A) * a = a * c) : Aˣ where
  val := c * e + (1 - e)
  inv := ((c⁻¹ : Aˣ) : A) * e + (1 - e)
  val_inv := by
    have h1 : e * (1 - e) = 0 := mul_one_sub_eq_zero he
    have h2 : (1 - e) * e = 0 := one_sub_mul_eq_zero he
    have h3 : (1 - e) * (1 - e) = 1 - e := (he.one_sub).eq
    have hc' := inv_comm_of_comm c hc
    calc ((c : A) * e + (1 - e)) * (((c⁻¹ : Aˣ) : A) * e + (1 - e))
        = (c : A) * (e * (((c⁻¹ : Aˣ) : A) * e)) + (c : A) * (e * (1 - e)) +
            (1 - e) * (((c⁻¹ : Aˣ) : A) * e) + (1 - e) * (1 - e) := by
          noncomm_ring
      _ = 1 := by
          rw [h1, h3, ← mul_assoc e, ← hc' e, mul_assoc _ e e, he.eq, ← mul_assoc (1 - e),
            ← hc' (1 - e), mul_assoc _ (1 - e) e, h2, ← mul_assoc, Units.mul_inv]
          noncomm_ring
  inv_val := by
    have h1 : e * (1 - e) = 0 := mul_one_sub_eq_zero he
    have h2 : (1 - e) * e = 0 := one_sub_mul_eq_zero he
    have h3 : (1 - e) * (1 - e) = 1 - e := (he.one_sub).eq
    calc (((c⁻¹ : Aˣ) : A) * e + (1 - e)) * ((c : A) * e + (1 - e))
        = ((c⁻¹ : Aˣ) : A) * (e * ((c : A) * e)) + ((c⁻¹ : Aˣ) : A) * (e * (1 - e)) +
            (1 - e) * ((c : A) * e) + (1 - e) * (1 - e) := by
          noncomm_ring
      _ = 1 := by
          rw [h1, h3, ← mul_assoc e, ← hc e, mul_assoc _ e e, he.eq, ← mul_assoc (1 - e),
            ← hc (1 - e), mul_assoc _ (1 - e) e, h2, ← mul_assoc, Units.inv_mul]
          noncomm_ring

variable (he : IsIdempotentElem e) (c : Aˣ) (hc : ∀ a : A, (c : A) * a = a * c)

theorem val_contraction : (contraction he c hc : A) = c * e + (1 - e) := rfl

theorem val_contraction_inv :
    ((contraction he c hc)⁻¹ : Aˣ) = ((c⁻¹ : Aˣ) : A) * e + (1 - e) := rfl

include he hc in
/-- Conjugation by the contraction multiplies `g - 1` by `c` on the unipotent radical. -/
theorem val_conj_upper {g : Aˣ} (hg : g ∈ upperGroup e) :
    ((contraction he c hc * g * (contraction he c hc)⁻¹ : Aˣ) : A) = 1 + c * ((g : A) - 1) := by
  obtain ⟨h1, h2⟩ := sub_one_eq_of_mem_upperGroup hg
  have hgy : (g : A) = 1 + ((g : A) - 1) := by abel
  generalize (g : A) - 1 = y at h1 h2 hgy ⊢
  have hc' := inv_comm_of_comm c hc
  have hZZi : ((c : A) * e + (1 - e)) * (((c⁻¹ : Aˣ) : A) * e + (1 - e)) = 1 := by
    rw [← val_contraction he c hc, ← val_contraction_inv he c hc, Units.mul_inv]
  have hZy : ((c : A) * e + (1 - e)) * y = c * y := by
    calc ((c : A) * e + (1 - e)) * y = c * (e * y) + (y - e * y) := by noncomm_ring
      _ = c * y := by rw [← h1, sub_self, add_zero]
  have hyZi : (c : A) * y * (((c⁻¹ : Aˣ) : A) * e + (1 - e)) = c * y := by
    calc (c : A) * y * (((c⁻¹ : Aˣ) : A) * e + (1 - e))
        = c * (y * ((c⁻¹ : Aˣ) : A)) * e + (c * y - c * (y * e)) := by noncomm_ring
      _ = c * (((c⁻¹ : Aˣ) : A) * y) * e + (c * y - c * (y * e)) := by rw [hc' y]
      _ = ((c : A) * ((c⁻¹ : Aˣ) : A)) * (y * e) + (c * y - c * (y * e)) := by noncomm_ring
      _ = c * y := by rw [h2, Units.mul_inv]; noncomm_ring
  rw [Units.val_mul, Units.val_mul, val_contraction, val_contraction_inv, hgy]
  calc ((c : A) * e + (1 - e)) * (1 + y) * (((c⁻¹ : Aˣ) : A) * e + (1 - e))
      = ((c : A) * e + (1 - e)) * (((c⁻¹ : Aˣ) : A) * e + (1 - e)) +
          ((c : A) * e + (1 - e)) * y * (((c⁻¹ : Aˣ) : A) * e + (1 - e)) := by noncomm_ring
    _ = 1 + c * y := by rw [hZZi, hZy, hyZi]

include he hc in
/-- Conjugation by the inverse contraction multiplies `g - 1` by `c` on the opposite radical. -/
theorem val_conj_lower {g : Aˣ} (hg : g ∈ lowerGroup e) :
    (((contraction he c hc)⁻¹ * g * contraction he c hc : Aˣ) : A) = 1 + c * ((g : A) - 1) := by
  obtain ⟨h1, h2⟩ := sub_one_eq_of_mem_upperGroup hg
  have hgy : (g : A) = 1 + ((g : A) - 1) := by abel
  generalize (g : A) - 1 = y at h1 h2 hgy ⊢
  have hc' := inv_comm_of_comm c hc
  have hZiZ : (((c⁻¹ : Aˣ) : A) * e + (1 - e)) * ((c : A) * e + (1 - e)) = 1 := by
    rw [← val_contraction he c hc, ← val_contraction_inv he c hc, Units.inv_mul]
  have hey : e * y = 0 := by
    rw [h1, ← mul_assoc, mul_one_sub_eq_zero he, zero_mul]
  have hye : y * e = y := by
    have h3 : y * (1 - e) = 0 := h2
    rw [mul_sub, mul_one, sub_eq_zero] at h3
    exact h3.symm
  have hZiy : (((c⁻¹ : Aˣ) : A) * e + (1 - e)) * y = y := by
    calc (((c⁻¹ : Aˣ) : A) * e + (1 - e)) * y = ((c⁻¹ : Aˣ) : A) * (e * y) + (y - e * y) := by
          noncomm_ring
      _ = y := by rw [hey]; noncomm_ring
  have hyZ : y * ((c : A) * e + (1 - e)) = c * y := by
    calc y * ((c : A) * e + (1 - e)) = (y * c) * e + (y - y * e) := by noncomm_ring
      _ = (c * y) * e + (y - y * e) := by rw [hc y]
      _ = c * y := by rw [mul_assoc, hye, sub_self, add_zero]
  rw [Units.val_mul, Units.val_mul, val_contraction, val_contraction_inv, hgy]
  calc (((c⁻¹ : Aˣ) : A) * e + (1 - e)) * (1 + y) * ((c : A) * e + (1 - e))
      = (((c⁻¹ : Aˣ) : A) * e + (1 - e)) * ((c : A) * e + (1 - e)) +
          (((c⁻¹ : Aˣ) : A) * e + (1 - e)) * y * ((c : A) * e + (1 - e)) := by noncomm_ring
    _ = 1 + c * y := by rw [hZiZ, hZiy, hyZ]

include he hc in
theorem pow_conj_upper (r : ℕ) {g : Aˣ} (hg : g ∈ upperGroup e) :
    contraction he c hc ^ r * g * (contraction he c hc ^ r)⁻¹ ∈ upperGroup e ∧
      ((contraction he c hc ^ r * g * (contraction he c hc ^ r)⁻¹ : Aˣ) : A) =
        1 + (c : A) ^ r * ((g : A) - 1) := by
  induction r with
  | zero => simpa using hg
  | succ r ih =>
    obtain ⟨hmem, hval⟩ := ih
    set k := contraction he c hc ^ r * g * (contraction he c hc ^ r)⁻¹
    have e1 : contraction he c hc ^ (r + 1) * g * (contraction he c hc ^ (r + 1))⁻¹ =
        contraction he c hc * k * (contraction he c hc)⁻¹ := by
      simp only [k]; group
    rw [e1]
    have hv := val_conj_upper he c hc hmem
    obtain ⟨h1, h2⟩ := sub_one_eq_of_mem_upperGroup hmem
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [hv, add_mul, one_mul, mul_assoc, h2, mul_zero, add_zero]
    · rw [hv, mul_add, mul_one, ← mul_assoc, ← hc (1 - e), mul_assoc,
        show (1 - e) * ((k : A) - 1) = 0 by rw [sub_mul, one_mul, ← h1, sub_self], mul_zero,
        add_zero]
    · rw [hv, hval, add_sub_cancel_left, ← mul_assoc, ← pow_succ']

include he hc in
theorem pow_conj_lower (r : ℕ) {g : Aˣ} (hg : g ∈ lowerGroup e) :
    (contraction he c hc ^ r)⁻¹ * g * contraction he c hc ^ r ∈ lowerGroup e ∧
      (((contraction he c hc ^ r)⁻¹ * g * contraction he c hc ^ r : Aˣ) : A) =
        1 + (c : A) ^ r * ((g : A) - 1) := by
  induction r with
  | zero => simpa using hg
  | succ r ih =>
    obtain ⟨hmem, hval⟩ := ih
    set k := (contraction he c hc ^ r)⁻¹ * g * contraction he c hc ^ r
    have e1 : (contraction he c hc ^ (r + 1))⁻¹ * g * contraction he c hc ^ (r + 1) =
        (contraction he c hc)⁻¹ * k * contraction he c hc := by
      simp only [k]; group
    rw [e1]
    have hv := val_conj_lower he c hc hmem
    obtain ⟨h1, h2⟩ := sub_one_eq_of_mem_upperGroup hmem
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [hv, add_mul, one_mul, mul_assoc, h2, mul_zero, add_zero]
    · rw [hv, mul_add, mul_one, ← mul_assoc, ← hc (1 - (1 - e)), mul_assoc,
        show (1 - (1 - e)) * ((k : A) - 1) = 0 by rw [sub_mul, one_mul, ← h1, sub_self],
        mul_zero, add_zero]
    · rw [hv, hval, add_sub_cancel_left, ← mul_assoc, ← pow_succ']

include hc in
theorem contraction_comm_levi {g : Aˣ} (hg : g ∈ leviGroup e) :
    contraction he c hc * g = g * contraction he c hc := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, val_contraction, add_mul, mul_add, mul_assoc, ← hg,
    ← mul_assoc, hc (g : A), mul_assoc, sub_mul, mul_sub, one_mul, mul_one, hg]

end Ring

section Block

variable {A : Type uA} [Ring A] {e f : A}

/-- Corner identities for complementary idempotents `e + f = 1`. -/
structure IsComplementary (e f : A) : Prop where
  add_eq : e + f = 1
  ee : e * e = e
  ff : f * f = f
  ef : e * f = 0
  fe : f * e = 0

theorem isComplementary_of_isIdempotentElem {e : A} (he : IsIdempotentElem e) :
    IsComplementary e (1 - e) where
  add_eq := by abel
  ee := he.eq
  ff := he.one_sub.eq
  ef := mul_one_sub_eq_zero he
  fe := one_sub_mul_eq_zero he

namespace IsComplementary

variable (h : IsComplementary e f)
include h

theorem one_sub : 1 - e = f := by rw [← h.add_eq]; abel

theorem ee' (y : A) : e * (e * y) = e * y := by rw [← mul_assoc, h.ee]
theorem ff' (y : A) : f * (f * y) = f * y := by rw [← mul_assoc, h.ff]
theorem ef' (y : A) : e * (f * y) = 0 := by rw [← mul_assoc, h.ef, zero_mul]
theorem fe' (y : A) : f * (e * y) = 0 := by rw [← mul_assoc, h.fe, zero_mul]

/-- Block LU identities: let `D` be an inverse of the corner `d = f x f` in `f A f`. Then
`u = 1 + (e x f) D` and `l = 1 + D (f x e)` are inverse to `1 - (e x f) D` and `1 - D (f x e)`,
and `(1 - (e x f) D) x (1 - D (f x e))` commutes with `e`. -/
theorem levi_comm (x D : A) (heD : e * D = 0) (hDe : D * e = 0)
    (hdD : f * x * f * D = f) (hDd : D * (f * x * f) = f) :
    (1 - e * x * f * D) * x * (1 - D * (f * x * e)) * e =
      e * ((1 - e * x * f * D) * x * (1 - D * (f * x * e))) := by
  have hD : D = f * D := by
    calc D = (e + f) * D := by rw [h.add_eq, one_mul]
      _ = f * D := by rw [add_mul, heD, zero_add]
  have hD' : D = D * f := by
    calc D = D * (e + f) := by rw [h.add_eq, mul_one]
      _ = D * f := by rw [mul_add, hDe, zero_add]
  -- the lower left corner of the middle factor vanishes
  have hlow : f * ((1 - e * x * f * D) * x * (1 - D * (f * x * e))) * e = 0 := by
    have h1 : f * (1 - e * x * f * D) = f := by
      rw [mul_sub, mul_one, show e * x * f * D = e * (x * f * D) by simp only [mul_assoc],
        h.fe', sub_zero]
    have h2 : f * x * D = f := by
      calc f * x * D = f * x * (f * D) := by rw [← hD]
        _ = f * x * f * D := by simp only [mul_assoc]
        _ = f := hdD
    calc f * ((1 - e * x * f * D) * x * (1 - D * (f * x * e))) * e
        = f * (1 - e * x * f * D) * x * (1 - D * (f * x * e)) * e := by simp only [mul_assoc]
      _ = f * x * e - f * x * D * (f * x * e) * e := by rw [h1]; noncomm_ring
      _ = 0 := by
          rw [h2]
          simp only [mul_assoc, h.ee, h.ff', sub_self]
  -- the upper right corner of the middle factor vanishes
  have hup : e * ((1 - e * x * f * D) * x * (1 - D * (f * x * e))) * f = 0 := by
    have h1 : (1 - D * (f * x * e)) * f = f := by
      rw [sub_mul, one_mul, show D * (f * x * e) * f = D * (f * x * (e * f)) by
        simp only [mul_assoc], h.ef, mul_zero, mul_zero, sub_zero]
    have h2 : D * x * f = f := by
      calc D * x * f = D * f * x * f := by rw [← hD']
        _ = D * (f * x * f) := by simp only [mul_assoc]
        _ = f := hDd
    calc e * ((1 - e * x * f * D) * x * (1 - D * (f * x * e))) * f
        = e * (1 - e * x * f * D) * x * ((1 - D * (f * x * e)) * f) := by simp only [mul_assoc]
      _ = e * x * f - e * (e * x * f) * (D * x * f) := by rw [h1]; noncomm_ring
      _ = 0 := by
          rw [h2]
          simp only [mul_assoc, h.ee', h.ff, sub_self]
  set m := (1 - e * x * f * D) * x * (1 - D * (f * x * e))
  calc m * e = (e + f) * m * e := by rw [h.add_eq, one_mul]
    _ = e * m * e + f * m * e := by noncomm_ring
    _ = e * m * e + e * m * f := by rw [hlow, hup]
    _ = e * m * (e + f) := by noncomm_ring
    _ = e * m := by rw [h.add_eq, mul_one]

end IsComplementary

end Block

section LatticeFactor

variable {F : Type uF} [Field F] [ValuativeRel F] {V : Type uV} [AddCommGroup V] [Module F V]

local notation "A" => Module.End F V
local notation "G" => (Module.End F V)ˣ

variable (L : LatticeChain 𝒪[F] F V) (R : Subalgebra 𝒪[F] (Module.End F V))
  (Jg : Subgroup (Module.End F V)ˣ)
  (hJ : ∀ g : (Module.End F V)ˣ, g ∈ Jg ↔ g ∈ L.unitFiltration 0 ∧ (g : Module.End F V) ∈ R)

/-- The unit `1 + y` for `y` with `y² = 0`, with inverse `1 - y`. -/
def unitOfSqZero (y : A) (hy : y * y = 0) : G where
  val := 1 + y
  inv := 1 - y
  val_inv := by rw [show (1 + y) * (1 - y) = 1 - y * y by noncomm_ring, hy, sub_zero]
  inv_val := by rw [show (1 - y) * (1 + y) = 1 - y * y by noncomm_ring, hy, sub_zero]

include hJ in
theorem unitOfSqZero_mem {y : A} (hy : y * y = 0) (hyR : y ∈ R) (hyO : y ∈ L.order) :
    unitOfSqZero y hy ∈ Jg := by
  rw [hJ, L.mem_unitFiltration_zero]
  refine ⟨⟨add_mem (one_mem _) hyO, sub_mem (one_mem _) hyO⟩, add_mem (one_mem _) hyR⟩

include hJ in
theorem exists_mem_of_mem_endFiltration_one {y : A} (hyR : y ∈ R)
    (hy : y ∈ L.endFiltration 1) : ∃ g ∈ Jg, (g : A) = 1 + y := by
  obtain ⟨g, hg, hgv⟩ := L.exists_mem_unitFiltration (n := 1) le_rfl (by exact_mod_cast hy)
  refine ⟨g, (hJ g).mpr ⟨L.unitFiltration_antitone (Nat.zero_le 1) hg, ?_⟩, hgv⟩
  rw [hgv]
  exact add_mem (one_mem _) hyR

include hJ in
/-- **Iwahori factorization relative to an idempotent.** Let `R ⊆ 𝔄` be an `𝔬_F`-subalgebra,
`J = {g ∈ U(𝔄) : g ∈ R}` and `e ∈ R` an idempotent such that `e x (1 - e)` and `(1 - e) x e`
lie in `𝔓 = End^1(𝓛)` for every `x ∈ 𝔄`. Then every `j ∈ J` is a product `u m l` with `u ∈ J`
in the unipotent radical of `e`, `m ∈ J` commuting with `e` and `l ∈ J` in the opposite
radical. -/
theorem exists_factor (hRL : ∀ x ∈ R, x ∈ L.order) {e : A} (he : IsIdempotentElem e)
    (heR : e ∈ R)
    (hoff : ∀ x ∈ L.order,
      e * x * (1 - e) ∈ L.endFiltration 1 ∧ (1 - e) * x * e ∈ L.endFiltration 1)
    (j : G) (hj : j ∈ Jg) :
    ∃ u ∈ Jg ⊓ upperGroup e, ∃ m ∈ Jg ⊓ leviGroup e, ∃ l ∈ Jg ⊓ lowerGroup e,
      j = u * m * l := by
  set f : A := 1 - e with hfdef
  have h : IsComplementary e f := isComplementary_of_isIdempotentElem he
  have hfR : f ∈ R := sub_mem (one_mem _) heR
  set x : A := (j : A) with hxdef
  set x' : A := ((j⁻¹ : G) : A) with hx'def
  have hxR : x ∈ R := ((hJ j).mp hj).2
  have hx'R : x' ∈ R := ((hJ _).mp (Jg.inv_mem hj)).2
  have hxO := hRL x hxR
  have hx'O := hRL x' hx'R
  have hxx' : x * x' = 1 := Units.mul_inv j
  have hx'x : x' * x = 1 := Units.inv_mul j
  have hle : ∀ {y : A}, y ∈ L.endFiltration 1 → y ∈ L.order := fun hy =>
    L.endFiltration_antitone (show (0 : ℤ) ≤ 1 by norm_num) hy
  have h1mul : ∀ {y w : A}, y ∈ L.endFiltration 1 → w ∈ L.endFiltration 1 →
      y * w ∈ L.endFiltration 1 := fun hy hw =>
    L.endFiltration_antitone (show (1 : ℤ) ≤ 1 + 1 by norm_num) (L.mul_mem_endFiltration hy hw)
  -- the corner units `1 - (f x e)(e x' f)` and `1 - (f x' e)(e x f)`
  have hcb : -(f * x * e * (e * x' * f)) ∈ L.endFiltration 1 :=
    neg_mem (h1mul (hoff x hxO).2 (hoff x' hx'O).1)
  have hcb2 : -(f * x' * e * (e * x * f)) ∈ L.endFiltration 1 :=
    neg_mem (h1mul (hoff x' hx'O).2 (hoff x hxO).1)
  obtain ⟨z, hzJ, hzv⟩ := exists_mem_of_mem_endFiltration_one L R Jg hJ
    (neg_mem (mul_mem (mul_mem (mul_mem hfR hxR) heR) (mul_mem (mul_mem heR hx'R) hfR))) hcb
  obtain ⟨z2, hz2J, hz2v⟩ := exists_mem_of_mem_endFiltration_one L R Jg hJ
    (neg_mem (mul_mem (mul_mem (mul_mem hfR hx'R) heR) (mul_mem (mul_mem heR hxR) hfR))) hcb2
  have hzl : z ∈ leviGroup e := by
    rw [mem_leviGroup, hzv]
    simp only [mul_add, add_mul, mul_one, one_mul, mul_neg, neg_mul, mul_assoc, h.fe, h.ef',
      mul_zero, neg_zero, add_zero]
  have hz2l : z2 ∈ leviGroup e := by
    rw [mem_leviGroup, hz2v]
    simp only [mul_add, add_mul, mul_one, one_mul, mul_neg, neg_mul, mul_assoc, h.fe, h.ef',
      mul_zero, neg_zero, add_zero]
  set zi : A := ((z⁻¹ : G) : A)
  set zi2 : A := ((z2⁻¹ : G) : A)
  have hzie : zi * e = e * zi := (leviGroup e).inv_mem hzl
  have hzi2e : zi2 * e = e * zi2 := (leviGroup e).inv_mem hz2l
  have hzif : zi * f = f * zi := by
    rw [hfdef, mul_sub, sub_mul, mul_one, one_mul, hzie]
  have hzi2f : zi2 * f = f * zi2 := by
    rw [hfdef, mul_sub, sub_mul, mul_one, one_mul, hzi2e]
  set D : A := f * x' * f * zi with hDdef
  have heD : e * D = 0 := by simp only [hDdef, mul_assoc, h.ef']
  have hDe : D * e = 0 := by
    rw [hDdef, mul_assoc, hzie, ← mul_assoc, show f * x' * f * e = f * x' * (f * e) by
      simp only [mul_assoc], h.fe, mul_zero, zero_mul]
  -- `(f x f)(f x' f) = f z` and `(f x' f)(f x f) = z2 f`
  have hf1 : f * x * f * (f * x' * f) = f * (z : A) := by
    have key : f = f * x * e * x' * f + f * x * f * x' * f := by
      calc f = f * (x * x') * f := by rw [hxx', mul_one, h.ff]
        _ = f * x * (e + f) * x' * f := by rw [h.add_eq]; noncomm_ring
        _ = f * x * e * x' * f + f * x * f * x' * f := by noncomm_ring
    rw [hzv]
    calc f * x * f * (f * x' * f) = f * x * f * x' * f := by
          simp only [mul_assoc, h.ff']
      _ = f - f * x * e * x' * f := by rw [eq_sub_iff_add_eq, add_comm, ← key]
      _ = f * (1 + -(f * x * e * (e * x' * f))) := by
          simp only [mul_add, mul_one, mul_neg, mul_assoc, h.ff', h.ee']
          abel
  have hf2 : f * x' * f * (f * x * f) = (z2 : A) * f := by
    have key : f = f * x' * e * x * f + f * x' * f * x * f := by
      calc f = f * (x' * x) * f := by rw [hx'x, mul_one, h.ff]
        _ = f * x' * (e + f) * x * f := by rw [h.add_eq]; noncomm_ring
        _ = f * x' * e * x * f + f * x' * f * x * f := by noncomm_ring
    rw [hz2v]
    calc f * x' * f * (f * x * f) = f * x' * f * x * f := by
          simp only [mul_assoc, h.ff']
      _ = f - f * x' * e * x * f := by rw [eq_sub_iff_add_eq, add_comm, ← key]
      _ = (1 + -(f * x' * e * (e * x * f))) * f := by
          simp only [add_mul, one_mul, neg_mul, mul_assoc, h.ff, h.ee']
          abel
  have hdD : f * x * f * D = f := by
    calc f * x * f * D = f * x * f * (f * x' * f) * zi := by simp only [hDdef, mul_assoc]
      _ = f * ((z : A) * zi) := by rw [hf1, mul_assoc]
      _ = f := by rw [Units.mul_inv, mul_one]
  have hDd : D * (f * x * f) = f := by
    set D2 : A := zi2 * (f * x' * f)
    have hD2 : D2 * (f * x * f) = f := by
      calc D2 * (f * x * f) = zi2 * (f * x' * f * (f * x * f)) := by simp only [D2, mul_assoc]
        _ = f := by rw [hf2, ← mul_assoc, Units.inv_mul, one_mul]
    have hD2f : D2 * f = D2 := by simp only [D2, mul_assoc, h.ff]
    have hfD : f * D = D := by simp only [hDdef, ← mul_assoc, h.ff]
    have hDeq : D = D2 := by
      calc D = f * D := hfD.symm
        _ = D2 * (f * x * f) * D := by rw [hD2]
        _ = D2 * (f * x * f * D) := by simp only [mul_assoc]
        _ = D2 := by rw [hdD, hD2f]
    rw [hDeq, hD2]
  -- the three factors
  have hDb : D * (e * x * f) = 0 := by
    rw [← mul_assoc, ← mul_assoc, hDe, zero_mul, zero_mul]
  have hcD : f * x * e * D = 0 := by rw [mul_assoc, heD, mul_zero]
  have hbDsq : e * x * f * D * (e * x * f * D) = 0 := by
    calc e * x * f * D * (e * x * f * D) = e * x * f * (D * (e * x * f)) * D := by
          simp only [mul_assoc]
      _ = 0 := by rw [hDb, mul_zero, zero_mul]
  have hDcsq : D * (f * x * e) * (D * (f * x * e)) = 0 := by
    calc D * (f * x * e) * (D * (f * x * e)) = D * (f * x * e * D) * (f * x * e) := by
          simp only [mul_assoc]
      _ = 0 := by rw [hcD, mul_zero, zero_mul]
  have hDR : D ∈ R := mul_mem (mul_mem (mul_mem hfR hx'R) hfR) ((hJ _).mp (Jg.inv_mem hzJ)).2
  have hDO := hRL D hDR
  have hbR : e * x * f ∈ R := mul_mem (mul_mem heR hxR) hfR
  have hcR : f * x * e ∈ R := mul_mem (mul_mem hfR hxR) heR
  let u := unitOfSqZero (e * x * f * D) hbDsq
  let l := unitOfSqZero (D * (f * x * e)) hDcsq
  have huJ : u ∈ Jg := unitOfSqZero_mem L R Jg hJ hbDsq (mul_mem hbR hDR)
    (hRL _ (mul_mem hbR hDR))
  have hlJ : l ∈ Jg := unitOfSqZero_mem L R Jg hJ hDcsq (mul_mem hDR hcR)
    (hRL _ (mul_mem hDR hcR))
  have huU : u ∈ upperGroup e := by
    refine ⟨?_, ?_⟩
    · change (1 + e * x * f * D) * e = e
      rw [add_mul, one_mul, mul_assoc, hDe, mul_zero, add_zero]
    · change f * (1 + e * x * f * D) = f
      rw [mul_add, mul_one, show f * (e * x * f * D) = f * e * x * f * D by
        simp only [mul_assoc], h.fe, zero_mul, zero_mul, zero_mul, add_zero]
  have hlU : l ∈ lowerGroup e := by
    refine ⟨?_, ?_⟩
    · change (1 + D * (f * x * e)) * f = f
      rw [add_mul, one_mul, show D * (f * x * e) * f = D * (f * x * (e * f)) by
        simp only [mul_assoc], h.ef, mul_zero, mul_zero, add_zero]
    · change (1 - f) * (1 + D * (f * x * e)) = 1 - f
      rw [show (1 : A) - f = e by rw [hfdef]; abel, mul_add, mul_one, ← mul_assoc, heD, zero_mul,
        add_zero]
  let m := u⁻¹ * j * l⁻¹
  have hmJ : m ∈ Jg := Jg.mul_mem (Jg.mul_mem (Jg.inv_mem huJ) hj) (Jg.inv_mem hlJ)
  have hmv : (m : A) = (1 - e * x * f * D) * x * (1 - D * (f * x * e)) := rfl
  have hmL : m ∈ leviGroup e := by
    rw [mem_leviGroup, hmv]
    exact h.levi_comm x D heD hDe hdD hDd
  refine ⟨u, ⟨huJ, huU⟩, m, ⟨hmJ, hmL⟩, l, ⟨hlJ, hlU⟩, ?_⟩
  simp only [m]
  group

end LatticeFactor

section LatticeContraction

variable {F : Type uF} [Field F] [ValuativeRel F] {V : Type uV} [AddCommGroup V] [Module F V]

local notation "A" => Module.End F V
local notation "G" => (Module.End F V)ˣ

variable (L : LatticeChain 𝒪[F] F V) (R : Subalgebra 𝒪[F] (Module.End F V))
  (Jg : Subgroup (Module.End F V)ˣ)
  (hJ : ∀ g : (Module.End F V)ˣ, g ∈ Jg ↔ g ∈ L.unitFiltration 0 ∧ (g : Module.End F V) ∈ R)

/-- The scalar unit `a · 1` of `End_F(V)` for `a ∈ F` nonzero. -/
def scalarUnit (a : F) (ha : a ≠ 0) : G :=
  Units.map (algebraMap F (Module.End F V)).toMonoidHom (Units.mk0 a ha)

omit [ValuativeRel F] in
theorem val_scalarUnit (a : F) (ha : a ≠ 0) :
    ((scalarUnit (V := V) a ha : G) : A) = algebraMap F A a := rfl

omit [ValuativeRel F] in
theorem scalarUnit_comm (a : F) (ha : a ≠ 0) (x : A) :
    ((scalarUnit (V := V) a ha : G) : A) * x = x * ((scalarUnit (V := V) a ha : G) : A) :=
  Algebra.commutes a x

include hJ in
/-- An element of the unipotent radical of an idempotent whose difference with `1` lies in `R`
lies in `J`. -/
theorem mem_of_mem_upperGroup (hRL : ∀ x ∈ R, x ∈ L.order) {e : A} {k : G}
    (hk : k ∈ upperGroup e) (hkR : (k : A) - 1 ∈ R) : k ∈ Jg := by
  obtain ⟨h1, h2⟩ := sub_one_eq_of_mem_upperGroup hk
  have hsq : ((k : A) - 1) * ((k : A) - 1) = 0 := by
    calc ((k : A) - 1) * ((k : A) - 1) = ((k : A) - 1) * (e * ((k : A) - 1)) := by rw [← h1]
      _ = ((k : A) - 1) * e * ((k : A) - 1) := by rw [mul_assoc]
      _ = 0 := by rw [h2, zero_mul]
  have hk' : k = unitOfSqZero ((k : A) - 1) hsq := Units.ext (by simp [unitOfSqZero])
  rw [hk']
  exact unitOfSqZero_mem L R Jg hJ hsq hkR (hRL _ hkR)

include hJ in
/-- Elements of `J` in the radicals of `e` lie in `J^1 = {g ∈ U^1(𝔄) : g ∈ R}`. -/
theorem mem_unitFiltration_one_of_mem_upperGroup {e : A} (he : IsIdempotentElem e)
    (hoff : ∀ x ∈ L.order, e * x * (1 - e) ∈ L.endFiltration 1) {k : G} (hkJ : k ∈ Jg)
    (hk : k ∈ upperGroup e) : k ∈ L.unitFiltration 1 := by
  obtain ⟨h1, h2⟩ := sub_one_eq_of_mem_upperGroup hk
  have hkO := ((hJ k).mp hkJ).1
  refine ⟨hkO.1, hkO.2.1, ?_⟩
  have : (k : A) - 1 = e * (k : A) * (1 - e) := by
    calc (k : A) - 1 = e * ((k : A) - 1) * (1 - e) := by
          rw [mul_sub (e * ((k : A) - 1)), mul_one, mul_assoc e, h2, mul_zero, sub_zero, ← h1]
      _ = e * (k : A) * (1 - e) - e * (1 - e) := by noncomm_ring
      _ = e * (k : A) * (1 - e) := by rw [mul_one_sub_eq_zero he, sub_zero]
  rw [this]
  exact hoff _ hkO.1

variable [TopologicalSpace F] [IsNonarchimedeanLocalField F]

/-- Every endomorphism has a multiple by a power of a uniformizer in an `𝔬_F`-submodule of full
rank. -/
theorem exists_pow_smul_mem {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ) (M : Submodule 𝒪[F] A)
    (hM : Submodule.span F (M : Set A) = ⊤) (y : A) : ∃ r : ℕ, ((ϖ : F) ^ r) • y ∈ M := by
  have hy : y ∈ Submodule.span F (M : Set A) := by rw [hM]; trivial
  have hpow : ∀ (k : ℕ) {z : A}, z ∈ M → ((ϖ : F) ^ k) • z ∈ M := by
    intro k z hz
    have : ((ϖ : F) ^ k) • z = (ϖ ^ k : 𝒪[F]) • z := by
      rw [← algebraMap_smul F (ϖ ^ k : 𝒪[F]) z, map_pow]
      rfl
    rw [this]
    exact M.smul_mem _ hz
  induction hy using Submodule.span_induction with
  | mem z hz => exact ⟨0, by simpa using hz⟩
  | zero => exact ⟨0, by simp⟩
  | add z w _ _ hz hw =>
    obtain ⟨r, hr⟩ := hz
    obtain ⟨s, hs⟩ := hw
    refine ⟨r + s, ?_⟩
    rw [smul_add]
    refine M.add_mem ?_ ?_
    · rw [pow_add, mul_comm, mul_smul]
      exact hpow s hr
    · rw [pow_add, mul_smul]
      exact hpow r hs
  | smul a z _ hz =>
    obtain ⟨r, hr⟩ := hz
    by_cases ha : a = 0
    · exact ⟨0, by simp [ha]⟩
    obtain ⟨t, w, hw⟩ := exists_eq_zpow_mul_unit hϖ ha
    refine ⟨(-t).toNat + r, ?_⟩
    have hint : ((ϖ : F) ^ ((-t).toNat)) * a ∈ 𝒪[F] := by
      rw [hw, ← mul_assoc, ← zpow_natCast, ← zpow_add₀ (coe_uniformizer_ne_zero hϖ)]
      have hnn : 0 ≤ ((-t).toNat : ℤ) + t := by omega
      lift ((-t).toNat : ℤ) + t to ℕ using hnn with k
      rw [zpow_natCast]
      exact mul_mem (pow_mem (ϖ.property) k) (w : 𝒪[F]).property
    have h1 : ((ϖ : F) ^ ((-t).toNat + r)) • (a • z) =
        ((ϖ : F) ^ ((-t).toNat) * a) • (((ϖ : F) ^ r) • z) := by
      rw [smul_smul, smul_smul]
      congr 1
      rw [pow_add]
      ring
    have h2 : ((ϖ : F) ^ ((-t).toNat) * a) • (((ϖ : F) ^ r) • z) =
        (⟨_, hint⟩ : 𝒪[F]) • (((ϖ : F) ^ r) • z) :=
      algebraMap_smul F (⟨_, hint⟩ : 𝒪[F]) _
    rw [h1, h2]
    exact M.smul_mem _ hr

theorem pow_smul_mem_endFiltration {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ) (r : ℕ) {k : ℤ} {y : A}
    (hy : y ∈ L.endFiltration k) : ((ϖ : F) ^ r) • y ∈ L.endFiltration (k + L.period * r) := by
  intro i v hv
  have hyv := hy i v hv
  change ((ϖ : F) ^ r) • (y v) ∈ L.lattice (i + (k + L.period * r))
  have h := (L.zpow_smul_mem_iff hϖ (r : ℤ) (j := i + (k + L.period * r)) (x := y v)).mpr
    (by rw [show i + (k + (L.period : ℤ) * r) - L.period * (r : ℤ) = i + k by ring]; exact hyv)
  simpa [zpow_natCast] using h

include hJ in
/-- For `r` large, conjugation by `ζ^r` carries `J ∩ U` into `U^m(𝓛')` for any lattice chain
`𝓛'` with `End^N(𝓛) ⊆ End^m(𝓛')`. -/
theorem pow_conj_mem_unitFiltration {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ) {e : A}
    (he : IsIdempotentElem e)
    (hoff : ∀ x ∈ L.order, e * x * (1 - e) ∈ L.endFiltration 1)
    (L' : LatticeChain 𝒪[F] F V) (m : ℕ) (N : ℤ) (hN : L.endFiltration N ≤ L'.endFiltration m)
    (r : ℕ) (hr : N ≤ L.period * r) {u : G} (hu : u ∈ Jg ⊓ upperGroup e) :
    contraction he (scalarUnit (ϖ : F) (coe_uniformizer_ne_zero hϖ))
        (scalarUnit_comm _ _) ^ r * u *
      (contraction he (scalarUnit (ϖ : F) (coe_uniformizer_ne_zero hϖ))
        (scalarUnit_comm _ _) ^ r)⁻¹ ∈ L'.unitFiltration m := by
  set ζ := contraction he (scalarUnit (V := V) (ϖ : F) (coe_uniformizer_ne_zero hϖ))
    (scalarUnit_comm _ _)
  obtain ⟨hmem, hval⟩ := pow_conj_upper he _ (scalarUnit_comm _ _) r hu.2
  have hu1 := mem_unitFiltration_one_of_mem_upperGroup L R Jg hJ he hoff hu.1 hu.2
  have hy : ((ϖ : F) ^ r) • ((u : A) - 1) ∈ L'.endFiltration m := by
    apply hN
    have := pow_smul_mem_endFiltration L hϖ r hu1.2.2
    exact L.endFiltration_antitone (by omega) this
  have hc : (((scalarUnit (V := V) (ϖ : F) (coe_uniformizer_ne_zero hϖ) : G) : A) ^ r) *
      ((u : A) - 1) = ((ϖ : F) ^ r) • ((u : A) - 1) := by
    rw [val_scalarUnit, ← map_pow, ← Algebra.smul_def]
  rw [hc] at hval
  have hy0 : ((ϖ : F) ^ r) • ((u : A) - 1) ∈ L'.order :=
    L'.endFiltration_antitone (show (0 : ℤ) ≤ m by omega) hy
  refine ⟨?_, ?_, ?_⟩
  · rw [hval]
    exact add_mem (one_mem _) hy0
  · rw [val_inv_of_mem_upperGroup hmem, hval, add_sub_cancel_left]
    exact sub_mem (one_mem _) hy0
  · rw [hval, add_sub_cancel_left]
    exact hy

end LatticeContraction

end Langlands.BushnellKutzko.BlockIdempotent
