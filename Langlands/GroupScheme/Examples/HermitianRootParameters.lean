import Langlands.GroupScheme.Examples.SU3RootParameters

/-! # Root parameters for a finite diagonal Hermitian middle form -/

namespace Langlands.GroupScheme.HermitianRoot

open SU3Root

universe u v w t

/-- The diagonal coefficients of a Hermitian form, fixed by the given involution. -/
structure DiagonalForm {A : Type u} [CommRing A] (c : RingInvolution A) (ι : Type v) where
  weight : ι → A
  bar_weight : ∀ i, c.bar (weight i) = weight i

variable {A : Type u} {B : Type w} {C : Type t} {ι : Type v}
  [CommRing A] [CommRing B] [CommRing C] [Fintype ι]
  {c : RingInvolution A} {d : RingInvolution B} {e : RingInvolution C}

namespace DiagonalForm

/-- The diagonal pairing, linear in the first variable and conjugate linear in the second. -/
def pairing (H : DiagonalForm c ι) (x y : ι → A) : A :=
  ∑ i, H.weight i * x i * c.bar (y i)

@[simp] theorem pairing_zero_left (H : DiagonalForm c ι) (y : ι → A) :
    H.pairing 0 y = 0 := by simp [pairing]

@[simp] theorem pairing_zero_right (H : DiagonalForm c ι) (x : ι → A) :
    H.pairing x 0 = 0 := by simp [pairing]

theorem pairing_add_left (H : DiagonalForm c ι) (x y z : ι → A) :
    H.pairing (x + y) z = H.pairing x z + H.pairing y z := by
  simp [pairing, mul_add, add_mul, Finset.sum_add_distrib]

theorem pairing_add_right (H : DiagonalForm c ι) (x y z : ι → A) :
    H.pairing x (y + z) = H.pairing x y + H.pairing x z := by
  simp [pairing, mul_add, Finset.sum_add_distrib]

@[simp] theorem pairing_neg_left (H : DiagonalForm c ι) (x y : ι → A) :
    H.pairing (-x) y = -H.pairing x y := by simp [pairing]

@[simp] theorem pairing_neg_right (H : DiagonalForm c ι) (x y : ι → A) :
    H.pairing x (-y) = -H.pairing x y := by simp [pairing]

theorem bar_pairing (H : DiagonalForm c ι) (x y : ι → A) :
    c.bar (H.pairing x y) = H.pairing y x := by
  simp only [pairing, map_sum, map_mul, H.bar_weight, RingInvolution.bar_bar]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem pairing_scale (H : DiagonalForm c ι) (r s : A) (x y : ι → A) :
    H.pairing (fun i => r * x i) (fun i => s * y i) =
      (r * c.bar s) * H.pairing x y := by
  simp only [pairing, map_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

end DiagonalForm

/-- Vector and scalar coordinates with their trace-pairing equation. -/
def Parameters (H : DiagonalForm c ι) :=
  {p : (ι → A) × A // p.2 + c.bar p.2 = H.pairing p.1 p.1}

namespace Parameters

variable {H : DiagonalForm c ι} {K : DiagonalForm d ι} {J : DiagonalForm e ι}

/-- The middle vector coordinate. -/
def vector (x : Parameters H) : ι → A := x.val.1

/-- The upper-right scalar coordinate. -/
def scalar (x : Parameters H) : A := x.val.2

@[simp] theorem equation (x : Parameters H) :
    x.scalar + c.bar x.scalar = H.pairing x.vector x.vector := x.property

@[ext] theorem ext {x y : Parameters H} (hv : x.vector = y.vector)
    (hs : x.scalar = y.scalar) : x = y := Subtype.ext (Prod.ext hv hs)

instance : One (Parameters H) := ⟨⟨(0, 0), by simp⟩⟩

instance : Mul (Parameters H) := ⟨fun x y =>
  ⟨(x.vector + y.vector, x.scalar + y.scalar + H.pairing x.vector y.vector), by
    change x.scalar + y.scalar + H.pairing x.vector y.vector +
        c.bar (x.scalar + y.scalar + H.pairing x.vector y.vector) =
      H.pairing (x.vector + y.vector) (x.vector + y.vector)
    rw [map_add, map_add, DiagonalForm.bar_pairing,
      DiagonalForm.pairing_add_left, DiagonalForm.pairing_add_right,
      DiagonalForm.pairing_add_right]
    linear_combination x.equation + y.equation⟩⟩

instance : Inv (Parameters H) := ⟨fun x =>
  ⟨(-x.vector, c.bar x.scalar), by
    simp only [RingInvolution.bar_bar, DiagonalForm.pairing_neg_left,
      DiagonalForm.pairing_neg_right, neg_neg]
    rw [add_comm, equation]⟩⟩

@[simp] theorem vector_one : (1 : Parameters H).vector = 0 := rfl
@[simp] theorem scalar_one : (1 : Parameters H).scalar = 0 := rfl
@[simp] theorem vector_mul (x y : Parameters H) : (x * y).vector = x.vector + y.vector := rfl
@[simp] theorem scalar_mul (x y : Parameters H) :
    (x * y).scalar = x.scalar + y.scalar + H.pairing x.vector y.vector := rfl
@[simp] theorem vector_inv (x : Parameters H) : x⁻¹.vector = -x.vector := rfl
@[simp] theorem scalar_inv (x : Parameters H) : x⁻¹.scalar = c.bar x.scalar := rfl

instance : Group (Parameters H) where
  mul_assoc x y z := by
    apply ext
    · simp [add_assoc]
    · simp only [scalar_mul, vector_mul, DiagonalForm.pairing_add_left,
        DiagonalForm.pairing_add_right]
      ring
  one_mul x := by ext <;> simp
  mul_one x := by ext <;> simp
  inv_mul_cancel x := by
    apply ext
    · simp
    · simp only [scalar_mul, scalar_inv, vector_inv, scalar_one,
        DiagonalForm.pairing_neg_left]
      linear_combination x.equation

/-- Coefficient change for compatible involutions and diagonal coefficients. -/
def map (f : A →+* B) (hf : ∀ a, f (c.bar a) = d.bar (f a))
    (hH : ∀ i, f (H.weight i) = K.weight i) : Parameters H →* Parameters K where
  toFun x := ⟨(fun i => f (x.vector i), f x.scalar), by
    change f x.scalar + d.bar (f x.scalar) =
      K.pairing (fun i => f (x.vector i)) (fun i => f (x.vector i))
    simpa only [map_add, DiagonalForm.pairing, map_sum, map_mul, hf, hH]
      using congrArg f x.equation⟩
  map_one' := by
    apply ext
    · funext i; exact map_zero f
    · exact map_zero f
  map_mul' x y := by
    apply ext
    · funext i; exact map_add f _ _
    · change f (x.scalar + y.scalar + H.pairing x.vector y.vector) =
        f x.scalar + f y.scalar +
          K.pairing (fun i => f (x.vector i)) (fun i => f (y.vector i))
      simp only [map_add, DiagonalForm.pairing, map_sum, map_mul, hf, hH]

@[simp] theorem vector_map (f : A →+* B) (hf : ∀ a, f (c.bar a) = d.bar (f a))
    (hH : ∀ i, f (H.weight i) = K.weight i) (x : Parameters H) :
    (map f hf hH x).vector = fun i => f (x.vector i) := rfl

@[simp] theorem scalar_map (f : A →+* B) (hf : ∀ a, f (c.bar a) = d.bar (f a))
    (hH : ∀ i, f (H.weight i) = K.weight i) (x : Parameters H) :
    (map f hf hH x).scalar = f x.scalar := rfl

@[simp] theorem map_id :
    map (H := H) (K := H) (RingHom.id A) (fun _ => rfl) (fun _ => rfl) =
      MonoidHom.id (Parameters H) := by ext x <;> rfl

theorem map_comp (f : A →+* B) (hf : ∀ a, f (c.bar a) = d.bar (f a))
    (hH : ∀ i, f (H.weight i) = K.weight i)
    (g : B →+* C) (hg : ∀ b, g (d.bar b) = e.bar (g b))
    (hK : ∀ i, g (K.weight i) = J.weight i) :
    map (g.comp f) (fun a => by simp only [RingHom.comp_apply, hf, hg])
        (fun i => by simp only [RingHom.comp_apply, hH, hK]) =
      (map g hg hK).comp (map f hf hH) := by ext x <;> rfl

/-- Scaling by a fixed scalar contracts the vector with weight one and the scalar
with weight two. -/
def scale (r : A) (hr : c.bar r = r) : Parameters H →* Parameters H where
  toFun x := ⟨(fun i => r * x.vector i, r ^ 2 * x.scalar), by
    change r ^ 2 * x.scalar + c.bar (r ^ 2 * x.scalar) =
      H.pairing (fun i => r * x.vector i) (fun i => r * x.vector i)
    rw [map_mul, map_pow, hr, DiagonalForm.pairing_scale, hr]
    linear_combination r ^ 2 * x.equation⟩
  map_one' := by
    apply ext
    · change (fun _ : ι => r * 0) = 0
      funext i
      exact mul_zero r
    · change r ^ 2 * 0 = 0
      exact mul_zero _
  map_mul' x y := by
    apply ext
    · funext i; exact mul_add r _ _
    · change r ^ 2 * (x.scalar + y.scalar + H.pairing x.vector y.vector) =
        r ^ 2 * x.scalar + r ^ 2 * y.scalar +
          H.pairing (fun i => r * x.vector i) (fun i => r * y.vector i)
      rw [DiagonalForm.pairing_scale, hr]
      ring

@[simp] theorem vector_scale (r : A) (hr : c.bar r = r) (x : Parameters H) :
    (scale r hr x).vector = fun i => r * x.vector i := rfl

@[simp] theorem scalar_scale (r : A) (hr : c.bar r = r) (x : Parameters H) :
    (scale r hr x).scalar = r ^ 2 * x.scalar := rfl

@[simp] theorem scale_zero (x : Parameters H) : scale 0 (map_zero c.bar) x = 1 := by
  apply ext
  · funext i
    simp
  · simp

@[simp] theorem scale_one : scale (H := H) 1 (map_one c.bar) =
    MonoidHom.id (Parameters H) := by ext x <;> simp

theorem scale_mul (r s : A) (hr : c.bar r = r) (hs : c.bar s = s) :
    scale (H := H) (r * s) (by rw [map_mul, hr, hs]) =
      (scale r hr).comp (scale s hs) := by
  apply MonoidHom.ext
  intro x
  apply ext
  · funext i
    simp only [vector_scale, MonoidHom.comp_apply]
    ring
  · simp only [scalar_scale, MonoidHom.comp_apply]
    ring

/-- The vector coordinate is a homomorphism to the additive vector group. -/
def vectorHom (H : DiagonalForm c ι) : Parameters H →* Multiplicative (ι → A) where
  toFun x := Multiplicative.ofAdd x.vector
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The subgroup of parameters with zero vector coordinate. -/
def central (H : DiagonalForm c ι) : Subgroup (Parameters H) := (vectorHom H).ker

@[simp] theorem mem_central (x : Parameters H) :
    x ∈ central H ↔ x.vector = 0 := Iff.rfl

theorem central_le_center : central H ≤ Subgroup.center (Parameters H) := by
  intro z hz
  rw [Subgroup.mem_center_iff]
  intro x
  have hz' : z.vector = 0 := hz
  apply ext <;> simp [hz', add_comm]

/-- The commutator has zero vector coordinate and the alternating pairing as scalar. -/
theorem commutator_coordinates (x y : Parameters H) :
    let z := x * y * x⁻¹ * y⁻¹
    z.vector = 0 ∧ z.scalar = H.pairing x.vector y.vector - H.pairing y.vector x.vector := by
  constructor
  · simp
  · simp only [scalar_mul, vector_mul, vector_inv, scalar_inv,
      DiagonalForm.pairing_add_left, DiagonalForm.pairing_neg_left,
      DiagonalForm.pairing_neg_right]
    linear_combination x.equation + y.equation

end Parameters
end Langlands.GroupScheme.HermitianRoot
