import Langlands.GroupScheme.Quaternionic.RationalIsometry

/-!
# Eichler transformations, reflections and hyperbolic scalings

Let `q` be a `σ`-quadratic form on row vectors `D^n` with polar form `h`. This module
introduces three families of explicit matrices acting on row vectors by `v ↦ v M`:

* the **Eichler transformation** `E^e_{x,c}`, `v ↦ v + h(v,e) x - (h(v,x) + h(v,e) c) e`,
  for `q(e) = 0`, `h(x,e) = 0` and `[c] = q(x)`;
* the **reflection** `ρ_{y,c}`, `v ↦ v - h(v,y) c⁻¹ y`, for `c ≠ 0` and `[c] = q(y)`;
* the **hyperbolic scaling** `ℓ_{e,f}(a, b)`, `v ↦ v + h(v,f) (a - 1) e + h(v,e) (b - 1) f`,
  for a hyperbolic pair `(e, f)` and `a σ(b) = 1`; it sends `e ↦ a e`, `f ↦ b f` and fixes
  `{e, f}^⊥`.

All three are rational isometries of `q`; Eichler transformations with a fixed `e` compose
by `E^e_{x,c} E^e_{y,d} = E^e_{x+y, c+d+h(x,y)}`, and conjugating any of them by a rational
isometry `g` moves the defining vectors by `g`.
-/

noncomputable section

universe u v w

open Matrix

namespace Langlands.GroupScheme.Quaternionic

namespace FirstKindInvolution.Eichler

variable {K : Type u} {D : Type v} [Field K] [DivisionRing D] [Algebra K D]
  (σ : FirstKindInvolution K D) {n : Type w} [Fintype n] [DecidableEq n]
  (q : σ.QuadraticForms n)

/-! ### Rank-one matrices attached to the polar form -/

/-- The matrix of the row-vector map `v ↦ h(v, y) x`, where `h` is the polar form of `q`. -/
def formRankOne (y x : n → D) : Matrix n n D :=
  vecMulVec (σ.polar q *ᵥ (σ ∘ y)) x

@[simp] theorem vecMul_formRankOne (y x v : n → D) :
    v ᵥ* formRankOne σ q y x = σ.sesqForm (σ.polar q) v y • x := by
  rw [formRankOne, vecMul_vecMulVec, σ.sesqForm_eq_dotProduct]

/-- If `[c] = q(x)` then `h(x, x) = c + σ(c)`. -/
theorem sesqForm_polar_self_of_quadraticValue {x : n → D} {c : D}
    (hc : (Submodule.Quotient.mk c : D ⧸ σ.alternatingSubspace) = σ.quadraticValue x q) :
    σ.sesqForm (σ.polar q) x x = c + σ c := by
  obtain ⟨Q, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  rw [quadraticValue_mk, Submodule.Quotient.eq] at hc
  obtain ⟨a, ha⟩ := σ.mem_alternatingSubspace.1 hc
  rw [sesqForm_polar_mk]
  have : σ.sesqForm Q x x = c - (a - σ a) := by rw [ha]; abel
  rw [this]
  simp only [map_sub, apply_apply]
  abel

/-! ### Eichler transformations -/

/-- The matrix of the Eichler transformation
`E^e_{x,c} : v ↦ v + h(v,e) x - (h(v,x) + h(v,e) c) e`. -/
def eichlerMatrix (e x : n → D) (c : D) : Matrix n n D :=
  1 + formRankOne σ q e x - formRankOne σ q x e - formRankOne σ q e (c • e)

theorem vecMul_eichlerMatrix (e x : n → D) (c : D) (v : n → D) :
    v ᵥ* eichlerMatrix σ q e x c =
      v + σ.sesqForm (σ.polar q) v e • x -
        (σ.sesqForm (σ.polar q) v x + σ.sesqForm (σ.polar q) v e * c) • e := by
  simp only [eichlerMatrix, vecMul_add, vecMul_sub, vecMul_one, vecMul_formRankOne, smul_smul,
    add_smul]
  abel

theorem eichlerMatrix_zero (e : n → D) : eichlerMatrix σ q e 0 0 = 1 := by
  rw [ext_iff_vecMul]
  intro v
  simp [vecMul_eichlerMatrix]

/-- The Eichler transformation preserves the polar form. -/
theorem sesqForm_vecMul_eichlerMatrix {e x : n → D} {c : D}
    (he : σ.sesqForm (σ.polar q) e e = 0) (hxe : σ.sesqForm (σ.polar q) x e = 0)
    (hxx : σ.sesqForm (σ.polar q) x x = c + σ c) (v w : n → D) :
    σ.sesqForm (σ.polar q) (v ᵥ* eichlerMatrix σ q e x c) (w ᵥ* eichlerMatrix σ q e x c) =
      σ.sesqForm (σ.polar q) v w := by
  have hex : σ.sesqForm (σ.polar q) e x = 0 := by
    rw [← sesqForm_polar_swap, hxe, map_zero]
  have hxw : σ.sesqForm (σ.polar q) x w = σ (σ.sesqForm (σ.polar q) w x) :=
    (sesqForm_polar_swap σ q w x).symm
  have hew : σ.sesqForm (σ.polar q) e w = σ (σ.sesqForm (σ.polar q) w e) :=
    (sesqForm_polar_swap σ q w e).symm
  simp only [vecMul_eichlerMatrix, sesqForm_add_left, sesqForm_sub_left, sesqForm_add_right,
    sesqForm_sub_right, sesqForm_smul_left, sesqForm_smul_right, hex, hxw, hew, he, hxe, hxx,
    map_add, map_mul]
  noncomm_ring

/-- The Eichler transformation preserves the values of `q`. -/
theorem quadraticValue_vecMul_eichlerMatrix {e x : n → D} {c : D}
    (he : σ.quadraticValue e q = 0) (hxe : σ.sesqForm (σ.polar q) x e = 0)
    (hc : (Submodule.Quotient.mk c : D ⧸ σ.alternatingSubspace) = σ.quadraticValue x q)
    (v : n → D) :
    σ.quadraticValue (v ᵥ* eichlerMatrix σ q e x c) q = σ.quadraticValue v q := by
  rw [vecMul_eichlerMatrix, sub_eq_add_neg, ← neg_smul, quadraticValue_add, quadraticValue_add,
    quadraticValue_smul, quadraticValue_smul, he, LinearMap.map_zero, ← hc, valueSandwich_mk,
    sesqForm_add_left, sesqForm_smul_right, sesqForm_smul_left, sesqForm_smul_right,
    sesqForm_smul_right, hxe, add_zero, add_assoc, add_assoc, ← Submodule.Quotient.mk_add,
    ← Submodule.Quotient.mk_add, add_eq_left, Submodule.Quotient.mk_eq_zero]
  set α := σ.sesqForm (σ.polar q) v e
  set β := σ.sesqForm (σ.polar q) v x
  refine σ.mem_alternatingSubspace.2 ⟨α * c * σ α + β * σ α, ?_⟩
  simp only [map_add, map_mul, apply_apply, map_neg]
  noncomm_ring

/-- Composition of Eichler transformations along a common singular vector. -/
theorem eichlerMatrix_mul {e x y : n → D} (c d : D) (he : σ.sesqForm (σ.polar q) e e = 0)
    (hxe : σ.sesqForm (σ.polar q) x e = 0) (hye : σ.sesqForm (σ.polar q) y e = 0) :
    eichlerMatrix σ q e x c * eichlerMatrix σ q e y d =
      eichlerMatrix σ q e (x + y) (c + d + σ.sesqForm (σ.polar q) x y) := by
  have hey : σ.sesqForm (σ.polar q) e y = 0 := by
    rw [← sesqForm_polar_swap, hye, map_zero]
  rw [ext_iff_vecMul]
  intro v
  rw [← vecMul_vecMul]
  simp only [vecMul_eichlerMatrix, sesqForm_add_left, sesqForm_sub_left, sesqForm_add_right,
    sesqForm_smul_left, he, hxe, hey, mul_zero, add_zero, sub_zero]
  ext i
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  noncomm_ring

/-- The Eichler transformation `E^e_{x,c}` is invertible with inverse `E^e_{-x,σ(c)}`. -/
theorem eichlerMatrix_mul_eichlerMatrix_neg {e x : n → D} {c : D}
    (he : σ.sesqForm (σ.polar q) e e = 0) (hxe : σ.sesqForm (σ.polar q) x e = 0)
    (hxx : σ.sesqForm (σ.polar q) x x = c + σ c) :
    eichlerMatrix σ q e x c * eichlerMatrix σ q e (-x) (σ c) = 1 := by
  have hnxe : σ.sesqForm (σ.polar q) (-x) e = 0 := by rw [sesqForm_neg_left, hxe, neg_zero]
  rw [eichlerMatrix_mul σ q c (σ c) he hxe hnxe, add_neg_cancel, sesqForm_neg_right, hxx]
  rw [show c + σ c + -(c + σ c) = 0 by abel, eichlerMatrix_zero]

theorem eichlerMatrix_neg_mul_eichlerMatrix {e x : n → D} {c : D}
    (he : σ.sesqForm (σ.polar q) e e = 0) (hxe : σ.sesqForm (σ.polar q) x e = 0)
    (hxx : σ.sesqForm (σ.polar q) x x = c + σ c) :
    eichlerMatrix σ q e (-x) (σ c) * eichlerMatrix σ q e x c = 1 := by
  have hnxe : σ.sesqForm (σ.polar q) (-x) e = 0 := by rw [sesqForm_neg_left, hxe, neg_zero]
  rw [eichlerMatrix_mul σ q (σ c) c he hnxe hxe, neg_add_cancel, sesqForm_neg_left, hxx]
  rw [show σ c + c + -(c + σ c) = 0 by abel, eichlerMatrix_zero]

/-- The Eichler transformations along `e`: the units `E^e_{x,c}` with `h(x,e) = 0` and
`[c] = q(x)`. -/
def eichlerSet (e : n → D) : Set (Matrix n n D)ˣ :=
  {u | ∃ x c, σ.sesqForm (σ.polar q) x e = 0 ∧
    (Submodule.Quotient.mk c : D ⧸ σ.alternatingSubspace) = σ.quadraticValue x q ∧
    (u : Matrix n n D) = eichlerMatrix σ q e x c}

/-- Every admissible Eichler matrix along a singular vector is a unit in `eichlerSet`. -/
theorem exists_mem_eichlerSet {e x : n → D} {c : D} (he : σ.quadraticValue e q = 0)
    (hxe : σ.sesqForm (σ.polar q) x e = 0)
    (hc : (Submodule.Quotient.mk c : D ⧸ σ.alternatingSubspace) = σ.quadraticValue x q) :
    ∃ u ∈ eichlerSet σ q e, (u : Matrix n n D) = eichlerMatrix σ q e x c := by
  have he' := sesqForm_polar_self_eq_zero σ q e he
  have hxx := sesqForm_polar_self_of_quadraticValue σ q hc
  exact ⟨⟨_, _, eichlerMatrix_mul_eichlerMatrix_neg σ q he' hxe hxx,
    eichlerMatrix_neg_mul_eichlerMatrix σ q he' hxe hxx⟩, ⟨x, c, hxe, hc, rfl⟩, rfl⟩

/-- Eichler transformations along a singular vector are rational isometries. -/
theorem eichlerSet_subset [LinearOrder n] {e : n → D} (he : σ.quadraticValue e q = 0) :
    eichlerSet σ q e ⊆ rationalIsometryGroup σ q := by
  rintro u ⟨x, c, hxe, hc, hu⟩
  have he' := sesqForm_polar_self_eq_zero σ q e he
  have hxx := sesqForm_polar_self_of_quadraticValue σ q hc
  rw [SetLike.mem_coe, mem_rationalIsometryGroup_iff_forall, hu]
  exact ⟨sesqForm_vecMul_eichlerMatrix σ q he' hxe hxx,
    quadraticValue_vecMul_eichlerMatrix σ q he hxe hc⟩

/-- The inverse of an Eichler transformation is an Eichler transformation. -/
theorem inv_mem_eichlerSet {e : n → D} (he : σ.quadraticValue e q = 0) {u : (Matrix n n D)ˣ}
    (hu : u ∈ eichlerSet σ q e) : u⁻¹ ∈ eichlerSet σ q e := by
  obtain ⟨x, c, hxe, hc, hu⟩ := hu
  have he' := sesqForm_polar_self_eq_zero σ q e he
  have hxx := sesqForm_polar_self_of_quadraticValue σ q hc
  refine ⟨-x, σ c, by rw [sesqForm_neg_left, hxe, neg_zero], ?_, ?_⟩
  · rw [quotient_mk_map, ← neg_one_smul D x, quadraticValue_smul, ← hc, valueSandwich_mk]
    simp
  · refine Units.inv_eq_of_mul_eq_one_right ?_
    rw [hu]
    exact eichlerMatrix_mul_eichlerMatrix_neg σ q he' hxe hxx

/-! ### Reflections -/

/-- An involution of the first kind commutes with inversion. -/
theorem map_inv_eq (a : D) : σ a⁻¹ = (σ a)⁻¹ := by
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  · exact eq_inv_of_mul_eq_one_left (by rw [← map_mul, mul_inv_cancel₀ ha, map_one])

theorem map_ne_zero_of_ne_zero {a : D} (ha : a ≠ 0) : σ a ≠ 0 := fun h =>
  ha (σ.injective (h.trans (map_zero σ).symm))

/-- The matrix of the reflection `ρ_{y,c} : v ↦ v - h(v,y) c⁻¹ y`. -/
def reflectionMatrix (y : n → D) (c : D) : Matrix n n D :=
  1 - formRankOne σ q y (c⁻¹ • y)

theorem vecMul_reflectionMatrix (y : n → D) (c : D) (v : n → D) :
    v ᵥ* reflectionMatrix σ q y c = v - (σ.sesqForm (σ.polar q) v y * c⁻¹) • y := by
  simp only [reflectionMatrix, vecMul_sub, vecMul_one, vecMul_formRankOne, smul_smul]

/-- The reflection preserves the polar form. -/
theorem sesqForm_vecMul_reflectionMatrix {y : n → D} {c : D} (hc0 : c ≠ 0)
    (hyy : σ.sesqForm (σ.polar q) y y = c + σ c) (v w : n → D) :
    σ.sesqForm (σ.polar q) (v ᵥ* reflectionMatrix σ q y c)
        (w ᵥ* reflectionMatrix σ q y c) =
      σ.sesqForm (σ.polar q) v w := by
  have hσc0 := map_ne_zero_of_ne_zero σ hc0
  have hyw : σ.sesqForm (σ.polar q) y w = σ (σ.sesqForm (σ.polar q) w y) :=
    (sesqForm_polar_swap σ q w y).symm
  simp only [vecMul_reflectionMatrix, sesqForm_sub_left, sesqForm_sub_right,
    sesqForm_smul_left, sesqForm_smul_right, hyw, hyy, map_mul, map_inv_eq, mul_add, add_mul,
    sub_mul, mul_assoc, inv_mul_cancel_left₀ hc0, mul_inv_cancel_left₀ hσc0]
  abel

/-- The reflection preserves the values of `q`. -/
theorem quadraticValue_vecMul_reflectionMatrix {y : n → D} {c : D} (hc0 : c ≠ 0)
    (hc : (Submodule.Quotient.mk c : D ⧸ σ.alternatingSubspace) = σ.quadraticValue y q)
    (v : n → D) :
    σ.quadraticValue (v ᵥ* reflectionMatrix σ q y c) q = σ.quadraticValue v q := by
  rw [vecMul_reflectionMatrix, sub_eq_add_neg, ← neg_smul, quadraticValue_add,
    quadraticValue_smul, ← hc, valueSandwich_mk, sesqForm_smul_right, add_assoc,
    ← Submodule.Quotient.mk_add, add_eq_left, Submodule.Quotient.mk_eq_zero]
  convert Submodule.zero_mem σ.alternatingSubspace using 1
  simp only [map_neg, map_mul, map_inv_eq, neg_mul, mul_neg, neg_neg, mul_assoc,
    inv_mul_cancel_left₀ hc0]
  abel

/-- `ρ_{y,σ(c)}` inverts `ρ_{y,c}`. -/
theorem reflectionMatrix_mul_reflectionMatrix_map {y : n → D} {c : D} (hc0 : c ≠ 0)
    (hyy : σ.sesqForm (σ.polar q) y y = c + σ c) :
    reflectionMatrix σ q y c * reflectionMatrix σ q y (σ c) = 1 := by
  have hσc0 := map_ne_zero_of_ne_zero σ hc0
  rw [ext_iff_vecMul]
  intro v
  rw [← vecMul_vecMul, vecMul_one, vecMul_reflectionMatrix, vecMul_reflectionMatrix,
    sesqForm_sub_left, sesqForm_smul_left, hyy]
  have key : (σ.sesqForm (σ.polar q) v y - σ.sesqForm (σ.polar q) v y * c⁻¹ * (c + σ c)) *
      (σ c)⁻¹ = -(σ.sesqForm (σ.polar q) v y * c⁻¹) := by
    simp only [mul_add, sub_mul, add_mul, mul_assoc, inv_mul_cancel_left₀ hc0,
      mul_inv_cancel₀ hσc0, mul_one]
    abel
  rw [key, neg_smul, sub_neg_eq_add, sub_add_cancel]

/-- The reflections `ρ_{y,c}` with `c ≠ 0` and `[c] = q(y)`. -/
def reflectionSet : Set (Matrix n n D)ˣ :=
  {u | ∃ y c, c ≠ 0 ∧
    (Submodule.Quotient.mk c : D ⧸ σ.alternatingSubspace) = σ.quadraticValue y q ∧
    (u : Matrix n n D) = reflectionMatrix σ q y c}

/-- Reflections are rational isometries. -/
theorem reflectionSet_subset [LinearOrder n] :
    reflectionSet σ q ⊆ rationalIsometryGroup σ q := by
  rintro u ⟨y, c, hc0, hc, hu⟩
  have hyy := sesqForm_polar_self_of_quadraticValue σ q hc
  rw [SetLike.mem_coe, mem_rationalIsometryGroup_iff_forall, hu]
  exact ⟨sesqForm_vecMul_reflectionMatrix σ q hc0 hyy,
    quadraticValue_vecMul_reflectionMatrix σ q hc0 hc⟩

/-- Every admissible reflection matrix is a unit in `reflectionSet`. -/
theorem exists_mem_reflectionSet {y : n → D} {c : D} (hc0 : c ≠ 0)
    (hc : (Submodule.Quotient.mk c : D ⧸ σ.alternatingSubspace) = σ.quadraticValue y q) :
    ∃ u ∈ reflectionSet σ q, (u : Matrix n n D) = reflectionMatrix σ q y c := by
  have hyy := sesqForm_polar_self_of_quadraticValue σ q hc
  have hyy' : σ.sesqForm (σ.polar q) y y = σ c + σ (σ c) := by rw [hyy, apply_apply, add_comm]
  have h2 := reflectionMatrix_mul_reflectionMatrix_map σ q (map_ne_zero_of_ne_zero σ hc0) hyy'
  rw [apply_apply] at h2
  exact ⟨⟨_, _, reflectionMatrix_mul_reflectionMatrix_map σ q hc0 hyy, h2⟩,
    ⟨y, c, hc0, hc, rfl⟩, rfl⟩

/-- The inverse of a reflection is a reflection. -/
theorem inv_mem_reflectionSet {u : (Matrix n n D)ˣ} (hu : u ∈ reflectionSet σ q) :
    u⁻¹ ∈ reflectionSet σ q := by
  obtain ⟨y, c, hc0, hc, hu⟩ := hu
  have hyy := sesqForm_polar_self_of_quadraticValue σ q hc
  refine ⟨y, σ c, map_ne_zero_of_ne_zero σ hc0, by rw [quotient_mk_map, hc], ?_⟩
  refine Units.inv_eq_of_mul_eq_one_right ?_
  rw [hu]
  exact reflectionMatrix_mul_reflectionMatrix_map σ q hc0 hyy

/-! ### Hyperbolic scalings -/

/-- The matrix of the hyperbolic scaling `v ↦ v + h(v,f) (a - 1) e + h(v,e) (b - 1) f`; for a
hyperbolic pair `(e, f)` it sends `e ↦ a e`, `f ↦ b f` and fixes `{e, f}^⊥`. -/
def scalingMatrix (e f : n → D) (a b : D) : Matrix n n D :=
  1 + formRankOne σ q f ((a - 1) • e) + formRankOne σ q e ((b - 1) • f)

theorem vecMul_scalingMatrix (e f : n → D) (a b : D) (v : n → D) :
    v ᵥ* scalingMatrix σ q e f a b =
      v + (σ.sesqForm (σ.polar q) v f * (a - 1)) • e +
        (σ.sesqForm (σ.polar q) v e * (b - 1)) • f := by
  simp only [scalingMatrix, vecMul_add, vecMul_one, vecMul_formRankOne, smul_smul]

theorem scalingMatrix_one_one (e f : n → D) : scalingMatrix σ q e f 1 1 = 1 := by
  rw [ext_iff_vecMul]
  intro v
  simp [vecMul_scalingMatrix]

/-- Hyperbolic scalings multiply coordinatewise. -/
theorem scalingMatrix_mul {e f : n → D} (hee : σ.sesqForm (σ.polar q) e e = 0)
    (hff : σ.sesqForm (σ.polar q) f f = 0) (hef : σ.sesqForm (σ.polar q) e f = 1)
    (a b a' b' : D) :
    scalingMatrix σ q e f a b * scalingMatrix σ q e f a' b' =
      scalingMatrix σ q e f (a * a') (b * b') := by
  have hfe : σ.sesqForm (σ.polar q) f e = 1 := by
    rw [← sesqForm_polar_swap, hef, map_one]
  rw [ext_iff_vecMul]
  intro v
  rw [← vecMul_vecMul]
  simp only [vecMul_scalingMatrix, sesqForm_add_left, sesqForm_smul_left, hee, hff, hef, hfe,
    mul_zero, mul_one, add_zero]
  ext i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  noncomm_ring

/-- A hyperbolic scaling with `a σ(b) = 1` preserves the polar form. -/
theorem sesqForm_vecMul_scalingMatrix {e f : n → D} (hee : σ.sesqForm (σ.polar q) e e = 0)
    (hff : σ.sesqForm (σ.polar q) f f = 0) (hef : σ.sesqForm (σ.polar q) e f = 1) {a b : D}
    (hab : a * σ b = 1) (v w : n → D) :
    σ.sesqForm (σ.polar q) (v ᵥ* scalingMatrix σ q e f a b)
        (w ᵥ* scalingMatrix σ q e f a b) =
      σ.sesqForm (σ.polar q) v w := by
  have hfe : σ.sesqForm (σ.polar q) f e = 1 := by
    rw [← sesqForm_polar_swap, hef, map_one]
  have hba : b * σ a = 1 := by
    have := congrArg σ hab
    simpa only [map_mul, apply_apply, map_one] using this
  have hab' : ∀ z, a * (σ b * z) = z := fun z => by rw [← mul_assoc, hab, one_mul]
  have hba' : ∀ z, b * (σ a * z) = z := fun z => by rw [← mul_assoc, hba, one_mul]
  have hew : σ.sesqForm (σ.polar q) e w = σ (σ.sesqForm (σ.polar q) w e) :=
    (sesqForm_polar_swap σ q w e).symm
  have hfw : σ.sesqForm (σ.polar q) f w = σ (σ.sesqForm (σ.polar q) w f) :=
    (sesqForm_polar_swap σ q w f).symm
  simp only [vecMul_scalingMatrix, sesqForm_add_left, sesqForm_add_right, sesqForm_smul_left,
    sesqForm_smul_right, hee, hff, hef, hfe, hew, hfw, map_mul, map_sub, add_mul, mul_sub,
    sub_mul, mul_assoc, mul_zero, zero_mul, mul_one, hab', hba']
  noncomm_ring

/-- A hyperbolic scaling with `a σ(b) = 1` preserves the values of `q`. -/
theorem quadraticValue_vecMul_scalingMatrix {e f : n → D} (he : σ.quadraticValue e q = 0)
    (hf : σ.quadraticValue f q = 0) (hef : σ.sesqForm (σ.polar q) e f = 1) {a b : D}
    (hab : a * σ b = 1) (v : n → D) :
    σ.quadraticValue (v ᵥ* scalingMatrix σ q e f a b) q = σ.quadraticValue v q := by
  have hab' : ∀ z, a * (σ b * z) = z := fun z => by rw [← mul_assoc, hab, one_mul]
  rw [vecMul_scalingMatrix, quadraticValue_add, quadraticValue_add, quadraticValue_smul,
    quadraticValue_smul, he, hf, LinearMap.map_zero, LinearMap.map_zero, add_zero, add_zero,
    sesqForm_add_left, sesqForm_smul_right, sesqForm_smul_right, sesqForm_smul_left,
    sesqForm_smul_right, hef, add_assoc, ← Submodule.Quotient.mk_add, add_eq_left,
    Submodule.Quotient.mk_eq_zero]
  set α := σ.sesqForm (σ.polar q) v f
  set β := σ.sesqForm (σ.polar q) v e
  refine σ.mem_alternatingSubspace.2 ⟨β * (σ a - 1) * σ α, ?_⟩
  simp only [map_mul, map_sub, apply_apply, mul_sub, sub_mul, mul_assoc, one_mul, mul_one,
    hab']
  noncomm_ring

/-! ### Conjugation by isometries -/

/-- Conjugating the rank-one matrix of `v ↦ h(v,y) x` by an isometry `g` of the polar form
moves `x` and `y` by `g`. -/
theorem conj_formRankOne (g : (Matrix n n D)ˣ)
    (hg : ∀ v w, σ.sesqForm (σ.polar q) (v ᵥ* (g : Matrix n n D)) (w ᵥ* (g : Matrix n n D)) =
      σ.sesqForm (σ.polar q) v w) (y x : n → D) :
    ((g⁻¹ : (Matrix n n D)ˣ) : Matrix n n D) * formRankOne σ q y x * g =
      formRankOne σ q (y ᵥ* (g : Matrix n n D)) (x ᵥ* (g : Matrix n n D)) := by
  rw [ext_iff_vecMul]
  intro v
  rw [← vecMul_vecMul, ← vecMul_vecMul, vecMul_formRankOne, vecMul_formRankOne, smul_vecMul,
    ← hg, vecMul_vecMul, Units.inv_mul, vecMul_one]

/-- Conjugating an Eichler transformation by an isometry `g` of the polar form moves its
defining vectors by `g`. -/
theorem conj_eichlerMatrix (g : (Matrix n n D)ˣ)
    (hg : ∀ v w, σ.sesqForm (σ.polar q) (v ᵥ* (g : Matrix n n D)) (w ᵥ* (g : Matrix n n D)) =
      σ.sesqForm (σ.polar q) v w) (e x : n → D) (c : D) :
    ((g⁻¹ : (Matrix n n D)ˣ) : Matrix n n D) * eichlerMatrix σ q e x c * g =
      eichlerMatrix σ q (e ᵥ* (g : Matrix n n D)) (x ᵥ* (g : Matrix n n D)) c := by
  simp only [eichlerMatrix, Matrix.mul_add, Matrix.mul_sub, Matrix.add_mul, Matrix.sub_mul,
    Matrix.mul_one, Units.inv_mul, conj_formRankOne σ q g hg, smul_vecMul]

/-- Conjugating a reflection by an isometry `g` of the polar form moves its vector by `g`. -/
theorem conj_reflectionMatrix (g : (Matrix n n D)ˣ)
    (hg : ∀ v w, σ.sesqForm (σ.polar q) (v ᵥ* (g : Matrix n n D)) (w ᵥ* (g : Matrix n n D)) =
      σ.sesqForm (σ.polar q) v w) (y : n → D) (c : D) :
    ((g⁻¹ : (Matrix n n D)ˣ) : Matrix n n D) * reflectionMatrix σ q y c * g =
      reflectionMatrix σ q (y ᵥ* (g : Matrix n n D)) c := by
  simp only [reflectionMatrix, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Units.inv_mul,
    conj_formRankOne σ q g hg, smul_vecMul]

/-- Conjugating a hyperbolic scaling by an isometry `g` of the polar form moves the pair by
`g`. -/
theorem conj_scalingMatrix (g : (Matrix n n D)ˣ)
    (hg : ∀ v w, σ.sesqForm (σ.polar q) (v ᵥ* (g : Matrix n n D)) (w ᵥ* (g : Matrix n n D)) =
      σ.sesqForm (σ.polar q) v w) (e f : n → D) (a b : D) :
    ((g⁻¹ : (Matrix n n D)ˣ) : Matrix n n D) * scalingMatrix σ q e f a b * g =
      scalingMatrix σ q (e ᵥ* (g : Matrix n n D)) (f ᵥ* (g : Matrix n n D)) a b := by
  simp only [scalingMatrix, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Units.inv_mul,
    conj_formRankOne σ q g hg, smul_vecMul]

/-- Rescaling the singular vector of an Eichler transformation. -/
theorem eichlerMatrix_smul (e x : n → D) (c d : D) :
    eichlerMatrix σ q (d • e) x c = eichlerMatrix σ q e (σ d • x) (σ d * c * d) := by
  rw [ext_iff_vecMul]
  intro v
  simp only [vecMul_eichlerMatrix, sesqForm_smul_right, apply_apply, smul_smul, add_mul,
    mul_assoc]

end FirstKindInvolution.Eichler

end Langlands.GroupScheme.Quaternionic
