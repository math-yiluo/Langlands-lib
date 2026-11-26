import Langlands.BaseChange.RegularCyclicBasis

/-! # Lifting twisted intertwiners using a cyclic basis -/

noncomputable section

open Function Matrix

namespace Langlands.BaseChange

section MatrixLift

variable {S T : Type*} [CommRing S] [CommRing T] {n : ℕ}

private theorem mul_cyclicBasisMatrix_of_intertwiner {A B X : Matrix (Fin n) (Fin n) T}
    (hX : A * X = X * B) (v : Fin n → T) :
    cyclicBasisMatrix A (X *ᵥ v) = X * cyclicBasisMatrix B v := by
  have hp (k : ℕ) : A ^ k * X = X * B ^ k := by
    induction k with
    | zero => simp
    | succ k hk => rw [pow_succ', pow_succ', mul_assoc, hk, ← mul_assoc, hX, mul_assoc]
  ext i j
  change ((cyclicBasisMatrix A (X *ᵥ v)).col j) i = ((X * cyclicBasisMatrix B v).col j) i
  rw [col_mul_eq_mulVec_col, cyclicBasisMatrix_col, cyclicBasisMatrix_col,
    mulVec_mulVec, mulVec_mulVec, hp]

private theorem exists_lift_of_norm_intertwiner (f : S →+* T) (hf : Surjective f)
    {A B : Matrix (Fin n) (Fin n) S} (hp : A.charpoly = B.charpoly)
    {v : Fin n → S} (hv : IsUnit (cyclicBasisMatrix B v))
    {x : Matrix (Fin n) (Fin n) T} (hx : A.map f * x = x * B.map f) :
    ∃ y : Matrix (Fin n) (Fin n) S, A * y = y * B ∧ y.map f = x := by
  classical
  choose w hw using fun i => hf ((x *ᵥ (f ∘ v)) i)
  let U := hv.unit
  have hU : U.val = cyclicBasisMatrix B v := hv.unit_spec
  let y := cyclicBasisMatrix A w * (U⁻¹).val
  have hy : y * U.val = cyclicBasisMatrix A w := by
    simp only [y, mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, mul_one]
  refine ⟨y, hv.mul_left_inj.mp ?_, (hv.map f.mapMatrix).mul_left_inj.mp ?_⟩
  · change (A * y) * U.val = (y * B) * U.val
    rw [mul_assoc A, hy, mul_cyclicBasisMatrix, hp, mul_assoc y, hU,
      mul_cyclicBasisMatrix B, ← mul_assoc, ← hU, hy]
  · change y.map f * (cyclicBasisMatrix B v).map f = x * (cyclicBasisMatrix B v).map f
    rw [← hU, ← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply, ← map_mul, hy,
      RingHom.mapMatrix_apply, hU]
    change (cyclicBasisMatrix A w).map f = x * (cyclicBasisMatrix B v).map f
    rw [cyclicBasisMatrix_map, cyclicBasisMatrix_map,
      show f ∘ w = x *ᵥ (f ∘ v) from funext hw, mul_cyclicBasisMatrix_of_intertwiner hx]

end MatrixLift

section Cyclic

variable {F F' S T : Type*} [CommRing F] [CommRing F'] [CommRing S] [CommRing T]
  [Algebra F S] [Algebra F' T]
  {n l : ℕ}

/-- The additive operator whose fixed matrices intertwine the two semilinear actions. -/
def cyclicIntertwinerStep (s : S ≃ₐ[F] S) (a b : GeneralLinear n S) :
    Matrix (Fin n) (Fin n) S →+ Matrix (Fin n) (Fin n) S where
  toFun X := a.val * X.map s.toRingHom * b⁻¹.val
  map_zero' := by simp
  map_add' X Y := by simp [Matrix.map_add, mul_add, add_mul]

@[simp] theorem cyclicIntertwinerStep_apply (s : S ≃ₐ[F] S) (a b : GeneralLinear n S)
    (X : Matrix (Fin n) (Fin n) S) : cyclicIntertwinerStep s a b X =
    a.val * X.map s.toRingHom * b⁻¹.val := rfl

theorem cyclicIntertwinerStep_eq_self_iff (s : S ≃ₐ[F] S) (a b : GeneralLinear n S)
    (X : Matrix (Fin n) (Fin n) S) : cyclicIntertwinerStep s a b X = X ↔
    a.val * X.map s.toRingHom = X * b.val := by
  rw [cyclicIntertwinerStep_apply]
  constructor
  · intro h
    have he := congrArg (· * b.val) h
    simpa only [mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, mul_one] using he
  · intro h
    rw [h, mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one]

@[simp] private theorem matrix_map_entrywiseAut (s : S ≃ₐ[F] S) (a : GeneralLinear n S) :
    a.val.map s.toRingHom = (entrywiseAut s n a).val := rfl

private theorem matrix_map_one (X : Matrix (Fin n) (Fin n) S) :
    X.map (1 : S ≃ₐ[F] S).toRingHom = X := by
  ext i j
  rfl

private theorem cyclicIntertwinerStep_iterate (s : S ≃ₐ[F] S) (a b : GeneralLinear n S)
    (X : Matrix (Fin n) (Fin n) S) (k : ℕ) :
    (cyclicIntertwinerStep s a b)^[k] X =
      (cyclicNorm s k a).val * X.map (s ^ k).toRingHom * (cyclicNorm s k b)⁻¹.val := by
  induction k generalizing X with
  | zero =>
    simp
    exact (matrix_map_one (F := F) X).symm
  | succ k ih =>
    rw [Function.iterate_succ_apply, ih, cyclicIntertwinerStep_apply,
      cyclicNorm_succ, cyclicNorm_succ, _root_.mul_inv_rev, Units.val_mul, Units.val_mul]
    simp only [Matrix.map_mul, matrix_map_entrywiseAut, map_inv]
    have hmap : (X.map s.toRingHom).map (s ^ k).toRingHom =
        X.map (s ^ (k + 1)).toRingHom := by
      ext i j
      change (s ^ k) (s (X i j)) = (s ^ (k + 1)) (X i j)
      rw [pow_succ, AlgEquiv.mul_apply]
    rw [hmap]
    simp only [mul_assoc]

private theorem cyclicIntertwinerStep_iterate_eq (s : S ≃ₐ[F] S) (a b : GeneralLinear n S)
    (hs : s ^ l = 1) {X : Matrix (Fin n) (Fin n) S}
    (hX : (cyclicNorm s l a).val * X = X * (cyclicNorm s l b).val) :
    (cyclicIntertwinerStep s a b)^[l] X = X := by
  rw [cyclicIntertwinerStep_iterate, hs, matrix_map_one]
  rw [hX, mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one]

private theorem norm_mul_eq_of_cyclicIntertwiner (s : S ≃ₐ[F] S) (a b : GeneralLinear n S)
    (hs : s ^ l = 1) {X : Matrix (Fin n) (Fin n) S} (hX : cyclicIntertwinerStep s a b X = X) :
    (cyclicNorm s l a).val * X = X * (cyclicNorm s l b).val := by
  have he := Function.iterate_fixed hX l
  rw [cyclicIntertwinerStep_iterate, hs, matrix_map_one] at he
  have he' := congrArg (· * (cyclicNorm s l b).val) he
  simpa only [mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, mul_one] using he'

/-- Ordered cyclic matrix norms commute with equivariant coefficient maps. -/
theorem map_cyclicNorm_of_equivariant (f : S →+* T) {s : S ≃ₐ[F] S} {t : T ≃ₐ[F'] T}
    (h : ∀ x, f (s x) = t (f x)) (a : GeneralLinear n S) (k : ℕ) :
    GeneralLinearGroup.map f (cyclicNorm s k a) = cyclicNorm t k (GeneralLinearGroup.map f a) := by
  have hi (j : ℕ) (x : S) : f ((s ^ j) x) = (t ^ j) (f x) := by
    induction j with
    | zero => rfl
    | succ j ih => simp only [pow_succ', AlgEquiv.mul_apply, h, ih]
  induction k with
  | zero => simp
  | succ k ih =>
    rw [cyclicNorm_succ, cyclicNorm_succ, map_mul, ih]
    congr 1
    ext i j
    exact hi k (a i j)

private theorem cyclicIntertwinerStep_map (f : S →+* T) {s : S ≃ₐ[F] S} {t : T ≃ₐ[F'] T}
    (h : ∀ x, f (s x) = t (f x)) (a b : GeneralLinear n S) :
    Semiconj (fun X => X.map f) (cyclicIntertwinerStep s a b)
      (cyclicIntertwinerStep t (GeneralLinearGroup.map f a) (GeneralLinearGroup.map f b)) := by
  intro X
  simp only [cyclicIntertwinerStep_apply, Matrix.map_mul, ← map_inv]
  have he : (X.map s.toRingHom).map f = (X.map f).map t.toRingHom := Matrix.ext fun i j => h _
  rw [he]
  rfl

/-- A twisted intertwiner after coefficient reduction lifts, up to the scalar cyclic degree,
if the right-hand norm admits a cyclic basis and the two norms have the same characteristic
polynomial. The lift is a matrix and need not be invertible. -/
theorem exists_cyclicIntertwiner_lift (f : S →+* T) (hf : Surjective f)
    {s : S ≃ₐ[F] S} {t : T ≃ₐ[F'] T} (hs : s ^ l = 1) (ht : t ^ l = 1)
    (h : ∀ x, f (s x) = t (f x))
    (a b : GeneralLinear n S)
    (hp : (cyclicNorm s l a).val.charpoly = (cyclicNorm s l b).val.charpoly)
    {v : Fin n → S} (hv : IsUnit (cyclicBasisMatrix (cyclicNorm s l b).val v))
    {x : Matrix (Fin n) (Fin n) T}
    (hx : cyclicIntertwinerStep t (GeneralLinearGroup.map f a) (GeneralLinearGroup.map f b) x = x) :
    ∃ y : Matrix (Fin n) (Fin n) S, cyclicIntertwinerStep s a b y = y ∧ y.map f = l • x := by
  have hm (g : GeneralLinear n S) : (cyclicNorm s l g).val.map f =
      (cyclicNorm t l (GeneralLinearGroup.map f g)).val := congrArg Units.val (map_cyclicNorm_of_equivariant f h g l)
  obtain ⟨z, hz, hzf⟩ := exists_lift_of_norm_intertwiner f hf hp hv
    (by rw [hm, hm]; exact norm_mul_eq_of_cyclicIntertwiner _ _ _ ht hx)
  let u := cyclicIntertwinerStep s a b
  let u' := cyclicIntertwinerStep t (GeneralLinearGroup.map f a) (GeneralLinearGroup.map f b)
  have hz₀ : u^[l] z = z := cyclicIntertwinerStep_iterate_eq s a b hs hz
  refine ⟨∑ k ∈ Finset.range l, u^[k] z, ?_, ?_⟩
  · change u (∑ k ∈ Finset.range l, u^[k] z) = _
    rw [map_sum]
    simp_rw [← Function.iterate_succ_apply']
    have hsum := Finset.sum_range_succ' (fun k => u^[k] z) l
    rw [Finset.sum_range_succ, hz₀] at hsum
    exact add_right_cancel (by simpa [add_comm] using hsum.symm :
      (∑ k ∈ Finset.range l, u^[k + 1] z) + z = (∑ k ∈ Finset.range l, u^[k] z) + z)
  · change f.mapMatrix (∑ k ∈ Finset.range l, u^[k] z) = _
    rw [map_sum]
    have hc : Semiconj (fun X => X.map f) u u' := cyclicIntertwinerStep_map f h a b
    have he (k : ℕ) : f.mapMatrix (u^[k] z) = x :=
      ((hc.iterate_right k) z).trans (hzf.symm ▸ Function.iterate_fixed hx k)
    simp only [he, Finset.sum_const, Finset.card_range]

end Cyclic

end Langlands.BaseChange
