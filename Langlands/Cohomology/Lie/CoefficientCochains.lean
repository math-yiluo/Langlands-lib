import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.LinearAlgebra.Alternating.Uncurry.Fin
import Mathlib.Tactic

/-!
# Coefficient-valued Chevalley–Eilenberg cochains

The differential is constructed from alternating uncurrying of the coefficient
action and of the Lie bracket. No square-zero assertion is part of this module.
-/

namespace Langlands.Cohomology.Lie

open scoped BigOperators

universe u v w

variable (K : Type u) (L : Type v) (M : Type w)
variable [Field K] [LieRing L] [LieAlgebra K L]
variable [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]

/-- Degree `q` cochains, with no dimension restriction on the coefficient module. -/
abbrev Cochains (q : ℕ) := L [⋀^Fin q]→ₗ[K] M

variable {K L M}

/-- Remove the indicated entry, preserving the order of the others. -/
def omitNth {q : ℕ} (i : Fin (q + 1)) (x : Fin (q + 1) → L) : Fin q → L :=
  fun k => x (i.succAbove k)

omit [LieRing L] in
@[simp]
theorem omitNth_zero {q : ℕ} (x : L) (z : Fin q → L) :
    omitNth 0 (Matrix.vecCons x z) = z := rfl

omit [LieRing L] in
@[simp]
theorem omitNth_one_pair (x y : L) : omitNth 1 ![x, y] = ![x] := by
  ext k
  fin_cases k
  rfl

/-- Insert the bracket first after omitting entries `i` and `j+1`.
The condition `i ≤ j` makes these the increasing pair `i.castSucc < j.succ`. -/
def bracketFirst {n : ℕ} (i j : Fin (n + 1)) (x : Fin (n + 2) → L) :
    Fin (n + 1) → L :=
  Matrix.vecCons ⁅x i.castSucc, x j.succ⁆ (omitNth j (omitNth i.castSucc x))

theorem bracketFirst_indices {n : ℕ} (i j : Fin (n + 1)) (hij : i ≤ j) :
    i.castSucc < j.succ := by
  simpa only [Fin.lt_def, Fin.val_castSucc, Fin.val_succ] using
    Nat.lt_succ_of_le (show i.val ≤ j.val from hij)

/-- The coefficient action, linear in its distinguished argument. -/
noncomputable def actionSeed {q : ℕ} (f : Cochains K L M q) :
    L →ₗ[K] Cochains K L M q where
  toFun x := (LieModule.toEnd K L M x).compAlternatingMap f
  map_add' x y := by
    ext z
    simp
  map_smul' a x := by
    ext z
    simp

@[simp]
theorem actionSeed_apply {q : ℕ} (f : Cochains K L M q) (x : L) (z : Fin q → L) :
    actionSeed f x z = ⁅x, f z⁆ := rfl

@[simp]
theorem actionSeed_add {q : ℕ} (f g : Cochains K L M q) :
    actionSeed (f + g) = actionSeed f + actionSeed g := by
  ext x z
  simp

@[simp]
theorem actionSeed_smul {q : ℕ} (a : K) (f : Cochains K L M q) :
    actionSeed (a • f) = a • actionSeed f := by
  ext x z
  simp

/-- The action part of the coefficient coboundary. -/
noncomputable def actionPart (q : ℕ) : Cochains K L M q →ₗ[K] Cochains K L M (q + 1) where
  toFun f := AlternatingMap.alternatizeUncurryFin (actionSeed f)
  map_add' f g := by simp
  map_smul' a f := by simp

theorem actionPart_apply {q : ℕ} (f : Cochains K L M q) (x : Fin (q + 1) → L) :
    actionPart q f x = ∑ i : Fin (q + 1), (-1 : ℤ) ^ (i : ℕ) • ⁅x i, f (omitNth i x)⁆ := by
  exact AlternatingMap.alternatizeUncurryFin_apply (actionSeed f) x

/-- Apply the curried cochain to the bracket, bilinearly in `x` and `y`. -/
noncomputable def bracketSeed {n : ℕ} (f : Cochains K L M (n + 1)) :
    L →ₗ[K] L →ₗ[K] Cochains K L M n where
  toFun x := f.curryLeft ∘ₗ (LieAlgebra.ad K L x)
  map_add' x y := by
    ext z v
    simp
  map_smul' a x := by
    ext z v
    simp

omit [LieRingModule L M] [LieModule K L M] in
@[simp]
theorem bracketSeed_apply {n : ℕ} (f : Cochains K L M (n + 1)) (x y : L)
    (z : Fin n → L) :
    bracketSeed f x y z = f (Matrix.vecCons ⁅x, y⁆ z) := rfl

omit [LieRingModule L M] [LieModule K L M] in
@[simp]
theorem bracketSeed_add {n : ℕ} (f g : Cochains K L M (n + 1)) :
    bracketSeed (f + g) = bracketSeed f + bracketSeed g := by
  ext x y z
  simp

omit [LieRingModule L M] [LieModule K L M] in
@[simp]
theorem bracketSeed_smul {n : ℕ} (a : K) (f : Cochains K L M (n + 1)) :
    bracketSeed (a • f) = a • bracketSeed f := by
  ext x y z
  simp

/-- The bracket part; double alternating uncurrying counts every pair twice. -/
noncomputable def bracketPart : (q : ℕ) → Cochains K L M q →ₗ[K] Cochains K L M (q + 1)
  | 0 => 0
  | n + 1 =>
    { toFun f := -((2 : K)⁻¹ • AlternatingMap.alternatizeUncurryFin
        (AlternatingMap.alternatizeUncurryFinLM ∘ₗ bracketSeed f))
      map_add' f g := by
        simp only [bracketSeed_add, LinearMap.comp_add,
          AlternatingMap.alternatizeUncurryFin_add, smul_add]
        abel
      map_smul' a f := by
        simp only [bracketSeed_smul, LinearMap.comp_smul,
          AlternatingMap.alternatizeUncurryFin_smul, smul_neg, smul_smul, RingHom.id_apply]
        rw [mul_comm] }

/-- The actual Chevalley–Eilenberg coefficient differential. -/
noncomputable def differential (q : ℕ) :
    Cochains K L M q →ₗ[K] Cochains K L M (q + 1) :=
  actionPart q + bracketPart q

omit [LieRingModule L M] [LieModule K L M] in
/-- View a coefficient vector as a degree-zero cochain. -/
def ofCoefficient (m : M) : Cochains K L M 0 :=
  AlternatingMap.constOfIsEmpty K L (Fin 0) m

omit [LieRingModule L M] [LieModule K L M] in
@[simp]
theorem ofCoefficient_apply (m : M) (x : Fin 0 → L) :
    ofCoefficient (K := K) (L := L) m x = m := rfl

/-- The differential in degree zero, for an arbitrary zero cochain. -/
theorem differential_apply_zero (f : Cochains K L M 0) (x : Fin 1 → L) :
    differential 0 f x = ⁅x 0, f Fin.elim0⁆ := by
  change actionPart 0 f x + 0 = _
  rw [actionPart_apply, add_zero]
  change (∑ i : Fin 1, (-1 : ℤ) ^ (i : ℕ) • ⁅x i, f (omitNth i x)⁆) = _
  rw [Fin.sum_univ_one]
  simp only [Fin.val_zero, pow_zero, one_smul]
  exact congrArg (fun z : Fin 0 → L => ⁅x 0, f z⁆) (Subsingleton.elim _ _)

/-- In degree zero the coboundary is the coefficient action. -/
theorem differential_ofCoefficient (m : M) (x : L) :
    differential 0 (ofCoefficient (K := K) (L := L) m) ![x] = ⁅x, m⁆ := by
  simp only [differential_apply_zero, Matrix.cons_val_zero, ofCoefficient_apply]

variable [CharZero K]

omit [LieRingModule L M] [LieModule K L M] in
private theorem half_double (z : M) : (2 : K)⁻¹ • (z + z) = z := by
  rw [← two_smul K z, smul_smul, inv_mul_cancel₀ (by norm_num : (2 : K) ≠ 0), one_smul]

omit [LieRingModule L M] [LieModule K L M] in
theorem bracketPart_apply {n : ℕ} (f : Cochains K L M (n + 1))
    (x : Fin (n + 2) → L) :
    bracketPart (n + 1) f x =
      ∑ i : Fin (n + 1), ∑ j ∈ Finset.Ici i,
        (-1 : ℤ) ^ ((i : ℕ) + (j : ℕ) + 1) • f (bracketFirst i j x) := by
  change -((2 : K)⁻¹ •
    AlternatingMap.alternatizeUncurryFin
      (AlternatingMap.alternatizeUncurryFinLM ∘ₗ bracketSeed f) x) = _
  rw [AlternatingMap.alternatizeUncurryFin_alternatizeUncurryFinLM_comp_apply]
  simp only [Finset.smul_sum, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  have hskew : bracketSeed f (x j.succ) (x i.castSucc)
      (j.removeNth (i.castSucc.removeNth x)) =
      -bracketSeed f (x i.castSucc) (x j.succ)
        (j.removeNth (i.castSucc.removeNth x)) := by
    change (f.curryLeft ⁅x j.succ, x i.castSucc⁆) _ =
      -(f.curryLeft ⁅x i.castSucc, x j.succ⁆) _
    rw [← lie_skew (x j.succ) (x i.castSucc)]
    simp only [map_neg, AlternatingMap.neg_apply]
  rw [hskew, sub_neg_eq_add, smul_comm (2 : K)⁻¹, half_double]
  simp only [pow_succ, mul_neg_one, neg_smul]
  rfl

theorem differential_apply_succ {n : ℕ} (f : Cochains K L M (n + 1))
    (x : Fin (n + 2) → L) :
    differential (n + 1) f x =
      (∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • ⁅x i, f (omitNth i x)⁆) +
      ∑ i : Fin (n + 1), ∑ j ∈ Finset.Ici i,
        (-1 : ℤ) ^ ((i : ℕ) + (j : ℕ) + 1) • f (bracketFirst i j x) := by
  exact congrArg₂ (· + ·) (actionPart_apply f x) (bracketPart_apply f x)

/-- In degree one, `df(x,y) = x.f(y) - y.f(x) - f([x,y])`. -/
theorem differential_one (f : Cochains K L M 1) (x y : L) :
    differential 1 f ![x, y] =
      ⁅x, f ![y]⁆ - ⁅y, f ![x]⁆ - f ![⁅x, y⁆] := by
  rw [differential_apply_succ]
  simp [Fin.sum_univ_two, bracketFirst, sub_eq_add_neg]

section CoefficientMaps

universe w'
variable {N : Type w'} [AddCommGroup N] [Module K N]
variable [LieRingModule L N] [LieModule K L N]

/-- Direct postcomposition of cochains by an equivariant coefficient map. -/
noncomputable def map (φ : M →ₗ⁅K,L⁆ N) (q : ℕ) :
    Cochains K L M q →ₗ[K] Cochains K L N q :=
  φ.toLinearMap.compAlternatingMapₗ K

omit [LieModule K L M] [CharZero K] [LieModule K L N] in
@[simp]
theorem map_apply (φ : M →ₗ⁅K,L⁆ N) (q : ℕ) (f : Cochains K L M q) (x : Fin q → L) :
    map φ q f x = φ (f x) := rfl

/-- Coefficient postcomposition commutes with the constructed differential. -/
theorem map_differential (φ : M →ₗ⁅K,L⁆ N) (q : ℕ) (f : Cochains K L M q) :
    map φ (q + 1) (differential q f) = differential q (map φ q f) := by
  ext x
  cases q with
  | zero => simp only [map_apply, differential_apply_zero, φ.map_lie]
  | succ n =>
    simp only [map_apply, differential_apply_succ, map_add, map_sum, map_zsmul, φ.map_lie]

end CoefficientMaps

end Langlands.Cohomology.Lie
