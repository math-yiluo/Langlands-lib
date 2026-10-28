import Langlands.Cohomology.Lie.CoefficientSquareZeroStatement

/-!
# Square-zero of the coefficient Chevalley–Eilenberg differential

The proof uses Cartan calculus for the constructed differential: interior
products, the derivation of the arguments by the adjoint action, and the Lie
derivative.  Cartan's formula, the commutation of the Lie derivative with the
differential, and square-zero are proved by induction on the degree.
-/

namespace Langlands.Cohomology.Lie

open scoped BigOperators

universe u v w

variable {K : Type u} {L : Type v} {M : Type w}
variable [Field K] [LieRing L] [LieAlgebra K L]
variable [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]

/-! ### Tuples and alternating sums -/

omit [LieRing L] in
theorem removeNth_zero_vecCons {n : ℕ} (x : L) (z : Fin n → L) :
    Fin.removeNth 0 (Matrix.vecCons x z) = z := by
  funext k
  simp [Fin.removeNth_apply]

omit [LieRing L] in
theorem removeNth_succ_vecCons {n : ℕ} (j : Fin (n + 1)) (x : L) (z : Fin (n + 1) → L) :
    Fin.removeNth j.succ (Matrix.vecCons x z) = Matrix.vecCons x (Fin.removeNth j z) := by
  funext k
  cases k using Fin.cases with
  | zero => simp [Fin.removeNth_apply]
  | succ k => simp [Fin.removeNth_apply]

omit [LieRingModule L M] [LieModule K L M] in
/-- Split off the first term of an alternating sum. -/
theorem negOnePow_sum_succ {n : ℕ} (φ : Fin (n + 1) → M) :
    ∑ i : Fin (n + 1), (-1 : ℤ) ^ (i : ℕ) • φ i =
      φ 0 - ∑ j : Fin n, (-1 : ℤ) ^ (j : ℕ) • φ j.succ := by
  rw [Fin.sum_univ_succ]
  simp [pow_succ, Finset.sum_neg_distrib, sub_eq_add_neg]

omit [LieRingModule L M] [LieModule K L M] in
/-- Exchanging the first two arguments of a cochain changes its sign. -/
theorem map_vecCons_vecCons_swap {n : ℕ} (g : L [⋀^Fin (n + 2)]→ₗ[K] M) (a b : L)
    (u : Fin n → L) :
    g (Matrix.vecCons a (Matrix.vecCons b u)) =
      -g (Matrix.vecCons b (Matrix.vecCons a u)) := by
  have h := g.curryLeft_same (a + b)
  have h' := congrArg (fun φ : L [⋀^Fin n]→ₗ[K] M => φ u) h
  simp only [map_add, AlternatingMap.curryLeft_add, LinearMap.add_apply,
    AlternatingMap.curryLeft_same, AlternatingMap.add_apply, AlternatingMap.zero_apply,
    zero_add, add_zero, AlternatingMap.curryLeft_apply_apply] at h'
  exact eq_neg_of_add_eq_zero_right h'

/-! ### Interior products -/

omit [LieRingModule L M] [LieModule K L M] in
/-- The interior product with `x`, inserting `x` as the first argument. -/
noncomputable def interiorProduct (x : L) (n : ℕ) :
    Cochains K L M (n + 1) →ₗ[K] Cochains K L M n where
  toFun f := f.curryLeft x
  map_add' f g := by simp
  map_smul' a f := by simp

omit [LieRingModule L M] [LieModule K L M] in
theorem interiorProduct_apply (x : L) {n : ℕ} (f : Cochains K L M (n + 1)) (z : Fin n → L) :
    interiorProduct x n f z = f (Matrix.vecCons x z) := rfl

omit [LieRingModule L M] [LieModule K L M] in
theorem interiorProduct_add_left (x y : L) {n : ℕ} (f : Cochains K L M (n + 1)) :
    interiorProduct (x + y) n f = interiorProduct x n f + interiorProduct y n f :=
  map_add (f.curryLeft) x y

omit [LieRingModule L M] [LieModule K L M] in
/-- Cochains of positive degree are determined by their interior products. -/
theorem ext_interiorProduct {n : ℕ} {g h : Cochains K L M (n + 1)}
    (H : ∀ x : L, interiorProduct x n g = interiorProduct x n h) : g = h := by
  ext v
  have h' := congrArg (fun φ : Cochains K L M n => φ (Fin.tail v)) (H (v 0))
  simp only [interiorProduct_apply] at h'
  rwa [show Matrix.vecCons (v 0) (Fin.tail v) = v from Fin.cons_self_tail v] at h'

/-! ### The derivation of the arguments -/

omit [LieRingModule L M] [LieModule K L M] in
/-- The adjoint action of `x` on the arguments of a cochain, as a derivation:
in positive degree it is the alternating uncurrying of `bracketSeed f x`, and in
degree zero it vanishes. -/
noncomputable def slotDerivation (x : L) :
    (q : ℕ) → Cochains K L M q →ₗ[K] Cochains K L M q
  | 0 => 0
  | n + 1 =>
    { toFun f := AlternatingMap.alternatizeUncurryFin (bracketSeed f x)
      map_add' f g := by simp
      map_smul' a f := by simp }

omit [LieRingModule L M] [LieModule K L M] in
@[simp]
theorem slotDerivation_zero (x : L) :
    slotDerivation (K := K) (M := M) x 0 = 0 := rfl

omit [LieRingModule L M] [LieModule K L M] in
theorem slotDerivation_succ_apply (x : L) {n : ℕ} (f : Cochains K L M (n + 1))
    (v : Fin (n + 1) → L) :
    slotDerivation x (n + 1) f v =
      ∑ k : Fin (n + 1), (-1 : ℤ) ^ (k : ℕ) •
        f (Matrix.vecCons ⁅x, v k⁆ (Fin.removeNth k v)) :=
  AlternatingMap.alternatizeUncurryFin_apply (bracketSeed f x) v

omit [LieRingModule L M] [LieModule K L M] in
/-- The slot derivation evaluated on a tuple with first entry `x`. -/
theorem slotDerivation_succ_vecCons (y x : L) {n : ℕ} (f : Cochains K L M (n + 1))
    (w : Fin n → L) :
    slotDerivation y (n + 1) f (Matrix.vecCons x w) =
      f (Matrix.vecCons ⁅y, x⁆ w) + slotDerivation y n (interiorProduct x n f) w := by
  rw [slotDerivation_succ_apply, negOnePow_sum_succ, sub_eq_add_neg]
  simp only [Matrix.cons_val_zero, removeNth_zero_vecCons, Matrix.cons_val_succ]
  congr 1
  cases n with
  | zero => simp
  | succ m =>
    rw [slotDerivation_succ_apply, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [removeNth_succ_vecCons, interiorProduct_apply, map_vecCons_vecCons_swap f, smul_neg,
      neg_neg]

omit [LieRingModule L M] [LieModule K L M] in
theorem sum_vecCons_lie_swap (x : L) {n : ℕ} (f : Cochains K L M (n + 1))
    (z : Fin (n + 1) → L) :
    ∑ j : Fin (n + 1), (-1 : ℤ) ^ (j : ℕ) • f (Matrix.vecCons ⁅z j, x⁆ (Fin.removeNth j z)) =
      -slotDerivation x (n + 1) f z := by
  rw [slotDerivation_succ_apply, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← smul_neg, ← lie_skew x (z j)]
  congr 1
  change f.curryLeft ⁅z j, x⁆ (Fin.removeNth j z) =
    -(f.curryLeft (-⁅z j, x⁆) (Fin.removeNth j z))
  rw [map_neg, AlternatingMap.neg_apply, neg_neg]

/-! ### The Lie derivative -/

/-- The Lie derivative: the coefficient action minus the slot derivation. -/
noncomputable def lieDerivative (x : L) (q : ℕ) :
    Cochains K L M q →ₗ[K] Cochains K L M q :=
  (LieModule.toEnd K L M x).compAlternatingMapₗ K - slotDerivation x q

theorem lieDerivative_apply (x : L) {q : ℕ} (f : Cochains K L M q) (v : Fin q → L) :
    lieDerivative x q f v = ⁅x, f v⁆ - slotDerivation x q f v := rfl

/-- Interior products and Lie derivatives: `ι_y θ_x = θ_x ι_y - ι_[x,y]`. -/
theorem interiorProduct_lieDerivative (x y : L) {n : ℕ} (f : Cochains K L M (n + 1)) :
    interiorProduct y n (lieDerivative x (n + 1) f) =
      lieDerivative x n (interiorProduct y n f) - interiorProduct ⁅x, y⁆ n f := by
  ext w
  simp only [interiorProduct_apply, lieDerivative_apply, AlternatingMap.sub_apply,
    slotDerivation_succ_vecCons]
  abel

/-- The Lie derivative is a representation: `[θ_x, θ_y] = θ_[x,y]`. -/
theorem lieDerivative_commutator (x y : L) : ∀ (q : ℕ) (f : Cochains K L M q),
    lieDerivative x q (lieDerivative y q f) - lieDerivative y q (lieDerivative x q f) =
      lieDerivative ⁅x, y⁆ q f
  | 0, f => by
    ext v
    simp only [AlternatingMap.sub_apply, lieDerivative_apply, slotDerivation_zero,
      LinearMap.zero_apply, AlternatingMap.zero_apply, sub_zero, lie_lie]
  | n + 1, f => by
    apply ext_interiorProduct
    intro z
    have ih := lieDerivative_commutator x y n (interiorProduct z n f)
    simp only [map_sub, interiorProduct_lieDerivative]
    rw [show ⁅x, ⁅y, z⁆⁆ = ⁅⁅x, y⁆, z⁆ + ⁅y, ⁅x, z⁆⁆ from leibniz_lie x y z,
      interiorProduct_add_left, ← ih]
    abel

/-! ### Cartan's formula -/

/-- The differential as an action sum minus one half of a slot-derivation sum. -/
theorem differential_apply_removeNth (q : ℕ) (f : Cochains K L M q) (v : Fin (q + 1) → L) :
    differential q f v =
      ∑ i : Fin (q + 1), (-1 : ℤ) ^ (i : ℕ) • ⁅v i, f (Fin.removeNth i v)⁆ -
        (2 : K)⁻¹ • ∑ i : Fin (q + 1), (-1 : ℤ) ^ (i : ℕ) •
          slotDerivation (v i) q f (Fin.removeNth i v) := by
  cases q with
  | zero =>
    rw [differential_apply_zero, Fin.sum_univ_one, Fin.sum_univ_one]
    simp only [Fin.val_zero, pow_zero, one_smul, slotDerivation_zero, LinearMap.zero_apply,
      AlternatingMap.zero_apply, smul_zero, sub_zero]
    exact congrArg (fun z : Fin 0 → L => ⁅v 0, f z⁆) (Subsingleton.elim _ _)
  | succ n =>
    change actionPart (n + 1) f v + bracketPart (n + 1) f v = _
    rw [actionPart_apply, sub_eq_add_neg]
    congr 1
    change -((2 : K)⁻¹ • AlternatingMap.alternatizeUncurryFin
      (AlternatingMap.alternatizeUncurryFinLM ∘ₗ bracketSeed f) v) = _
    rw [AlternatingMap.alternatizeUncurryFin_apply]
    rfl

/-- Cartan's formula in degree zero: `ι_x d = θ_x`. -/
theorem interiorProduct_differential_zero (x : L) (f : Cochains K L M 0) :
    interiorProduct x 0 (differential 0 f) = lieDerivative x 0 f := by
  ext z
  rw [interiorProduct_apply, differential_apply_zero, lieDerivative_apply, slotDerivation_zero,
    LinearMap.zero_apply, AlternatingMap.zero_apply, sub_zero, Matrix.cons_val_zero]
  exact congrArg (fun t : Fin 0 → L => ⁅x, f t⁆) (Subsingleton.elim _ _)

variable [CharZero K]

omit [LieRingModule L M] [LieModule K L M] in
private theorem half_add_half (s : M) : (2 : K)⁻¹ • s + (2 : K)⁻¹ • s = s := by
  rw [← add_smul, ← two_mul, mul_inv_cancel₀ (by norm_num : (2 : K) ≠ 0), one_smul]

/-- Cartan's formula in positive degree: `ι_x d + d ι_x = θ_x`. -/
theorem interiorProduct_differential_add (x : L) {n : ℕ} (f : Cochains K L M (n + 1)) :
    interiorProduct x (n + 1) (differential (n + 1) f) + differential n (interiorProduct x n f) =
      lieDerivative x (n + 1) f := by
  ext z
  have h1 : ∑ i : Fin (n + 1 + 1), (-1 : ℤ) ^ (i : ℕ) •
      ⁅Matrix.vecCons x z i, f (Fin.removeNth i (Matrix.vecCons x z))⁆ =
      ⁅x, f z⁆ - ∑ j : Fin (n + 1), (-1 : ℤ) ^ (j : ℕ) •
        ⁅z j, f (Matrix.vecCons x (Fin.removeNth j z))⁆ := by
    rw [negOnePow_sum_succ]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_succ, removeNth_zero_vecCons,
      removeNth_succ_vecCons]
  have h2 : ∑ i : Fin (n + 1 + 1), (-1 : ℤ) ^ (i : ℕ) •
      slotDerivation (Matrix.vecCons x z i) (n + 1) f (Fin.removeNth i (Matrix.vecCons x z)) =
      slotDerivation x (n + 1) f z - (-slotDerivation x (n + 1) f z +
        ∑ j : Fin (n + 1), (-1 : ℤ) ^ (j : ℕ) •
          slotDerivation (z j) n (interiorProduct x n f) (Fin.removeNth j z)) := by
    rw [negOnePow_sum_succ]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_succ, removeNth_zero_vecCons,
      removeNth_succ_vecCons, slotDerivation_succ_vecCons, smul_add, Finset.sum_add_distrib,
      sum_vecCons_lie_swap]
  rw [AlternatingMap.add_apply, interiorProduct_apply, differential_apply_removeNth,
    differential_apply_removeNth, h1, h2, lieDerivative_apply]
  simp only [interiorProduct_apply]
  conv_rhs => rw [← half_add_half (K := K) (slotDerivation x (n + 1) f z)]
  rw [smul_sub, smul_add, smul_neg]
  abel

/-- Cartan's formula, solved for the interior product of the differential. -/
theorem interiorProduct_differential_succ (x : L) {n : ℕ} (f : Cochains K L M (n + 1)) :
    interiorProduct x (n + 1) (differential (n + 1) f) =
      lieDerivative x (n + 1) f - differential n (interiorProduct x n f) :=
  eq_sub_of_add_eq (interiorProduct_differential_add x f)

/-- The Lie derivative commutes with the differential. -/
theorem lieDerivative_differential (x : L) : ∀ (q : ℕ) (f : Cochains K L M q),
    lieDerivative x (q + 1) (differential q f) = differential q (lieDerivative x q f)
  | 0, f => by
    apply ext_interiorProduct
    intro y
    rw [interiorProduct_lieDerivative, interiorProduct_differential_zero,
      interiorProduct_differential_zero, interiorProduct_differential_zero,
      ← lieDerivative_commutator x y 0 f]
    abel
  | n + 1, f => by
    apply ext_interiorProduct
    intro z
    have ih := lieDerivative_differential x n (interiorProduct z n f)
    rw [interiorProduct_lieDerivative, interiorProduct_differential_succ,
      interiorProduct_differential_succ, interiorProduct_differential_succ,
      interiorProduct_lieDerivative]
    simp only [map_sub]
    rw [ih, ← lieDerivative_commutator x z (n + 1) f]
    abel

/-- The constructed differential squares to zero on every cochain. -/
theorem differential_differential : ∀ (q : ℕ) (f : Cochains K L M q),
    differential (q + 1) (differential q f) = 0
  | 0, f => by
    apply ext_interiorProduct
    intro x
    rw [interiorProduct_differential_succ, interiorProduct_differential_zero,
      lieDerivative_differential, sub_self, map_zero]
  | n + 1, f => by
    apply ext_interiorProduct
    intro x
    rw [interiorProduct_differential_succ, interiorProduct_differential_succ, map_sub,
      differential_differential n, sub_zero, lieDerivative_differential, sub_self, map_zero]

end Langlands.Cohomology.Lie

namespace Langlands.Cohomology.Lie

universe u v w

/-- The published square-zero proposition for the constructed coefficient differential. -/
theorem differentialSquareZero (K : Type u) (L : Type v) (M : Type w)
    [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
    [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M] :
    DifferentialSquareZero K L M := fun q =>
  LinearMap.ext fun f => differential_differential q f

end Langlands.Cohomology.Lie
