import Langlands.GroupScheme.FiniteAlgebraBinaryDynamic
import Mathlib.Data.Matrix.PEquiv

/-!
# Weighted diagonal cocharacters of finite matrix-algebra unit groups

Let `k` be a field, `D` a `k`-algebra, `n` a finite index type and `w : n → ℤ` a weight
function. On the unit group scheme of `M_n(D)`, the diagonal matrices `diag(t^{w i})` form an
actual cocharacter. If every weight is `-1`, `0` or `1`, then every invertible matrix `u` over
the tensor coefficient algebra of a test scheme with contracting shape (`u i j = δ i j` whenever
`w i ≤ w j`) lies in the dynamic unipotent subgroup functor of this cocharacter: with
`u = 1 + N`, the curve `s ↦ 1 + N(s)`, `N(s) i j = s^{w i - w j} N i j`, extends the conjugation
orbit and is the identity at `s = 0`. Its inverse is `1 - N(s) + N(s)²`, since `N³ = 0`.
-/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
  CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme.FiniteAlgebraUnits.WeightedRoot

open BinaryRoot

section Matrices

variable {n : Type} [Fintype n] [DecidableEq n]

section Diagonal

variable {R S : Type u} [CommRing R] [Ring S] [Algebra R S]

/-- The diagonal unit `diag(t^{w i})`. -/
def weightMatrix (w : n → ℤ) (t : Rˣ) : Matrix.GeneralLinearGroup n S where
  val := Matrix.diagonal fun i => algebraMap R S ((t ^ w i : Rˣ) : R)
  inv := Matrix.diagonal fun i => algebraMap R S ((t ^ (-w i) : Rˣ) : R)
  val_inv := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    rw [← map_mul, ← Units.val_mul, ← zpow_add, add_neg_cancel, zpow_zero, Units.val_one,
      map_one]
  inv_val := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    rw [← map_mul, ← Units.val_mul, ← zpow_add, neg_add_cancel, zpow_zero, Units.val_one,
      map_one]

theorem weightMatrix_val (w : n → ℤ) (t : Rˣ) :
    ((weightMatrix w t : Matrix.GeneralLinearGroup n S) : Matrix n n S) =
      Matrix.diagonal fun i => algebraMap R S ((t ^ w i : Rˣ) : R) :=
  rfl

theorem weightMatrix_inv_val (w : n → ℤ) (t : Rˣ) :
    (((weightMatrix w t)⁻¹ : Matrix.GeneralLinearGroup n S) : Matrix n n S) =
      Matrix.diagonal fun i => algebraMap R S ((t ^ (-w i) : Rˣ) : R) :=
  rfl

/-- The weighted diagonal units form a homomorphism. -/
def weightMatrixHom (w : n → ℤ) : Rˣ →* Matrix.GeneralLinearGroup n S where
  toFun := weightMatrix w
  map_one' := by
    apply Units.ext
    rw [weightMatrix_val, Units.val_one, ← Matrix.diagonal_one]
    congr 1
    funext i
    rw [one_zpow, Units.val_one, map_one]
  map_mul' t v := by
    apply Units.ext
    rw [Units.val_mul, weightMatrix_val, weightMatrix_val, weightMatrix_val,
      Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    rw [mul_zpow, Units.val_mul, map_mul]

theorem weightMatrixHom_apply (w : n → ℤ) (t : Rˣ) :
    (weightMatrixHom w t : Matrix.GeneralLinearGroup n S) = weightMatrix w t :=
  rfl

/-- Conjugation by `diag(t^{w i})` multiplies the `(i, j)` entry by `t^{w i - w j}`. -/
theorem weightMatrix_conj_apply (w : n → ℤ) (t : Rˣ) (M : Matrix n n S) (i j : n) :
    ((weightMatrix w t : Matrix.GeneralLinearGroup n S) * M *
        (((weightMatrix w t)⁻¹ : Matrix.GeneralLinearGroup n S) : Matrix n n S)) i j =
      algebraMap R S ((t ^ (w i - w j) : Rˣ) : R) * M i j := by
  rw [weightMatrix_val, weightMatrix_inv_val, Matrix.mul_diagonal, Matrix.diagonal_mul,
    mul_assoc, ← Algebra.commutes, ← mul_assoc, ← map_mul, ← Units.val_mul, ← zpow_add,
    ← sub_eq_add_neg]

theorem weightMatrixHom_conj_apply (w : n → ℤ) (t : Rˣ) (M : Matrix n n S) (i j : n) :
    ((weightMatrixHom (S := S) w t : Matrix.GeneralLinearGroup n S) * M *
        (((weightMatrixHom (S := S) w t)⁻¹ : Matrix.GeneralLinearGroup n S) : Matrix n n S)) i j =
      algebraMap R S ((t ^ (w i - w j) : Rˣ) : R) * M i j :=
  weightMatrix_conj_apply w t M i j

theorem weightMatrix_add (w w' : n → ℤ) (t : Rˣ) :
    (weightMatrix (w + w') t : Matrix.GeneralLinearGroup n S) =
      weightMatrix w t * weightMatrix w' t := by
  apply Units.ext
  rw [Units.val_mul, weightMatrix_val, weightMatrix_val, weightMatrix_val,
    Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  rw [Pi.add_apply, zpow_add, Units.val_mul, map_mul]

theorem weightMatrix_neg (w : n → ℤ) (t : Rˣ) :
    (weightMatrix (-w) t : Matrix.GeneralLinearGroup n S) = (weightMatrix w t)⁻¹ := by
  apply Units.ext
  rw [weightMatrix_val, weightMatrix_inv_val]
  rfl

/-- The permutation matrix of the transposition of `a` and `b`. -/
def swapMatrix (a b : n) : Matrix n n S :=
  (Equiv.swap a b).toPEquiv.toMatrix

omit [CommRing R] [Algebra R S] in
theorem swapMatrix_mul_self (a b : n) :
    (swapMatrix a b : Matrix n n S) * swapMatrix a b = 1 := by
  rw [swapMatrix, PEquiv.toMatrix_toPEquiv_mul]
  ext i j
  simp [PEquiv.toMatrix_apply, Matrix.one_apply, Equiv.swap_apply_self]

/-- The transposition matrix as a unit, equal to its inverse. -/
def swapUnit (a b : n) : Matrix.GeneralLinearGroup n S where
  val := swapMatrix a b
  inv := swapMatrix a b
  val_inv := swapMatrix_mul_self a b
  inv_val := swapMatrix_mul_self a b

/-- Conjugation by the transposition matrix permutes the weights. -/
theorem swapUnit_conj_weightMatrix (a b : n) (w : n → ℤ) (t : Rˣ) :
    swapUnit a b * (weightMatrix w t : Matrix.GeneralLinearGroup n S) * (swapUnit a b)⁻¹ =
      weightMatrix (fun i => w (Equiv.swap a b i)) t := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, weightMatrix_val, weightMatrix_val]
  change swapMatrix a b * _ * swapMatrix a b = _
  rw [swapMatrix, PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv,
    Matrix.submatrix_submatrix, Equiv.symm_swap]
  exact Matrix.submatrix_diagonal_equiv _ _

theorem map_swapUnit {S' : Type u} [Ring S'] (f : S →+* S') (a b : n) :
    Units.map (RingHom.mapMatrix f).toMonoidHom (swapUnit a b : Matrix.GeneralLinearGroup n S) =
      swapUnit a b := by
  apply Units.ext
  ext i j
  change f (swapMatrix a b i j) = swapMatrix a b i j
  simp only [swapMatrix, PEquiv.toMatrix_apply]
  split_ifs <;> simp

end Diagonal

/-- The weight `1` at `a` and `0` elsewhere. -/
def indicatorWeight {n : Type} [DecidableEq n] (a : n) : n → ℤ :=
  fun i => if i = a then 1 else 0

/-- The weight `1` at `a`, `-1` at `b` and `0` elsewhere. -/
def pairWeight {n : Type} [DecidableEq n] (a b : n) : n → ℤ :=
  fun i => (if i = a then 1 else 0) - (if i = b then 1 else 0)

theorem pairWeight_eq {n : Type} [DecidableEq n] (a b : n) :
    pairWeight a b = indicatorWeight a + -(fun i => indicatorWeight a (Equiv.swap a b i)) := by
  funext i
  simp only [pairWeight, indicatorWeight, Pi.add_apply, Pi.neg_apply, Equiv.swap_apply_eq_iff,
    Equiv.swap_apply_left]
  omega

theorem pairWeight_mem {n : Type} [DecidableEq n] {a b : n} (hab : a ≠ b) (i : n) :
    pairWeight a b i = -1 ∨ pairWeight a b i = 0 ∨ pairWeight a b i = 1 := by
  simp only [pairWeight]
  split_ifs with h1 h2 <;> first | (subst h1; subst h2; exact absurd rfl hab) | omega

theorem weightMatrix_pairWeight {R S : Type u} [CommRing R] [Ring S] [Algebra R S]
    (a b : n) (t : Rˣ) :
    (weightMatrix (pairWeight a b) t : Matrix.GeneralLinearGroup n S) =
      weightMatrix (indicatorWeight a) t *
        (swapUnit a b * weightMatrix (indicatorWeight a) t * (swapUnit a b)⁻¹)⁻¹ := by
  rw [swapUnit_conj_weightMatrix, pairWeight_eq, weightMatrix_add, weightMatrix_neg]

/-- The weighted diagonal commutes with change of commutative coefficient algebra. -/
theorem map_weightMatrix {A B C E : Type u}
    [CommRing A] [CommRing B] [Ring C] [Ring E] [Algebra A C] [Algebra B E]
    (f : A →+* B) (g : C →+* E)
    (h : ∀ a, g (algebraMap A C a) = algebraMap B E (f a))
    (w : n → ℤ) (t : Aˣ) :
    Units.map (RingHom.mapMatrix g).toMonoidHom (weightMatrixHom (S := C) w t) =
      weightMatrixHom (S := E) w (Units.map f.toMonoidHom t) := by
  apply Units.ext
  ext i j
  change g (((weightMatrix (S := C) w t : Matrix.GeneralLinearGroup n C) : Matrix n n C) i j) =
    ((weightMatrix (S := E) w (Units.map f.toMonoidHom t) : Matrix.GeneralLinearGroup n E) :
      Matrix n n E) i j
  rw [weightMatrix_val, weightMatrix_val]
  by_cases hij : i = j
  · subst hij
    rw [Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq, h, ← map_zpow]
    rfl
  · rw [Matrix.diagonal_apply_ne _ hij, Matrix.diagonal_apply_ne _ hij, map_zero]

section Contracting

variable {S : Type u} [Ring S]

/-- A matrix is weight-strict for `w` when its entries vanish at the positions with
`w i ≤ w j`. -/
def IsWeightStrict (w : n → ℤ) (M : Matrix n n S) : Prop :=
  ∀ i j, w i ≤ w j → M i j = 0

omit [DecidableEq n] in
/-- A weight-strict matrix cubes to zero when all weights are `-1`, `0` or `1`. -/
theorem cube_eq_zero {w : n → ℤ} (hw : ∀ i, w i = -1 ∨ w i = 0 ∨ w i = 1)
    {M : Matrix n n S} (hM : IsWeightStrict w M) : M * M * M = 0 := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.zero_apply, Finset.sum_mul]
  refine Finset.sum_eq_zero fun l _ => Finset.sum_eq_zero fun k _ => ?_
  by_cases h1 : w i ≤ w k
  · rw [hM i k h1, zero_mul, zero_mul]
  by_cases h2 : w k ≤ w l
  · rw [hM k l h2, mul_zero, zero_mul]
  by_cases h3 : w l ≤ w j
  · rw [hM l j h3, mul_zero]
  exfalso
  rcases hw i with hi | hi | hi <;> rcases hw j with hj | hj | hj <;> omega

/-- The unipotent unit `1 + M` with inverse `1 - M + M²`, for `M³ = 0`. -/
def unipotentUnit (M : Matrix n n S) (hM : M * M * M = 0) : Matrix.GeneralLinearGroup n S where
  val := 1 + M
  inv := 1 - M + M * M
  val_inv := by
    have e : (1 + M) * (1 - M + M * M) = 1 + M * M * M := by noncomm_ring
    rw [e, hM, add_zero]
  inv_val := by
    have e : (1 - M + M * M) * (1 + M) = 1 + M * M * M := by noncomm_ring
    rw [e, hM, add_zero]

@[simp] theorem unipotentUnit_val (M : Matrix n n S) (hM : M * M * M = 0) :
    ((unipotentUnit M hM : Matrix.GeneralLinearGroup n S) : Matrix n n S) = 1 + M :=
  rfl

/-- The curve parameter `M(s) i j = s^{(w i - w j)₊} M i j`. -/
def scale (w : n → ℤ) (s : S) (M : Matrix n n S) : Matrix n n S :=
  Matrix.of fun i j => s ^ (w i - w j).toNat * M i j

omit [Fintype n] [DecidableEq n] in
theorem scale_apply (w : n → ℤ) (s : S) (M : Matrix n n S) (i j : n) :
    scale w s M i j = s ^ (w i - w j).toNat * M i j :=
  rfl

omit [Fintype n] [DecidableEq n] in
theorem isWeightStrict_scale {w : n → ℤ} (s : S) {M : Matrix n n S} (hM : IsWeightStrict w M) :
    IsWeightStrict w (scale w s M) := by
  intro i j hij
  rw [scale_apply, hM i j hij, mul_zero]

omit [Fintype n] [DecidableEq n] in
theorem isWeightStrict_map {T F : Type*} [Ring T] [FunLike F S T] [ZeroHomClass F S T] (f : F)
    {w : n → ℤ} {M : Matrix n n S} (hM : IsWeightStrict w M) :
    IsWeightStrict w (M.map f) := by
  intro i j hij
  rw [Matrix.map_apply, hM i j hij, map_zero]

omit [Fintype n] [DecidableEq n] in
theorem map_scale {T : Type u} [Ring T] (f : S →+* T) (w : n → ℤ) (s : S) (M : Matrix n n S) :
    (scale w s M).map f = scale w (f s) (M.map f) := by
  ext i j
  rw [Matrix.map_apply, scale_apply, scale_apply, map_mul, map_pow, Matrix.map_apply]

omit [Fintype n] [DecidableEq n] in
theorem scale_zero {w : n → ℤ} {M : Matrix n n S} (hM : IsWeightStrict w M) :
    scale w 0 M = 0 := by
  ext i j
  rw [scale_apply, Matrix.zero_apply]
  by_cases h : w i ≤ w j
  · rw [hM i j h, mul_zero]
  · rw [zero_pow (by omega), zero_mul]

omit [Fintype n] in
/-- A matrix of contracting shape minus the identity is weight-strict. -/
theorem isWeightStrict_sub_one {w : n → ℤ} {u : Matrix n n S}
    (hu : ∀ i j, w i ≤ w j → u i j = (1 : Matrix n n S) i j) :
    IsWeightStrict w (u - 1) := by
  intro i j hij
  rw [Matrix.sub_apply, hu i j hij, sub_self]

omit [Fintype n] in
/-- A ring map preserves contracting shape. -/
theorem map_contracting {T F : Type*} [Ring T] [FunLike F S T] [RingHomClass F S T] (f : F)
    {w : n → ℤ} {U : Matrix n n S} (hU : ∀ i j, w i ≤ w j → U i j = (1 : Matrix n n S) i j) :
    ∀ i j, w i ≤ w j → U.map f i j = (1 : Matrix n n T) i j := by
  intro i j hij
  rw [Matrix.map_apply, hU i j hij]
  by_cases h : i = j
  · subst h
    rw [Matrix.one_apply_eq, Matrix.one_apply_eq, map_one]
  · rw [Matrix.one_apply_ne h, Matrix.one_apply_ne h, map_zero]

/-- Conjugating a matrix `U` of contracting shape by `diag(t^{w i})` gives `1 + (U - 1)(t)`. -/
theorem weightMatrix_conj_eq {R : Type u} [CommRing R] [Algebra R S] (w : n → ℤ) (t : Rˣ)
    (U : Matrix n n S) (hU : ∀ i j, w i ≤ w j → U i j = (1 : Matrix n n S) i j) :
    ((weightMatrix (S := S) w t : Matrix.GeneralLinearGroup n S) : Matrix n n S) * U *
        (((weightMatrix (S := S) w t)⁻¹ : Matrix.GeneralLinearGroup n S) : Matrix n n S) =
      1 + scale w (algebraMap R S (t : R)) (U - 1) := by
  ext i j
  rw [weightMatrix_conj_apply, Matrix.add_apply, scale_apply, Matrix.sub_apply]
  by_cases hij : w i ≤ w j
  · rw [hU i j hij, sub_self, mul_zero, add_zero]
    by_cases h : i = j
    · subst h
      rw [sub_self, zpow_zero, Units.val_one, map_one, one_mul]
    · rw [Matrix.one_apply_ne h, mul_zero]
  · have hne : i ≠ j := fun h => hij (h ▸ le_rfl)
    have he : w i - w j = ((w i - w j).toNat : ℤ) := (Int.toNat_of_nonneg (by omega)).symm
    rw [Matrix.one_apply_ne hne, sub_zero, zero_add, he, zpow_natCast, Units.val_pow_eq_pow_val,
      map_pow, Int.toNat_natCast]

end Contracting

end Matrices

variable (k D : Type u) [Field k] [Ring D] [Algebra k D]
  {n : Type} [Fintype n] [DecidableEq n] {d : ℕ} (b : Module.Basis (Fin d) k (Matrix n n D))

/-- The weighted diagonal on every actual relative point group. -/
def cocharacterPoints (w : n → ℤ) (T : Over (base k)) :
    (T ⟶ (Gm (base k)).X) →* (T ⟶ (groupScheme b).X) :=
  (MatrixPoints.tensorMatrixEquiv k D b T).symm.toMonoidHom.comp
    ((weightMatrixHom (R := ((algΓ (CommRingCat.of k)).obj T).unop)
      (S := tensorAlgebra k D T) w).comp (Gm.pointsEquiv (base k) T).toMonoidHom)

theorem tensorMatrixEquiv_cocharacterPoints (w : n → ℤ) (T : Over (base k))
    (x : T ⟶ (Gm (base k)).X) :
    MatrixPoints.tensorMatrixEquiv k D b T (cocharacterPoints k D b w T x) =
      weightMatrixHom (R := ((algΓ (CommRingCat.of k)).obj T).unop)
        (S := tensorAlgebra k D T) w (Gm.pointsEquiv (base k) T x) :=
  (MatrixPoints.tensorMatrixEquiv k D b T).apply_symm_apply _

theorem cocharacterPoints_naturality (w : n → ℤ)
    {T T' : Over (base k)} (a : T' ⟶ T) (x : T ⟶ (Gm (base k)).X) :
    cocharacterPoints k D b w T' (a ≫ x) = a ≫ cocharacterPoints k D b w T x := by
  apply (MatrixPoints.tensorMatrixEquiv k D b T').injective
  rw [MatrixPoints.tensorMatrixEquiv_naturality, tensorMatrixEquiv_cocharacterPoints,
    tensorMatrixEquiv_cocharacterPoints]
  erw [map_weightMatrix
    (A := ((algΓ (CommRingCat.of k)).obj T).unop)
    (B := ((algΓ (CommRingCat.of k)).obj T').unop)
    ((algΓ (CommRingCat.of k)).map a).unop.hom.toRingHom
    (tensorMap k D a).toRingHom (tensorMap_includeSections k D a)]
  rw [Gm.pointsEquiv_naturality]
  rfl

/-- The actual ground-field cocharacter `t ↦ diag(t^{w i})`. -/
def cocharacter (w : n → ℤ) : (Gm (base k)).toGrp ⟶ groupScheme b :=
  homOfPoints (cocharacterPoints k D b w) (cocharacterPoints_naturality k D b w)

/-- On every test the actual cocharacter has its prescribed weighted diagonal. -/
theorem tensorMatrixEquiv_cocharacter (w : n → ℤ) {T : Over (base k)}
    (x : T ⟶ (Gm (base k)).X) :
    MatrixPoints.tensorMatrixEquiv k D b T (x ≫ (cocharacter k D b w).hom.hom) =
      weightMatrixHom (R := ((algΓ (CommRingCat.of k)).obj T).unop)
        (S := tensorAlgebra k D T) w (Gm.pointsEquiv (base k) T x) := by
  rw [cocharacter, comp_homOfPoints]
  exact tensorMatrixEquiv_cocharacterPoints k D b w T x

variable {k D b}

section Contraction

variable {w : n → ℤ} (hw : ∀ i, w i = -1 ∨ w i = 0 ∨ w i = 1) {T : Over (base k)}
  (u : Matrix.GeneralLinearGroup n (tensorAlgebra k D T))
  (hu : ∀ i j, w i ≤ w j →
    (u : Matrix n n (tensorAlgebra k D T)) i j = (1 : Matrix n n (tensorAlgebra k D T)) i j)

/-- The coordinate of the affine line, as a central scalar on `T × A¹`. -/
abbrev lineScalar (T : Over (base k)) : tensorAlgebra k D (T ⊗ AffineLine.scheme (base k)) :=
  includeSections k D _
    ((snd T (AffineLine.scheme (base k))).left.appTop (AffineLine.coord (base k)))

variable (w) in
/-- The weight-strict part of `u`, pulled back to `T × A¹` and scaled by the coordinate. -/
def curveMatrix : Matrix n n (tensorAlgebra k D (T ⊗ AffineLine.scheme (base k))) :=
  scale w (lineScalar (k := k) (D := D) T)
    (((u : Matrix n n (tensorAlgebra k D T)) - 1).map
      (tensorMap k D (fst T (AffineLine.scheme (base k)))))

include hu in
theorem isWeightStrict_curveMatrix : IsWeightStrict w (curveMatrix w u) :=
  isWeightStrict_scale _ (isWeightStrict_map _ (isWeightStrict_sub_one hu))

/-- The contraction curve `s ↦ 1 + N(s)` on `T × A¹`. -/
def contraction : T ⊗ AffineLine.scheme (base k) ⟶ (groupScheme b).X :=
  (MatrixPoints.tensorMatrixEquiv k D b _).symm
    (unipotentUnit (curveMatrix w u) (cube_eq_zero hw (isWeightStrict_curveMatrix u hu)))

/-- Pulling back the curve pulls back its coordinate and its weight-strict part. -/
theorem tensorMatrixEquiv_comp_contraction {T' : Over (base k)}
    (a : T' ⟶ T ⊗ AffineLine.scheme (base k)) :
    (MatrixPoints.tensorMatrixEquiv k D b T' (a ≫ contraction hw u hu) :
        Matrix n n (tensorAlgebra k D T')) =
      1 + scale w (includeSections k D T'
          ((a ≫ snd T (AffineLine.scheme (base k))).left.appTop (AffineLine.coord (base k))))
        (((u : Matrix n n (tensorAlgebra k D T)) - 1).map
          (tensorMap k D (a ≫ fst T (AffineLine.scheme (base k))))) := by
  rw [MatrixPoints.tensorMatrixEquiv_naturality, contraction, MulEquiv.apply_symm_apply]
  simp only [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, unipotentUnit_val,
    map_add, map_one, RingHom.mapMatrix_apply, curveMatrix, map_scale, Matrix.map_map]
  congr 2
  funext i j
  exact tensorMap_comp k D _ a _

/-- The curve extends the conjugation orbit of `u` under the weighted cocharacter. -/
theorem contraction_isOrbitExtension :
    Dynamic.IsOrbitExtension (cocharacter k D b w)
      ((MatrixPoints.tensorMatrixEquiv k D b T).symm u) (contraction hw u hu) := by
  apply (MatrixPoints.tensorMatrixEquiv k D b _).injective
  apply Units.ext
  rw [tensorMatrixEquiv_comp_contraction]
  simp only [Dynamic.orbit, map_mul, map_inv, tensorMatrixEquiv_cocharacter]
  rw [MatrixPoints.tensorMatrixEquiv_naturality, MulEquiv.apply_symm_apply, whiskerLeft_snd,
    whiskerLeft_fst, ← AffineLine.homEquiv_apply, AffineLine.homEquiv_comp_unitInclusion]
  rw [Units.val_mul, Units.val_mul]
  have hU := map_contracting (tensorMap k D (fst T (Gm (base k)).X)) hu
  have key := weightMatrix_conj_eq (S := tensorAlgebra k D (T ⊗ (Gm (base k)).X))
    (R := ((algΓ (CommRingCat.of k)).obj (T ⊗ (Gm (base k)).X)).unop) w
    (Gm.pointsEquiv (base k) _ (snd T (Gm (base k)).X)) _ hU
  rw [Matrix.map_sub _ (map_sub _), Matrix.map_one _ (map_zero _) (map_one _)]
  exact key.symm

/-- The curve is the identity at zero. -/
theorem contraction_evalZero : Dynamic.evalZero (contraction (b := b) hw u hu) = 1 := by
  apply (MatrixPoints.tensorMatrixEquiv k D b _).injective
  apply Units.ext
  rw [Dynamic.evalZero, tensorMatrixEquiv_comp_contraction, map_one, Units.val_one, lift_snd,
    ← AffineLine.homEquiv_apply, AffineLine.homEquiv_comp_zeroSection, map_zero,
    scale_zero (isWeightStrict_map _ (isWeightStrict_sub_one hu)), add_zero]

include hw hu in
/-- **Contraction.** Every invertible matrix of contracting shape for `w` over the tensor
coefficient algebra of a test scheme lies in the dynamic unipotent subgroup functor of the
weighted cocharacter. -/
theorem mem_unipotent_of_contracting :
    (MatrixPoints.tensorMatrixEquiv k D b T).symm u ∈
      (Dynamic.unipotent (cocharacter k D b w)).carrier T :=
  ⟨contraction hw u hu, contraction_isOrbitExtension hw u hu, contraction_evalZero hw u hu⟩

end Contraction

end Langlands.GroupScheme.FiniteAlgebraUnits.WeightedRoot
