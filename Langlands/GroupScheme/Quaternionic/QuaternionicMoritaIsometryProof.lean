import Langlands.GroupScheme.Quaternionic.QuaternionicMoritaIsometryStatement
import Langlands.GroupScheme.Quaternionic.SymplecticReductive
import Langlands.GroupScheme.Quaternionic.ScalarInvolution
import Langlands.Algebra.CentralSimpleScalarExtension

/-!
# The quaternionic Morita comparison for isometry groups

Let `D` be a quaternion division algebra over a field `K`, `σ` an involution of the first kind
of `D` with `3`-dimensional symmetric subspace, and `q` a nondegenerate `σ`-quadratic form on
`D^m` in the sense of Tits. This module proves `QuaternionicMoritaIsometryStatement`
(Tits 1968, §3, Prop. 6, isometry part): after base change to an algebraic closure `L` of `K`,
the isometry group scheme `O(q)` becomes isomorphic to the orthogonal group scheme of a
nondegenerate ordinary quadratic form on `L^(2m)`.

The proof works with any field `L` and any splitting chart `e : L ⊗[K] D ≃ₐ[L] M_2(L)`.

* Points of `O(q)` over a `K`-algebra `R` are the units `u` of `R ⊗[K] M_m(D)` with
  `u Q₀ ᵗu^σ - Q₀ ∈ R ⊗ {x - ᵗx^σ}`, for any representative `Q₀` of `q`
  (`FirstKindInvolution.isometryPointsEquiv`).
* Through the chart `Φ : R ⊗[K] M_m(D) ≅ M_{2m}(R)` the conjugate transpose becomes
  `X ↦ S Xᵀ S⁻¹` with `S` symmetric, so this condition becomes `g C gᵀ - C = Y - Yᵀ` for
  `g = Φ(u)` and the split Gram matrix `C = Φ(1 ⊗ Q₀) S` (`MoritaIsometry.isometryUnitsEquiv`),
  which is the isometry condition of the scalar form represented by `C`.
* These identifications are natural in the test scheme, so `isoOfPointModels` gives the
  group-scheme isomorphism (`MoritaIsometry.splitIso`); the polar matrix of `C` is
  `Φ(1 ⊗ (Q₀ + ᵗQ₀^σ)) S`, a unit (`MoritaIsometry.isNondegenerateQuadratic_gramN`).
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Matrix Module
open scoped TensorProduct CategoryTheory.MonObj

namespace Langlands.GroupScheme.Quaternionic

namespace IsometryCut

open FirstKindInvolution

variable {K A : Type u} [Field K] [Ring A] [Algebra K A] [FiniteDimensional K A]
  {τ : FirstKindInvolution K A} {M : Submodule K A}

/-- Coefficient changes preserve `R ⊗ M`. -/
theorem map_mem_baseChange {R S : Type u} [CommRing R] [Algebra K R] [CommRing S] [Algebra K S]
    (φ : R →ₐ[K] S) {y : R ⊗[K] A} (hy : y ∈ M.baseChange R) :
    Algebra.TensorProduct.map φ (AlgHom.id K A) y ∈ M.baseChange S := by
  rw [mem_baseChange_iff] at hy ⊢
  intro j
  rw [coord_map, hy j, _root_.map_zero]

/-- The restriction of isometry subgroups along a change of coefficient algebra. -/
def isometrySubgroupMap (hM : IsStable τ M) (Q : A) {R S : Type u} [CommRing R] [Algebra K R]
    [CommRing S] [Algebra K S] (φ : R →ₐ[K] S) :
    isometrySubgroup hM Q R →* isometrySubgroup hM Q S :=
  ((Units.map (Algebra.TensorProduct.map φ (AlgHom.id K A)).toMonoidHom).comp
    (isometrySubgroup hM Q R).subtype).codRestrict _ fun y => by
    change defect τ Q (Algebra.TensorProduct.map φ (AlgHom.id K A)
      ((y : (R ⊗[K] A)ˣ) : R ⊗[K] A)) ∈ M.baseChange S
    rw [← map_defect]
    exact map_mem_baseChange φ y.2

theorem coe_isometrySubgroupMap (hM : IsStable τ M) (Q : A) {R S : Type u} [CommRing R]
    [Algebra K R] [CommRing S] [Algebra K S] (φ : R →ₐ[K] S) (y : isometrySubgroup hM Q R) :
    (((isometrySubgroupMap hM Q φ y : (S ⊗[K] A)ˣ)) : S ⊗[K] A) =
      Algebra.TensorProduct.map φ (AlgHom.id K A) ((y : (R ⊗[K] A)ˣ) : R ⊗[K] A) :=
  rfl

end IsometryCut

namespace FirstKindInvolution

section Points

variable {F D' : Type u} [Field F] [DivisionRing D'] [Algebra F D'] [FiniteDimensional F D']
  (σ' : FirstKindInvolution F D') {n : Type} [Fintype n] [DecidableEq n]

omit [FiniteDimensional F D'] in
/-- Tits's subspace `{x - ᵗx^σ}` is stable under `y ↦ u y ᵗu^σ`. -/
theorem isStable_quadraticKernel :
    IsometryCut.IsStable (σ'.matrix n) (σ'.quadraticKernel n) :=
  IsometryCut.isStable_alternatingSubspace

/-- The units `u` of `R ⊗[F] M_n(D')` with `u Q ᵗu^σ - Q ∈ R ⊗ {x - ᵗx^σ}`. -/
abbrev isometryUnits (Q : Matrix n n D') (R : Type u) [CommRing R] [Algebra F R] :
    Subgroup (R ⊗[F] Matrix n n D')ˣ :=
  IsometryCut.isometrySubgroup σ'.isStable_quadraticKernel Q R

variable (q : σ'.QuadraticForms n) (Q : Matrix n n D')
  (hQ : (Submodule.Quotient.mk Q : σ'.QuadraticForms n) = q)

/-- A point of `O(q)` gives an isometry unit for any representative `Q` of `q`. -/
def isometryPointsHom (T : Over (Spec (CommRingCat.of F))) :
    (T ⟶ (σ'.isometryGroup q).X) →* σ'.isometryUnits Q ((algΓ (CommRingCat.of F)).obj T).unop :=
  ((FiniteAlgebraUnits.pointsEquiv (Module.finBasis F (Matrix n n D')) T).toMonoidHom.comp
    ((yonedaGrp.map (σ'.isometryGroupι q)).app (Opposite.op T)).hom).codRestrict _ fun x =>
      (σ'.mem_range_isometryGroupι_iff q Q hQ _).1 (SubgroupFunctor.mem_range.2 ⟨x, rfl⟩)

theorem isometryPointsHom_apply (T : Over (Spec (CommRingCat.of F)))
    (x : T ⟶ (σ'.isometryGroup q).X) :
    ((σ'.isometryPointsHom q Q hQ T x : (((algΓ (CommRingCat.of F)).obj T).unop ⊗[F]
        Matrix n n D')ˣ)) =
      FiniteAlgebraUnits.pointsEquiv (Module.finBasis F (Matrix n n D')) T
        (x ≫ (σ'.isometryGroupι q).hom.hom) :=
  rfl

theorem isometryPointsHom_bijective (T : Over (Spec (CommRingCat.of F))) :
    Function.Bijective (σ'.isometryPointsHom q Q hQ T) := by
  constructor
  · intro x y hxy
    have h1 := congrArg Subtype.val hxy
    rw [isometryPointsHom_apply, isometryPointsHom_apply] at h1
    have h2 := (FiniteAlgebraUnits.pointsEquiv _ _).injective h1
    have := (σ'.isClosedSubgroup_isometryGroupι q).mono_overHom
    exact (cancel_mono _).1 h2
  · intro y
    set x0 := (FiniteAlgebraUnits.pointsEquiv (Module.finBasis F (Matrix n n D')) T).symm y
    have hx0 : x0 ∈ (SubgroupFunctor.range (σ'.isometryGroupι q)).carrier T := by
      rw [σ'.mem_range_isometryGroupι_iff q Q hQ, MulEquiv.apply_symm_apply]
      exact y.2
    obtain ⟨z, hz⟩ := SubgroupFunctor.mem_range.1 hx0
    refine ⟨z, Subtype.ext ?_⟩
    rw [isometryPointsHom_apply, hz, MulEquiv.apply_symm_apply]

/-- Points of `O(q)` are the isometry units for any representative `Q` of `q`. -/
def isometryPointsEquiv (T : Over (Spec (CommRingCat.of F))) :
    (T ⟶ (σ'.isometryGroup q).X) ≃* σ'.isometryUnits Q ((algΓ (CommRingCat.of F)).obj T).unop :=
  MulEquiv.ofBijective (σ'.isometryPointsHom q Q hQ T) (σ'.isometryPointsHom_bijective q Q hQ T)

theorem isometryPointsEquiv_apply (T : Over (Spec (CommRingCat.of F)))
    (x : T ⟶ (σ'.isometryGroup q).X) :
    ((σ'.isometryPointsEquiv q Q hQ T x : (((algΓ (CommRingCat.of F)).obj T).unop ⊗[F]
        Matrix n n D')ˣ)) =
      FiniteAlgebraUnits.pointsEquiv (Module.finBasis F (Matrix n n D')) T
        (x ≫ (σ'.isometryGroupι q).hom.hom) :=
  rfl

theorem isometryPointsEquiv_naturality {T T' : Over (Spec (CommRingCat.of F))} (a : T' ⟶ T)
    (x : T ⟶ (σ'.isometryGroup q).X) :
    σ'.isometryPointsEquiv q Q hQ T' (a ≫ x) =
      IsometryCut.isometrySubgroupMap _ Q ((algΓ (CommRingCat.of F)).map a).unop.hom
        (σ'.isometryPointsEquiv q Q hQ T x) := by
  apply Subtype.ext
  rw [isometryPointsEquiv_apply, Category.assoc, FiniteAlgebraUnits.pointsEquiv_naturality]
  rfl

end Points

end FirstKindInvolution

namespace MoritaIsometry

/-! ### Alternating defects in a matrix chart -/

section Abstract

variable {A R : Type*} [Ring A] [CommRing R] {κ : Type*} [Fintype κ] [DecidableEq κ]
  (Φ : A ≃+* Matrix κ κ R) (τ : A → A) (S S' : Matrix κ κ R)

theorem transpose_eq_of_mul_eq_one (hS'S : S' * S = 1) (hS : Sᵀ = S) : S'ᵀ = S' := by
  have h : S * S'ᵀ = 1 := by
    rw [← hS, ← Matrix.transpose_mul, hS'S, Matrix.transpose_one]
  calc S'ᵀ = (S' * S) * S'ᵀ := by rw [hS'S, Matrix.one_mul]
    _ = S' := by rw [Matrix.mul_assoc, h, Matrix.mul_one]

variable {Φ τ S S'}
variable (hΦ : ∀ a, Φ (τ a) = S * (Φ a)ᵀ * S') (hSS' : S * S' = 1) (hS'S : S' * S = 1)
  (hS : Sᵀ = S)

include hΦ hSS' hS'S hS in
/-- If `Φ (τ a) = S Φ(a)ᵀ S⁻¹` with `S` symmetric, then `x` has the form `a - τ a` exactly when
`Φ(x) S` has the form `Y - Yᵀ`. -/
theorem exists_sub_eq_iff (x : A) :
    (∃ a, a - τ a = x) ↔ ∃ Y : Matrix κ κ R, Φ x * S = Y - Yᵀ := by
  constructor
  · rintro ⟨a, rfl⟩
    refine ⟨Φ a * S, ?_⟩
    rw [map_sub, hΦ, Matrix.sub_mul, Matrix.transpose_mul, hS, Matrix.mul_assoc (S * _), hS'S,
      Matrix.mul_one]
  · rintro ⟨Y, hY⟩
    refine ⟨Φ.symm (Y * S'), Φ.injective ?_⟩
    have hS't := transpose_eq_of_mul_eq_one S S' hS'S hS
    have hx : Φ x = (Y - Yᵀ) * S' := by
      rw [← hY, Matrix.mul_assoc, hSS', Matrix.mul_one]
    rw [map_sub, hΦ, RingEquiv.apply_symm_apply, Matrix.transpose_mul, hS't, hx,
      ← Matrix.mul_assoc S S', hSS', Matrix.one_mul, Matrix.sub_mul]

include hΦ hS'S in
/-- The defect `y H τ(y) - H` in the chart: `Φ(y H τ(y) - H) S = g C gᵀ - C` with `g = Φ y` and
`C = Φ(H) S`. -/
theorem map_defect_mul (y H : A) :
    Φ (y * H * τ y - H) * S = Φ y * (Φ H * S) * (Φ y)ᵀ - Φ H * S := by
  rw [map_sub, map_mul, map_mul, hΦ, Matrix.sub_mul]
  simp only [Matrix.mul_assoc]
  rw [hS'S, Matrix.mul_one]

include hΦ hSS' hS'S hS in
/-- The defect `y H τ(y) - H` is alternating exactly when `g C gᵀ - C` is, for `g = Φ y` and
`C = Φ(H) S`. -/
theorem exists_sub_eq_defect_iff (y H : A) :
    (∃ a, a - τ a = y * H * τ y - H) ↔
      ∃ Y : Matrix κ κ R, Φ y * (Φ H * S) * (Φ y)ᵀ - Φ H * S = Y - Yᵀ := by
  rw [exists_sub_eq_iff hΦ hSS' hS'S hS, map_defect_mul hΦ hS'S]

end Abstract

/-- A group isomorphism carrying one subgroup exactly onto another restricts to an isomorphism
of the subgroups. -/
def subgroupEquivOfIff {G G' : Type*} [Group G] [Group G'] (f : G ≃* G') {H : Subgroup G}
    {H' : Subgroup G'} (h : ∀ x, x ∈ H ↔ f x ∈ H') : H ≃* H' where
  toFun x := ⟨f x.1, (h x.1).1 x.2⟩
  invFun y := ⟨f.symm y, (h _).2 (by rw [MulEquiv.apply_symm_apply]; exact y.2)⟩
  left_inv x := Subtype.ext (f.symm_apply_apply x)
  right_inv y := Subtype.ext (f.apply_symm_apply y)
  map_mul' x y := Subtype.ext (map_mul f x.1 y.1)

/-! ### The scalar side -/

section ScalarSide

variable {L : Type u} [Field L] {N : ℕ} (R : Type u) [CommRing R] [Algebra L R]

variable (L N) in
/-- The identification `R ⊗[L] M_N(L) ≅ M_N(R)`. -/
abbrev scalarChart : R ⊗[L] Matrix (Fin N) (Fin N) L ≃ₐ[L] Matrix (Fin N) (Fin N) R :=
  (matrixEquivTensor (Fin N) L R).symm

theorem scalarChart_baseChange (y : R ⊗[L] Matrix (Fin N) (Fin N) L) :
    scalarChart L N R (((FirstKindInvolution.scalar L).matrix (Fin N)).baseChange R y) =
      (scalarChart L N R y)ᵀ := by
  induction y using TensorProduct.inductionOn with
  | tmul r M =>
    rw [FirstKindInvolution.baseChange_tmul, FirstKindInvolution.scalar_matrix_apply,
      matrixEquivTensor_apply_symm, matrixEquivTensor_apply_symm, Matrix.transpose_smul,
      Matrix.transpose_map]
  | add y y' hy hy' =>
    rw [FirstKindInvolution.map_add, _root_.map_add, hy, hy', _root_.map_add,
      Matrix.transpose_add]

variable {R} in
theorem scalarChart_naturality {R' : Type u} [CommRing R'] [Algebra L R'] (f : R →ₐ[L] R')
    (y : R ⊗[L] Matrix (Fin N) (Fin N) L) :
    scalarChart L N R' (Algebra.TensorProduct.map f (AlgHom.id L _) y) =
      (scalarChart L N R y).map f := by
  induction y using TensorProduct.inductionOn with
  | tmul r M =>
    rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, matrixEquivTensor_apply_symm,
      matrixEquivTensor_apply_symm]
    ext i j
    simp
  | add y y' hy hy' =>
    rw [_root_.map_add, _root_.map_add, hy, hy', _root_.map_add, Matrix.map_add _ (map_add f)]

/-- A unit `y` of `R ⊗[L] M_N(L)` is an isometry of the scalar form represented by `C` exactly
when `g C gᵀ - C` has the form `Y - Yᵀ` for its matrix `g`. -/
theorem mem_scalar_isometryUnits_iff (C : Matrix (Fin N) (Fin N) L)
    (y : (R ⊗[L] Matrix (Fin N) (Fin N) L)ˣ) :
    y ∈ (FirstKindInvolution.scalar L).isometryUnits C R ↔
      ∃ Y : Matrix (Fin N) (Fin N) R,
        scalarChart L N R (y : R ⊗[L] Matrix (Fin N) (Fin N) L) * C.map (algebraMap L R) *
            (scalarChart L N R (y : R ⊗[L] Matrix (Fin N) (Fin N) L))ᵀ - C.map (algebraMap L R) =
          Y - Yᵀ := by
  change IsometryCut.defect ((FirstKindInvolution.scalar L).matrix (Fin N)) C
      (y : R ⊗[L] Matrix (Fin N) (Fin N) L) ∈
    ((FirstKindInvolution.scalar L).matrix (Fin N)).alternatingSubspace.baseChange R ↔ _
  rw [IsometryCut.alternatingSubspace_baseChange, Submodule.restrictScalars_mem,
    FirstKindInvolution.mem_alternatingSubspace, IsometryCut.defect,
    exists_sub_eq_defect_iff (Φ := (scalarChart L N R).toRingEquiv)
      (τ := ((FirstKindInvolution.scalar L).matrix (Fin N)).baseChange R) (S := 1) (S' := 1)
      (fun a => by rw [Matrix.one_mul, Matrix.mul_one]; exact scalarChart_baseChange R a)
      (Matrix.mul_one 1) (Matrix.mul_one 1) Matrix.transpose_one]
  change (∃ Y, scalarChart L N R _ * (scalarChart L N R (1 ⊗ₜ[L] C) * 1) * _ -
    scalarChart L N R (1 ⊗ₜ[L] C) * 1 = Y - Yᵀ) ↔ _
  rw [matrixEquivTensor_apply_symm, one_smul, Matrix.mul_one]
  rfl

end ScalarSide

/-! ### The quaternionic side -/

/-- The reindexing `Fin m × Fin 2 ≃ Fin (2 * m)`. -/
def blockIndex (m : ℕ) : Fin m × Fin 2 ≃ Fin (2 * m) :=
  finProdFinEquiv.trans (finCongr (Nat.mul_comm m 2))

section QuaternionicSide

open FirstKindInvolution

variable {K D : Type u} [Field K] [DivisionRing D] [Algebra K D]
  {L : Type u} [Field L] [Algebra K L]
  (e : L ⊗[K] D ≃ₐ[L] Matrix (Fin 2) (Fin 2) L) (σ : FirstKindInvolution K D) (m : ℕ)
  (R : Type u) [CommRing R] [Algebra K R] [Algebra L R] [IsScalarTower K L R]

/-- The matrix chart `R ⊗[K] M_m(D) ≅ M_{2m}(R)`. -/
def chartN : R ⊗[K] Matrix (Fin m) (Fin m) D ≃+* Matrix (Fin (2 * m)) (Fin (2 * m)) R :=
  (matrixChartR e R).trans (Matrix.reindexRingEquiv R (blockIndex m))

theorem chartN_apply (x : R ⊗[K] Matrix (Fin m) (Fin m) D) :
    chartN e m R x = Matrix.reindex (blockIndex m) (blockIndex m) (matrixChartR e R x) :=
  rfl

/-- The reindexed block involution matrix `S`. -/
def invMatrix : Matrix (Fin (2 * m)) (Fin (2 * m)) L :=
  Matrix.reindex (blockIndex m) (blockIndex m) (σ.blockInvolutionMatrix e)

/-- The reindexed inverse block involution matrix `S⁻¹`. -/
def invMatrixInv : Matrix (Fin (2 * m)) (Fin (2 * m)) L :=
  Matrix.reindex (blockIndex m) (blockIndex m) (σ.blockInvolutionMatrixInv e)

theorem invMatrix_mul_inv : invMatrix e σ m * invMatrixInv e σ m = 1 := by
  change Matrix.reindexRingEquiv L (blockIndex m) _ * Matrix.reindexRingEquiv L (blockIndex m) _ = 1
  rw [← _root_.map_mul, blockInvolutionMatrix_mul_inv, _root_.map_one]

theorem invMatrix_inv_mul : invMatrixInv e σ m * invMatrix e σ m = 1 := by
  change Matrix.reindexRingEquiv L (blockIndex m) _ * Matrix.reindexRingEquiv L (blockIndex m) _ = 1
  rw [← _root_.map_mul, blockInvolutionMatrix_inv_mul, _root_.map_one]

theorem transpose_invMatrix [FiniteDimensional K D] (hσ : finrank K σ.symmetricSubspace = 3) :
    (invMatrix e σ m)ᵀ = invMatrix e σ m := by
  rw [invMatrix, Matrix.transpose_reindex, transpose_blockInvolutionMatrix e σ hσ]

/-- The transport of the conjugate-transpose involution: `X ↦ S Xᵀ S⁻¹`. -/
theorem chartN_baseChange (x : R ⊗[K] Matrix (Fin m) (Fin m) D) :
    chartN e m R ((σ.matrix (Fin m)).baseChange R x) =
      (invMatrix e σ m).map (algebraMap L R) * (chartN e m R x)ᵀ *
        (invMatrixInv e σ m).map (algebraMap L R) := by
  change Matrix.reindexRingEquiv R (blockIndex m) (matrixChartR e R _) = _
  rw [matrixChartR_baseChange, _root_.map_mul, _root_.map_mul]
  rfl

theorem chartN_one_tmul (M : Matrix (Fin m) (Fin m) D) :
    chartN e m R (1 ⊗ₜ[K] M) = (chartN e m L (1 ⊗ₜ[K] M)).map (algebraMap L R) := by
  rw [chartN_apply, chartN_apply, matrixChartR_one_tmul]
  rfl

variable {R} in
theorem chartN_naturality {R' : Type u} [CommRing R'] [Algebra K R'] [Algebra L R']
    [IsScalarTower K L R'] (f : R →ₐ[L] R') (x : R ⊗[K] Matrix (Fin m) (Fin m) D) :
    chartN e m R' (Algebra.TensorProduct.map (f.restrictScalars K) (AlgHom.id K _) x) =
      (chartN e m R x).map f := by
  rw [chartN_apply, chartN_apply, matrixChartR_naturality]
  rfl

/-- The Gram matrix `C = Φ(Q₀) S` over `L` of the split form. -/
def gramN (Q₀ : Matrix (Fin m) (Fin m) D) : Matrix (Fin (2 * m)) (Fin (2 * m)) L :=
  chartN e m L (1 ⊗ₜ[K] Q₀) * invMatrix e σ m

/-- A unit `y` of `R ⊗[K] M_m(D)` is an isometry of the form represented by `Q₀` exactly when
`g C gᵀ - C` has the form `Y - Yᵀ`, for `g` its matrix and `C` the split Gram matrix. -/
theorem mem_isometryUnits_iff [FiniteDimensional K D] (hσ : finrank K σ.symmetricSubspace = 3)
    (Q₀ : Matrix (Fin m) (Fin m) D) (y : (R ⊗[K] Matrix (Fin m) (Fin m) D)ˣ) :
    y ∈ σ.isometryUnits Q₀ R ↔
      ∃ Y : Matrix (Fin (2 * m)) (Fin (2 * m)) R,
        chartN e m R y * (gramN e σ m Q₀).map (algebraMap L R) * (chartN e m R y)ᵀ -
            (gramN e σ m Q₀).map (algebraMap L R) = Y - Yᵀ := by
  have hSS' : (invMatrix e σ m).map (algebraMap L R) * (invMatrixInv e σ m).map (algebraMap L R)
      = 1 := by
    rw [← Matrix.map_mul, invMatrix_mul_inv, Matrix.map_one _ (_root_.map_zero _)
      (_root_.map_one _)]
  have hS'S : (invMatrixInv e σ m).map (algebraMap L R) * (invMatrix e σ m).map (algebraMap L R)
      = 1 := by
    rw [← Matrix.map_mul, invMatrix_inv_mul, Matrix.map_one _ (_root_.map_zero _)
      (_root_.map_one _)]
  have hS : ((invMatrix e σ m).map (algebraMap L R))ᵀ = (invMatrix e σ m).map (algebraMap L R) := by
    rw [← Matrix.transpose_map, transpose_invMatrix e σ m hσ]
  change IsometryCut.defect (σ.matrix (Fin m)) Q₀ (y : R ⊗[K] Matrix (Fin m) (Fin m) D) ∈
    (σ.matrix (Fin m)).alternatingSubspace.baseChange R ↔ _
  rw [IsometryCut.alternatingSubspace_baseChange, Submodule.restrictScalars_mem,
    FirstKindInvolution.mem_alternatingSubspace, IsometryCut.defect,
    exists_sub_eq_defect_iff (Φ := chartN e m R) (τ := (σ.matrix (Fin m)).baseChange R)
      (chartN_baseChange e σ m R) hSS' hS'S hS, gramN, Matrix.map_mul, ← chartN_one_tmul]

/-- The composite `R ⊗[K] M_m(D) ≅ M_{2m}(R) ≅ R ⊗[L] M_{2m}(L)`. -/
def theta : R ⊗[K] Matrix (Fin m) (Fin m) D ≃+* R ⊗[L] Matrix (Fin (2 * m)) (Fin (2 * m)) L :=
  (chartN e m R).trans (matrixEquivTensor (Fin (2 * m)) L R).toRingEquiv

theorem scalarChart_theta (x : R ⊗[K] Matrix (Fin m) (Fin m) D) :
    scalarChart L (2 * m) R (theta e m R x) = chartN e m R x :=
  (matrixEquivTensor (Fin (2 * m)) L R).symm_apply_apply _

/-- The isometry units of the form represented by `Q₀` correspond, through `theta`, to the
isometry units of the scalar form represented by the split Gram matrix. -/
def isometryUnitsEquiv [FiniteDimensional K D] (hσ : finrank K σ.symmetricSubspace = 3)
    (Q₀ : Matrix (Fin m) (Fin m) D) :
    σ.isometryUnits Q₀ R ≃* (FirstKindInvolution.scalar L).isometryUnits (gramN e σ m Q₀) R :=
  subgroupEquivOfIff (Units.mapEquiv (theta e m R).toMulEquiv) fun y => by
    rw [mem_isometryUnits_iff e σ m R hσ, mem_scalar_isometryUnits_iff]
    change _ ↔ ∃ Y, scalarChart L (2 * m) R (theta e m R y) * _ *
      (scalarChart L (2 * m) R (theta e m R y))ᵀ - _ = _
    rw [scalarChart_theta]

theorem coe_isometryUnitsEquiv [FiniteDimensional K D] (hσ : finrank K σ.symmetricSubspace = 3)
    (Q₀ : Matrix (Fin m) (Fin m) D) (y : σ.isometryUnits Q₀ R) :
    (((isometryUnitsEquiv e σ m R hσ Q₀ y : (R ⊗[L] Matrix (Fin (2 * m)) (Fin (2 * m)) L)ˣ)) :
        R ⊗[L] Matrix (Fin (2 * m)) (Fin (2 * m)) L) =
      theta e m R ((y : (R ⊗[K] Matrix (Fin m) (Fin m) D)ˣ) : R ⊗[K] Matrix (Fin m) (Fin m) D) :=
  rfl

variable {R} in
theorem isometryUnitsEquiv_naturality [FiniteDimensional K D]
    (hσ : finrank K σ.symmetricSubspace = 3) (Q₀ : Matrix (Fin m) (Fin m) D) {R' : Type u}
    [CommRing R'] [Algebra K R'] [Algebra L R'] [IsScalarTower K L R'] (f : R →ₐ[L] R')
    (y : σ.isometryUnits Q₀ R) :
    isometryUnitsEquiv e σ m R' hσ Q₀
        (IsometryCut.isometrySubgroupMap _ Q₀ (f.restrictScalars K) y) =
      IsometryCut.isometrySubgroupMap _ (gramN e σ m Q₀) f
        (isometryUnitsEquiv e σ m R hσ Q₀ y) := by
  apply Subtype.ext
  apply Units.ext
  rw [coe_isometryUnitsEquiv, IsometryCut.coe_isometrySubgroupMap,
    IsometryCut.coe_isometrySubgroupMap, coe_isometryUnitsEquiv]
  apply (scalarChart L (2 * m) R').injective
  rw [scalarChart_theta, scalarChart_naturality, scalarChart_theta, chartN_naturality]

end QuaternionicSide


/-! ### Assembly of the group-scheme isomorphism -/

section Assembly

attribute [local instance] restrictedSectionsAlgebra restrictedSectionsScalarTower

open FirstKindInvolution

variable {K D : Type u} [Field K] [DivisionRing D] [Algebra K D] [FiniteDimensional K D]
  {L : Type u} [Field L] [Algebra K L]
  (e : L ⊗[K] D ≃ₐ[L] Matrix (Fin 2) (Fin 2) L) (σ : FirstKindInvolution K D) (m : ℕ)
  (hσ : finrank K σ.symmetricSubspace = 3)
  (q : σ.QuadraticForms (Fin m)) (Q₀ : Matrix (Fin m) (Fin m) D)
  (hQ₀ : (Submodule.Quotient.mk Q₀ : σ.QuadraticForms (Fin m)) = q)

/-- The common point model: scalar isometry units of the split Gram matrix over `Γ(T, ⊤)`. -/
abbrev splitModel (T : Over (Spec (CommRingCat.of L))) : Type u :=
  (scalar L).isometryUnits (gramN e σ m Q₀) ((algΓ (CommRingCat.of L)).obj T).unop

/-- Points of the base change of `O(q)` to `L`, read in the split model. -/
def basePointsEquiv (T : Over (Spec (CommRingCat.of L))) :
    (T ⟶ ((GroupScheme.baseChange (scalarBaseMap K L)).obj (σ.isometryGroup q)).X) ≃*
      splitModel e σ m Q₀ T :=
  (GroupScheme.baseChangePointsEquiv (scalarBaseMap K L) (σ.isometryGroup q) T).trans
    ((σ.isometryPointsEquiv q Q₀ hQ₀ ((Over.map (scalarBaseMap K L)).obj T)).trans
      (isometryUnitsEquiv e σ m (restrictedSections K L T) hσ Q₀))

theorem basePointsEquiv_naturality {T T' : Over (Spec (CommRingCat.of L))} (a : T' ⟶ T)
    (x : T ⟶ ((GroupScheme.baseChange (scalarBaseMap K L)).obj (σ.isometryGroup q)).X) :
    basePointsEquiv e σ m hσ q Q₀ hQ₀ T' (a ≫ x) =
      IsometryCut.isometrySubgroupMap _ (gramN e σ m Q₀)
        ((algΓ (CommRingCat.of L)).map a).unop.hom (basePointsEquiv e σ m hσ q Q₀ hQ₀ T x) := by
  let f : restrictedSections K L T →ₐ[L] restrictedSections K L T' :=
    { ((algΓ (CommRingCat.of K)).map ((Over.map (scalarBaseMap K L)).map a)).unop.hom.toRingHom
      with commutes' := fun c => ((algΓ (CommRingCat.of L)).map a).unop.hom.commutes c }
  have h0 := GroupScheme.baseChangePointsEquiv_naturality (scalarBaseMap K L)
    (σ.isometryGroup q) a x
  have h1 := σ.isometryPointsEquiv_naturality q Q₀ hQ₀ ((Over.map (scalarBaseMap K L)).map a)
    (GroupScheme.baseChangePointsEquiv (scalarBaseMap K L) (σ.isometryGroup q) T x)
  have h2 := isometryUnitsEquiv_naturality e σ m hσ Q₀ f
    (σ.isometryPointsEquiv q Q₀ hQ₀ _
      (GroupScheme.baseChangePointsEquiv (scalarBaseMap K L) (σ.isometryGroup q) T x))
  have h3 := congrArg (isometryUnitsEquiv e σ m (restrictedSections K L T') hσ Q₀)
    ((congrArg (σ.isometryPointsEquiv q Q₀ hQ₀ _) h0).trans h1)
  exact h3.trans h2

/-- The base change of `O(q)` to `L` is the orthogonal group of the split Gram matrix. -/
def splitIso :
    (GroupScheme.baseChange (scalarBaseMap K L)).obj (σ.isometryGroup q) ≅
      (scalar L).isometryGroup (Submodule.Quotient.mk (gramN e σ m Q₀)) :=
  isoOfPointModels (splitModel e σ m Q₀)
    (fun a => IsometryCut.isometrySubgroupMap _ (gramN e σ m Q₀)
      ((algΓ (CommRingCat.of L)).map a).unop.hom)
    (basePointsEquiv e σ m hσ q Q₀ hQ₀)
    ((scalar L).isometryPointsEquiv _ (gramN e σ m Q₀) rfl)
    (basePointsEquiv_naturality e σ m hσ q Q₀ hQ₀)
    (fun a y => (scalar L).isometryPointsEquiv_naturality _ (gramN e σ m Q₀) rfl a y)

end Assembly

/-! ### Nondegeneracy of the split form -/

section Nondegenerate

open FirstKindInvolution

variable {K D : Type u} [Field K] [DivisionRing D] [Algebra K D] [FiniteDimensional K D]
  {L : Type u} [Field L] [Algebra K L]
  (e : L ⊗[K] D ≃ₐ[L] Matrix (Fin 2) (Fin 2) L) (σ : FirstKindInvolution K D) (m : ℕ)
  (hσ : finrank K σ.symmetricSubspace = 3)

include hσ in
/-- The polar matrix of the split Gram matrix is `Φ(Q₀ + ᵗQ₀^σ) S`. -/
theorem gramN_add_transpose (Q₀ : Matrix (Fin m) (Fin m) D) :
    gramN e σ m Q₀ + (gramN e σ m Q₀)ᵀ =
      chartN e m L (1 ⊗ₜ[K] (Q₀ + σ.matrix (Fin m) Q₀)) * invMatrix e σ m := by
  have hmap : ∀ M : Matrix (Fin (2 * m)) (Fin (2 * m)) L, M.map (algebraMap L L) = M :=
    fun M => by ext i j; simp
  have h := chartN_baseChange e σ m L (1 ⊗ₜ[K] Q₀)
  rw [baseChange_tmul, hmap, hmap] at h
  rw [TensorProduct.tmul_add, _root_.map_add, Matrix.add_mul, h, gramN, Matrix.transpose_mul,
    transpose_invMatrix e σ m hσ]
  congr 1
  rw [Matrix.mul_assoc, invMatrix_inv_mul, Matrix.mul_one]

include hσ in
/-- The split form is nondegenerate when `q` is. -/
theorem isNondegenerateQuadratic_gramN (q : σ.QuadraticForms (Fin m))
    (Q₀ : Matrix (Fin m) (Fin m) D)
    (hQ₀ : (Submodule.Quotient.mk Q₀ : σ.QuadraticForms (Fin m)) = q)
    (hq : σ.IsNondegenerateQuadratic q) :
    (scalar L).IsNondegenerateQuadratic
      (Submodule.Quotient.mk (gramN e σ m Q₀) : (scalar L).QuadraticForms (Fin (2 * m))) := by
  unfold IsNondegenerateQuadratic at hq ⊢
  rw [scalar_polar_mk, gramN_add_transpose e σ m hσ]
  rw [← hQ₀, polar_mk] at hq
  refine IsUnit.mul ?_ ?_
  · exact (hq.map (Algebra.TensorProduct.includeRight :
      Matrix (Fin m) (Fin m) D →ₐ[K] L ⊗[K] Matrix (Fin m) (Fin m) D)).map (chartN e m L)
  · exact ⟨⟨invMatrix e σ m, invMatrixInv e σ m, invMatrix_mul_inv e σ m,
      invMatrix_inv_mul e σ m⟩, rfl⟩

end Nondegenerate

end MoritaIsometry

open MoritaIsometry in
/-- **Quaternionic Morita comparison for isometry groups** (Tits 1968, §3, Prop. 6). -/
theorem quaternionicMoritaIsometry : QuaternionicMoritaIsometryStatement.{u} := by
  intro K D _ _ _ _ _ hD σ hσ m q hq
  obtain ⟨n, _, ⟨e⟩⟩ := CentralSimple.exists_matrix_chart K D (AlgebraicClosure K)
  have hn : n = 2 := by
    have h := CentralSimple.finrank_eq_matrix_size K D (AlgebraicClosure K) n e
    rw [hD] at h
    exact Nat.mul_self_inj.mp (h.symm.trans rfl)
  subst hn
  have hQ₀ : (Submodule.Quotient.mk (Quotient.out q) : σ.QuadraticForms (Fin m)) = q :=
    Quotient.out_eq q
  exact ⟨_, isNondegenerateQuadratic_gramN e σ m hσ q _ hQ₀ hq,
    ⟨splitIso e σ m hσ q _ hQ₀⟩⟩

end Langlands.GroupScheme.Quaternionic
