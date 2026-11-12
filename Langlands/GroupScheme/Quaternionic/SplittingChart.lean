import Langlands.GroupScheme.Quaternionic.Involution
import Langlands.Algebra.ReducedNormEvaluation
import Langlands.Algebra.MatrixAlgEquivInnerProof
import Mathlib.LinearAlgebra.Matrix.Transvection
import Mathlib.RingTheory.MatrixAlgebra

/-! # Splitting a quaternion algebra with an involution of the first kind

Let `D` be an algebra over a field `K` with an involution of the first kind `σ`, and let
`e : L ⊗[K] D ≃ₐ[L] M₂(L)` be a matrix chart over a field extension `L`. This module

* extends the chart to every commutative `L`-algebra `R` as a ring isomorphism
  `chartR e R : R ⊗[K] D ≃+* M₂(R)` (`chartR_tmul`, `chartR_naturality`);
* finds, by the Skolem–Noether theorem, an invertible matrix `S` with
  `e (σ_L y) = S (e y)ᵀ S⁻¹` (`involutionMatrix`), so that the same formula holds over every
  `R` (`chartR_baseChange`);
* proves that `S` is symmetric when the symmetric elements of `σ` form a `3`-dimensional space
  (`involutionMatrix_transpose`). In characteristic not two this condition says that `σ` is
  orthogonal; in characteristic two `S` is always symmetric, and the dimension condition does
  not determine the type of `σ`.
-/

noncomputable section

universe u

open scoped TensorProduct
open Matrix Module

namespace Langlands.GroupScheme.Quaternionic

namespace FirstKindInvolution

variable {K D : Type u} [Field K] [Ring D] [Algebra K D]
  {L : Type u} [Field L] [Algebra K L]
  (e : L ⊗[K] D ≃ₐ[L] Matrix (Fin 2) (Fin 2) L)

section Chart

variable (R : Type u) [CommRing R] [Algebra K R] [Algebra L R] [IsScalarTower K L R]

/-- The splitting map agrees with the composite of the cancellation of the base change, the
chart, and the matrix–tensor comparison. -/
theorem splittingMap_eq_comp (x : R ⊗[K] D) :
    ReducedNorm.splittingMap e R x =
      (matrixEquivTensor (Fin 2) L R).symm
        (e.toLinearEquiv.lTensor R
          ((TensorProduct.AlgebraTensorModule.cancelBaseChange K L R R D).symm x)) := by
  induction x using TensorProduct.inductionOn with
  | tmul r d =>
    rw [ReducedNorm.splittingMap_tmul,
      TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul, LinearEquiv.lTensor_tmul,
      AlgEquiv.toLinearEquiv_apply, matrixEquivTensor_apply_symm]
  | add x y hx hy => rw [_root_.map_add, hx, hy, _root_.map_add, _root_.map_add, _root_.map_add]

theorem bijective_splittingMap : Function.Bijective (ReducedNorm.splittingMap e R) := by
  have h : ⇑(ReducedNorm.splittingMap e R) =
      (matrixEquivTensor (Fin 2) L R).symm ∘ (e.toLinearEquiv.lTensor R) ∘
        (TensorProduct.AlgebraTensorModule.cancelBaseChange K L R R D).symm := by
    funext x
    exact splittingMap_eq_comp e R x
  rw [h]
  exact (matrixEquivTensor (Fin 2) L R).symm.bijective.comp
    ((e.toLinearEquiv.lTensor R).bijective.comp
      (TensorProduct.AlgebraTensorModule.cancelBaseChange K L R R D).symm.bijective)

/-- The chart extended to a commutative `L`-algebra `R`: `R ⊗[K] D ≅ M₂(R)`. -/
def chartR : R ⊗[K] D ≃+* Matrix (Fin 2) (Fin 2) R :=
  RingEquiv.ofBijective (ReducedNorm.splittingMap e R).toRingHom (bijective_splittingMap e R)

theorem chartR_apply (x : R ⊗[K] D) : chartR e R x = ReducedNorm.splittingMap e R x := rfl

@[simp] theorem chartR_tmul (r : R) (d : D) :
    chartR e R (r ⊗ₜ[K] d) = r • (e (1 ⊗ₜ[K] d)).map (algebraMap L R) :=
  ReducedNorm.splittingMap_tmul e R r d

variable {R} in
/-- The extended chart commutes with every coefficient change of `L`-algebras. -/
theorem chartR_naturality {R' : Type u} [CommRing R'] [Algebra K R'] [Algebra L R']
    [IsScalarTower K L R'] (f : R →ₐ[L] R') (x : R ⊗[K] D) :
    chartR e R' (Algebra.TensorProduct.map (f.restrictScalars K) (AlgHom.id K D) x) =
      (chartR e R x).map f := by
  induction x using TensorProduct.inductionOn with
  | tmul r d =>
    rw [Algebra.TensorProduct.map_tmul, chartR_tmul, chartR_tmul]
    ext i j
    simp [Matrix.map_apply, AlgHom.restrictScalars_apply]
  | add x y hx hy =>
    rw [_root_.map_add, _root_.map_add, hx, hy, _root_.map_add,
      Matrix.map_add _ (_root_.map_add f)]

end Chart

section Involution

variable (σ : FirstKindInvolution K D)

/-- The automorphism `X ↦ (e (σ_L (e⁻¹ X)))ᵀ` of `M₂(L)`. -/
def transposedInvolution : Matrix (Fin 2) (Fin 2) L ≃ₐ[L] Matrix (Fin 2) (Fin 2) L where
  toFun X := (e (σ.baseChange L (e.symm X)))ᵀ
  invFun X := e (σ.baseChange L (e.symm Xᵀ))
  left_inv X := by simp
  right_inv X := by simp
  map_mul' X Y := by simp [Matrix.transpose_mul]
  map_add' X Y := by simp
  commutes' c := by
    rw [AlgEquiv.commutes, map_algebraMap, AlgEquiv.commutes, Matrix.algebraMap_eq_diagonal,
      Matrix.diagonal_transpose]

theorem exists_involutionMatrix :
    ∃ S : (Matrix (Fin 2) (Fin 2) L)ˣ, ∀ y : L ⊗[K] D,
      e (σ.baseChange L y) = (S : Matrix (Fin 2) (Fin 2) L) * (e y)ᵀ *
        ((S⁻¹ : (Matrix (Fin 2) (Fin 2) L)ˣ) : Matrix (Fin 2) (Fin 2) L) := by
  obtain ⟨U, hU⟩ := MatrixAlgebra.exists_unit_conj_of_algEquiv (transposedInvolution e σ)
  let S : (Matrix (Fin 2) (Fin 2) L)ˣ :=
    { val := ((U⁻¹ : (Matrix (Fin 2) (Fin 2) L)ˣ) : Matrix (Fin 2) (Fin 2) L)ᵀ
      inv := (U : Matrix (Fin 2) (Fin 2) L)ᵀ
      val_inv := by rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one]
      inv_val := by rw [← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one] }
  refine ⟨S, fun y => ?_⟩
  have h := congrArg Matrix.transpose (hU (e y))
  simp only [transposedInvolution, AlgEquiv.coe_mk, Equiv.coe_fn_mk, AlgEquiv.symm_apply_apply,
    Matrix.transpose_transpose, Matrix.transpose_mul] at h
  rw [h, Matrix.mul_assoc]
  rfl

/-- An invertible matrix `S` with `e (σ_L y) = S (e y)ᵀ S⁻¹`. -/
def involutionMatrix : (Matrix (Fin 2) (Fin 2) L)ˣ :=
  (exists_involutionMatrix e σ).choose

theorem chart_baseChange (y : L ⊗[K] D) :
    e (σ.baseChange L y) = (σ.involutionMatrix e : Matrix (Fin 2) (Fin 2) L) * (e y)ᵀ *
      (((σ.involutionMatrix e)⁻¹ : (Matrix (Fin 2) (Fin 2) L)ˣ) : Matrix (Fin 2) (Fin 2) L) :=
  (exists_involutionMatrix e σ).choose_spec y

/-- The transport of `σ` holds over every commutative `L`-algebra. -/
theorem chartR_baseChange (R : Type u) [CommRing R] [Algebra K R] [Algebra L R]
    [IsScalarTower K L R] (y : R ⊗[K] D) :
    chartR e R (σ.baseChange R y) =
      (σ.involutionMatrix e : Matrix (Fin 2) (Fin 2) L).map (algebraMap L R) * (chartR e R y)ᵀ *
        (((σ.involutionMatrix e)⁻¹ : (Matrix (Fin 2) (Fin 2) L)ˣ) :
          Matrix (Fin 2) (Fin 2) L).map (algebraMap L R) := by
  induction y using TensorProduct.inductionOn with
  | tmul r d =>
    have h := chart_baseChange e σ (1 ⊗ₜ[K] d)
    rw [baseChange_tmul] at h
    rw [baseChange_tmul, chartR_tmul, chartR_tmul, h, Matrix.transpose_smul,
      Matrix.mul_smul, Matrix.smul_mul, Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map]
  | add x y hx hy =>
    rw [FirstKindInvolution.map_add, _root_.map_add, hx, hy, _root_.map_add,
      Matrix.transpose_add, Matrix.mul_add, Matrix.add_mul]

/-- `S` is symmetric or antisymmetric: `Sᵀ = c S` with `c² = 1`. -/
theorem exists_transpose_involutionMatrix_eq_smul :
    ∃ c : L, (σ.involutionMatrix e : Matrix (Fin 2) (Fin 2) L)ᵀ =
      c • (σ.involutionMatrix e : Matrix (Fin 2) (Fin 2) L) ∧ c * c = 1 := by
  set S : Matrix (Fin 2) (Fin 2) L := ↑(σ.involutionMatrix e) with hSdef
  set S' : Matrix (Fin 2) (Fin 2) L := ↑(σ.involutionMatrix e)⁻¹ with hS'def
  have hSS' : S * S' = 1 := Units.mul_inv _
  have hS'S : S' * S = 1 := Units.inv_mul _
  have hcomm : ∀ X : Matrix (Fin 2) (Fin 2) L, X * (S * S'ᵀ) = (S * S'ᵀ) * X := by
    intro X
    have h := chart_baseChange e σ (σ.baseChange L (e.symm X))
    rw [apply_apply, AlgEquiv.apply_symm_apply, chart_baseChange, AlgEquiv.apply_symm_apply,
      Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose] at h
    calc X * (S * S'ᵀ) = S * (S'ᵀ * (X * Sᵀ)) * S' * (S * S'ᵀ) := by
          conv_lhs => rw [h]
      _ = S * S'ᵀ * X * (Sᵀ * (S' * S) * S'ᵀ) := by simp only [Matrix.mul_assoc]
      _ = S * S'ᵀ * X := by
          rw [hS'S, Matrix.mul_one, ← Matrix.transpose_mul, hS'S, Matrix.transpose_one,
            Matrix.mul_one]
  have hW : S * S'ᵀ ∈ Set.center (Matrix (Fin 2) (Fin 2) L) :=
    Semigroup.mem_center_iff.2 hcomm
  rw [Matrix.center_eq_range] at hW
  obtain ⟨c, hc⟩ := hW
  have hS : S = c • Sᵀ := by
    calc S = S * S'ᵀ * Sᵀ := by
          rw [Matrix.mul_assoc, ← Matrix.transpose_mul, hSS', Matrix.transpose_one,
            Matrix.mul_one]
      _ = c • Sᵀ := by rw [← hc, Matrix.scalar_apply, ← Matrix.smul_eq_diagonal_mul]
  have hST : Sᵀ = c • S := by
    have h := congrArg Matrix.transpose hS
    rwa [Matrix.transpose_smul, Matrix.transpose_transpose] at h
  refine ⟨c, hST, ?_⟩
  have h2 : (c * c) • S = S := by
    conv_rhs => rw [hS, hST]
    rw [smul_smul]
  have h3 := congrArg (fun M => M * S') h2
  simp only [Matrix.smul_mul, hSS'] at h3
  simpa using congrFun (congrFun h3 0) 0

/-- Antisymmetric `2 × 2` matrices over a field of characteristic not two are multiples of
`!![0, 1; -1, 0]`. -/
theorem eq_smul_of_transpose_eq_neg {M : Matrix (Fin 2) (Fin 2) L} (h2 : (2 : L) ≠ 0)
    (hM : Mᵀ = -M) : M = M 0 1 • !![0, 1; -1, 0] := by
  have hent : ∀ i j, M j i = -M i j := fun i j => by
    simpa using congrFun (congrFun hM i) j
  have hdiag : ∀ i, M i i = 0 := fun i => by
    have h := hent i i
    have h' : (2 : L) * M i i = 0 := by linear_combination h
    exact (mul_eq_zero.1 h').resolve_left h2
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hdiag, hent 0 1]

/-- If the symmetric elements of `σ` form a `3`-dimensional space, then `S` is symmetric. -/
theorem involutionMatrix_transpose [FiniteDimensional K D]
    (hσ : finrank K σ.symmetricSubspace = 3) :
    (σ.involutionMatrix e : Matrix (Fin 2) (Fin 2) L)ᵀ = σ.involutionMatrix e := by
  obtain ⟨c, hc, hcc⟩ := exists_transpose_involutionMatrix_eq_smul e σ
  have hc' : c = 1 ∨ c = -1 := by
    have h : (c - 1) * (c + 1) = 0 := by linear_combination hcc
    rcases mul_eq_zero.1 h with h | h
    · left
      linear_combination h
    · right
      linear_combination h
  rcases hc' with rfl | rfl
  · rw [hc, one_smul]
  by_cases h2 : (2 : L) = 0
  · have h : (-1 : L) = 1 := by linear_combination -h2
    rw [hc, h, one_smul]
  exfalso
  set S : Matrix (Fin 2) (Fin 2) L := ↑(σ.involutionMatrix e) with hSdef
  set S' : Matrix (Fin 2) (Fin 2) L := ↑(σ.involutionMatrix e)⁻¹ with hS'def
  have hSS' : S * S' = 1 := Units.mul_inv _
  have hS'S : S' * S = 1 := Units.inv_mul _
  let ι : L ⊗[K] σ.symmetricSubspace →ₗ[L] L ⊗[K] D :=
    σ.symmetricSubspace.subtype.baseChange L
  let Ψ : L ⊗[K] σ.symmetricSubspace →ₗ[L] Matrix (Fin 2) (Fin 2) L :=
    LinearMap.mulRight L S ∘ₗ e.toLinearEquiv.toLinearMap ∘ₗ ι
  have hι : Function.Injective ι := by
    change Function.Injective (σ.symmetricSubspace.subtype.baseChange L)
    rw [LinearMap.baseChange_eq_ltensor]
    exact Module.Flat.lTensor_preserves_injective_linearMap _ (Submodule.injective_subtype _)
  have hΨ : Function.Injective Ψ := by
    intro z z' h
    apply hι
    apply e.injective
    have h' := congrArg (fun M => M * S') h
    simpa [Ψ, Matrix.mul_assoc, hSS'] using h'
  have hsym : ∀ z, σ.baseChange L (ι z) = ι z := by
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul c s =>
      simp only [ι, LinearMap.baseChange_tmul, Submodule.coe_subtype, baseChange_tmul]
      rw [(mem_symmetricSubspace σ).1 s.2]
    | add z z' hz hz' => rw [_root_.map_add, FirstKindInvolution.map_add, hz, hz']
  set A₀ : Matrix (Fin 2) (Fin 2) L := !![0, 1; -1, 0]
  have hmem : ∀ z, Ψ z ∈ Submodule.span L {A₀} := by
    intro z
    have hz := chart_baseChange e σ (ι z)
    rw [hsym] at hz
    have hzS : e (ι z) * S = S * (e (ι z))ᵀ := by
      conv_lhs => rw [hz]
      rw [Matrix.mul_assoc, hS'S, Matrix.mul_one]
    have hT : (e (ι z) * S)ᵀ = -(e (ι z) * S) := by
      rw [Matrix.transpose_mul, hc, hzS, neg_one_smul, Matrix.neg_mul]
    rw [Submodule.mem_span_singleton]
    exact ⟨_, (eq_smul_of_transpose_eq_neg h2 hT).symm⟩
  have hle := LinearMap.finrank_le_finrank_of_injective
    (f := Ψ.codRestrict (Submodule.span L {A₀}) hmem)
    (fun z z' h => hΨ (congrArg Subtype.val h))
  rw [Module.finrank_baseChange, hσ] at hle
  have hspan : finrank L (Submodule.span L {A₀}) ≤ 1 := by
    have := finrank_span_le_card (R := L) ({A₀} : Set (Matrix (Fin 2) (Fin 2) L))
    simpa using this
  omega

end Involution

end FirstKindInvolution

end Langlands.GroupScheme.Quaternionic
