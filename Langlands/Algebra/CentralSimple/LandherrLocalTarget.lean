import Langlands.Algebra.CentralSimple.LandherrNonsplitLocal
import Langlands.Algebra.CentralSimple.LandherrSquareRoot
import Langlands.Algebra.CentralSimple.LandherrCancellation
import Mathlib.LinearAlgebra.Matrix.StdBasis
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.Instances.Matrix
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic

/-! # Local targets in `2 × 2` matrices over a completed algebra -/

noncomputable section

namespace Langlands.CentralSimple.Landherr

open Langlands.GroupScheme.Quaternionic Langlands.GroupScheme.SU3Root Langlands.BinaryElementary
open scoped TensorProduct

universe u

section Comparison

variable (F : Type u) [Field F] (B : Type u) [Ring B] [Algebra F B] [FiniteDimensional F B]
  (k : Type u) [Field k] [Algebra F k]

/-- Entrywise scalar extension `M₂(B) → M₂(k ⊗ B)`. -/
def matrixBaseMap : Matrix (Fin 2) (Fin 2) B →ₐ[F] Matrix (Fin 2) (Fin 2) (k ⊗[F] B) :=
  (Algebra.TensorProduct.includeRight : B →ₐ[F] k ⊗[F] B).mapMatrix

omit [FiniteDimensional F B] in
@[simp] theorem matrixBaseMap_apply (Z : Matrix (Fin 2) (Fin 2) B) :
    matrixBaseMap F B k Z = Z.map (fun b => (1 : k) ⊗ₜ[F] b) := rfl

/-- The comparison `k ⊗ M₂(B) → M₂(k ⊗ B)`. -/
def matrixTensorMap :
    k ⊗[F] Matrix (Fin 2) (Fin 2) B →ₐ[k] Matrix (Fin 2) (Fin 2) (k ⊗[F] B) :=
  Algebra.TensorProduct.lift (Algebra.ofId k _) (matrixBaseMap F B k)
    (fun c x => Algebra.commute_algebraMap_left c (matrixBaseMap F B k x))

@[simp] theorem matrixTensorMap_tmul (c : k) (Z : Matrix (Fin 2) (Fin 2) B) :
    matrixTensorMap F B k (c ⊗ₜ Z) = algebraMap k _ c * matrixBaseMap F B k Z := by
  rfl

theorem matrixTensorMap_surjective : Function.Surjective (matrixTensorMap F B k) := by
  classical
  rw [← AlgHom.range_eq_top, eq_top_iff]
  intro Z _
  rw [Matrix.matrix_eq_sum_single Z]
  refine Subalgebra.sum_mem _ fun i _ => Subalgebra.sum_mem _ fun j _ => ?_
  induction Z i j using TensorProduct.induction_on with
  | zero => rw [Matrix.single_zero]; exact Subalgebra.zero_mem _
  | tmul c b =>
    refine ⟨c ⊗ₜ Matrix.single i j b, ?_⟩
    change matrixTensorMap F B k _ = _
    rw [matrixTensorMap_tmul, matrixBaseMap_apply, ← Algebra.smul_def]
    ext a b'
    simp only [Matrix.smul_apply, Matrix.map_apply, Matrix.single_apply]
    split_ifs with h
    · rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    · rw [TensorProduct.tmul_zero, smul_zero]
  | add x y hx hy => rw [Matrix.single_add]; exact Subalgebra.add_mem _ hx hy

theorem matrixTensorMap_bijective : Function.Bijective (matrixTensorMap F B k) := by
  refine ⟨?_, matrixTensorMap_surjective F B k⟩
  have hdim : Module.finrank k (k ⊗[F] Matrix (Fin 2) (Fin 2) B) =
      Module.finrank k (Matrix (Fin 2) (Fin 2) (k ⊗[F] B)) := by
    rw [Module.finrank_baseChange, Module.finrank_matrix, Module.finrank_matrix,
      Module.finrank_baseChange]
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (f := (matrixTensorMap F B k).toLinearMap) hdim).mpr (matrixTensorMap_surjective F B k)

/-- The comparison restricted to `k ⊗ K` for a subalgebra `K ≤ M₂(B)` is injective. -/
theorem matrixTensorMap_comp_injective (K : Subalgebra F (Matrix (Fin 2) (Fin 2) B)) :
    Function.Injective ((matrixTensorMap F B k).comp
      (Algebra.TensorProduct.map (AlgHom.id k k) K.val)) := by
  refine (matrixTensorMap_bijective F B k).1.comp ?_
  exact Module.Flat.lTensor_preserves_injective_linearMap (M := k) (K.val.toLinearMap)
    Subtype.val_injective

/-- **Square roots descend to `k ⊗ K`.** If the image of `y' ∈ K` in `M₂(k ⊗ B)` is the square of
an element of the `k`-subalgebra it generates, then `1 ⊗ y'` is a square in `k ⊗ K`. -/
theorem exists_mul_self_eq_tmul (K : Subalgebra F (Matrix (Fin 2) (Fin 2) B)) (z : K)
    (h : ∃ σ ∈ Algebra.adjoin k {matrixBaseMap F B k z},
      σ * σ = matrixBaseMap F B k z) :
    ∃ s : k ⊗[F] K, s * s = 1 ⊗ₜ z := by
  obtain ⟨σ, hσ, hσσ⟩ := h
  set Ψ := (matrixTensorMap F B k).comp (Algebra.TensorProduct.map (AlgHom.id k k) K.val)
  have hΨz : Ψ (1 ⊗ₜ z) = matrixBaseMap F B k z := by
    simp [Ψ]
  have hle : Algebra.adjoin k {matrixBaseMap F B k z} ≤ Ψ.range := by
    rw [Algebra.adjoin_le_iff, Set.singleton_subset_iff]
    exact ⟨1 ⊗ₜ z, hΨz⟩
  obtain ⟨s, hs⟩ := hle hσ
  change Ψ s = σ at hs
  refine ⟨s, matrixTensorMap_comp_injective F B k K ?_⟩
  change Ψ (s * s) = Ψ (1 ⊗ₜ z)
  rw [map_mul, hs, hσσ, hΨz]

end Comparison

section Target

variable (F E : Type u) [Field F] [Field E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [Algebra.IsSeparable F E] [CharZero F]
  (B : Type u) [Ring B] [Algebra E B] [Algebra F B] [IsScalarTower F E B]
  [FiniteDimensional E B] [Algebra.IsCentral E B] [IsSimpleRing B]
  (τ : FirstKindInvolution F B)
  (hτ : ∀ e : E, τ (algebraMap E B e) = algebraMap E B (conjugation F E e))

include hτ in
/-- Let `τ` act on `E` by quadratic conjugation and let `k` be a field over `F` with the
unitary splitting property and with `skewSq F E` nonsquare in `k`.
If `y` is a unit of relative reduced norm one over `k`
and `1 ⊗ y = x τ_k(x)` for a unit `x` of `k ⊗_F B`, some elementary product `t` over
`k ⊗_F B` satisfies `t diag(1 ⊗ y, 1) τ_k(t)ᵗ = 1`. -/
theorem exists_target_list (k : Type u) [Field k] [Algebra F k]
    [Fact (¬ IsSquare (algebraMap F k (skewSq F E)))] (hS : UnitaryInvolutionSplitting k)
    (y : Bˣ) (x : (k ⊗[F] B)ˣ) (hx : (1 : k) ⊗ₜ[F] (y : B) = x * τ.baseChange k x)
    (hy : relNorm F E B k ((1 : k) ⊗ₜ[F] (y : B)) = 1) :
    ∃ l : List ((k ⊗[F] B) × (k ⊗[F] B)),
      (listProd l : Matrix (Fin 2) (Fin 2) (k ⊗[F] B)) *
          (Matrix.of ![![(1 : k) ⊗ₜ[F] (y : B), 0], ![0, 1]]) *
        (τ.baseChange k).matrix (Fin 2) (listProd l : Matrix (Fin 2) (Fin 2) (k ⊗[F] B)) = 1 := by
  let yk : (k ⊗[F] B)ˣ :=
    Units.map (Algebra.TensorProduct.includeRight : B →ₐ[F] k ⊗[F] B).toMonoidHom y
  have hyk : (yk : k ⊗[F] B) = (1 : k) ⊗ₜ[F] (y : B) := rfl
  obtain ⟨w, hw, -, hwc⟩ := exists_commutator_solution F E B k τ hτ hS yk x
    (by rw [hyk]; exact hx) (by rw [hyk]; exact hy)
  obtain ⟨l, hl⟩ := exists_listProd_of_mem (diagonal_mem_of_mem_commutator (inv_mem hwc))
  refine ⟨l, ?_⟩
  rw [← hl, val_diagonal, matrix_fin_two, Units.val_one, FirstKindInvolution.map_one,
    FirstKindInvolution.map_zero, ← hyk, hw]
  have h1 : τ.baseChange k (w : k ⊗[F] B) *
      τ.baseChange k ((w⁻¹ : (k ⊗[F] B)ˣ) : k ⊗[F] B) = 1 := by
    rw [← FirstKindInvolution.map_mul, Units.inv_mul, FirstKindInvolution.map_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, h1]

end Target

end Langlands.CentralSimple.Landherr
