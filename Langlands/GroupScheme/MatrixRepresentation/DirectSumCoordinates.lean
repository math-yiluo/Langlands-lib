import Langlands.GroupScheme.MatrixRepresentation.SemisimpleDirectSum
import Langlands.GroupScheme.MatrixRepresentation.IntertwinerTransport
import Mathlib.LinearAlgebra.DFinsupp

/-! # Matrices out of finite direct sums -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped Matrix CategoryTheory.MonObj

namespace Langlands.GroupScheme.MatrixRepresentation

section Matrices

variable {R : CommRingCat.{u}} {I : Type} [Fintype I] [DecidableEq I]
  {n : I → Type} [∀ i, Fintype (n i)] [∀ i, DecidableEq (n i)]
  {m l : Type} [Fintype m] [Fintype l]

/-- Concatenate a finite family of matrices with a common target. -/
def directSumMap (C : ∀ i, Matrix m (n i) R) : Matrix m (Σ i, n i) R :=
  fun a b => C b.1 a b.2

omit [Fintype I] [DecidableEq I] [∀ i, Fintype (n i)]
  [∀ i, DecidableEq (n i)] [Fintype m] in
/-- Concatenation commutes with mapping the coefficients. -/
theorem directSumMap_map {A : CommRingCat.{u}} (f : R →+* A)
    (C : ∀ i, Matrix m (n i) R) :
    (directSumMap C).map f = directSumMap (fun i => (C i).map f) := rfl

omit [DecidableEq I] [∀ i, DecidableEq (n i)] [Fintype m] in
/-- The concatenated matrix sums the component images. -/
theorem directSumMap_mulVec (C : ∀ i, Matrix m (n i) R)
    (v : (Σ i, n i) → R) :
    directSumMap C *ᵥ v = ∑ i, C i *ᵥ (fun a => v ⟨i, a⟩) := by
  funext a
  simp only [Matrix.mulVec, dotProduct, directSumMap, ← Finset.univ_sigma_univ,
    Finset.sum_sigma, Finset.sum_apply]

omit [Fintype m] in
/-- A concatenated matrix restricts to the chosen component matrix. -/
theorem directSumMap_mulVec_inclusion (C : ∀ i, Matrix m (n i) R)
    (i : I) (v : n i → R) :
    directSumMap C *ᵥ (directSumInclusion (R := R) i *ᵥ v) = C i *ᵥ v := by
  rw [directSumMap_mulVec, directSumInclusion_mulVec, Fintype.sum_eq_single i]
  · simp only [Sigma.uncurry, Pi.single_eq_same]
  · intro j hj
    simp only [Sigma.uncurry, Pi.single_eq_of_ne hj, Pi.zero_apply]
    change C j *ᵥ 0 = 0
    exact Matrix.mulVec_zero _

/-- The range of a concatenated matrix is the supremum of the component ranges. -/
theorem range_directSumMap (C : ∀ i, Matrix m (n i) R) :
    LinearMap.range (directSumMap C).mulVecLin =
      ⨆ i, LinearMap.range (C i).mulVecLin := by
  apply le_antisymm
  · rintro v ⟨w, rfl⟩
    change directSumMap C *ᵥ w ∈ _
    rw [directSumMap_mulVec]
    apply Submodule.sum_mem
    intro i hi
    exact (le_iSup (fun i => LinearMap.range (C i).mulVecLin) i) ⟨_, rfl⟩
  · apply iSup_le
    intro i
    rintro v ⟨w, rfl⟩
    refine ⟨directSumInclusion (R := R) i *ᵥ w, ?_⟩
    exact directSumMap_mulVec_inclusion C i w

omit [∀ i, DecidableEq (n i)] [Fintype m] in
/-- A block diagonal action on the source acts separately on the concatenated blocks. -/
theorem directSumMap_mul_blockDiagonal (C : ∀ i, Matrix m (n i) R)
    (M : ∀ i, Matrix (n i) (n i) R) :
    directSumMap C * Matrix.blockDiagonal' M =
      directSumMap (fun i => C i * M i) := by
  ext a ⟨i, b⟩
  simp only [Matrix.mul_apply, directSumMap, ← Finset.univ_sigma_univ,
    Finset.sum_sigma]
  rw [Fintype.sum_eq_single i]
  · simp only [Matrix.blockDiagonal'_apply_eq]
  · intro j hj
    apply Finset.sum_eq_zero
    intro c hc
    rw [Matrix.blockDiagonal'_apply_ne _ _ _ hj, mul_zero]

omit [Fintype I] [DecidableEq I] [∀ i, Fintype (n i)]
  [∀ i, DecidableEq (n i)] [Fintype l] in
/-- Left multiplication acts on each concatenated block. -/
theorem mul_directSumMap (D : Matrix l m R) (C : ∀ i, Matrix m (n i) R) :
    D * directSumMap C = directSumMap (fun i => D * C i) := by
  ext a ⟨i, b⟩
  rfl

end Matrices

section Field

variable {k : Type u} [Field k] {I : Type} [Fintype I] [DecidableEq I]
  {n : I → Type} [∀ i, Fintype (n i)] [∀ i, DecidableEq (n i)]
  {m : Type} [Fintype m]

omit [DecidableEq I] [∀ i, DecidableEq (n i)] [Fintype m] in
/-- Independent component ranges and injective component maps give an injective sum. -/
theorem directSumMap_injective (C : ∀ i, Matrix m (n i) k)
    (hi : ∀ i, Function.Injective (C i).mulVecLin)
    (hind : iSupIndep (fun i => LinearMap.range (C i).mulVecLin)) :
    Function.Injective (directSumMap (R := CommRingCat.of k) C).mulVecLin := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro v hv
  have hsum : ∑ i, C i *ᵥ (fun a => v ⟨i, a⟩) = 0 := by
    rw [← directSumMap_mulVec (R := CommRingCat.of k)]
    exact hv
  have hzero := (iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero _).mp hind
    Finset.univ (fun i => C i *ᵥ (fun a => v ⟨i, a⟩))
    (fun i hi => ⟨_, rfl⟩) hsum
  funext ⟨i, a⟩
  have hvzero : (fun a => v ⟨i, a⟩) = 0 :=
    hi i ((hzero i (Finset.mem_univ i)).trans (map_zero _).symm)
  exact congrFun hvzero a

/-- Spanning component ranges give a surjective concatenated matrix. -/
theorem directSumMap_surjective (C : ∀ i, Matrix m (n i) k)
    (hspan : (⨆ i, LinearMap.range (C i).mulVecLin) = ⊤) :
    Function.Surjective (directSumMap (R := CommRingCat.of k) C).mulVecLin := by
  apply LinearMap.range_eq_top.mp
  rw [range_directSumMap]
  exact hspan

end Field

section Representations

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))}
  {I : Type} [Fintype I] [DecidableEq I] {n : I → Type}
  [∀ i, Fintype (n i)] [∀ i, DecidableEq (n i)]
  {m : Type} [Fintype m] [DecidableEq m]
  {ρ : ∀ i, MatrixRepresentation G (n i)} {σ : MatrixRepresentation G m}

/-- A finite family of actual intertwiners induces an intertwiner from the direct sum. -/
theorem intertwines_directSumMap (C : ∀ i, Matrix m (n i) k)
    (hC : ∀ i, (ρ i).Intertwines σ (C i)) :
    (directSum ρ).Intertwines σ (directSumMap (R := CommRingCat.of k) C) := by
  intro A x
  rw [directSum_affineMatrix_val,
    directSumMap_map (R := CommRingCat.of k) (A := CommRingCat.of A),
    directSumMap_mul_blockDiagonal, mul_directSumMap (R := CommRingCat.of A)]
  congr 1
  funext i
  exact hC i A x

end Representations

section BaseChange

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  {G : GroupScheme (Spec (CommRingCat.of k))}
  {I : Type} [Fintype I] [DecidableEq I] {n : I → Type}
  [∀ i, Fintype (n i)] [∀ i, DecidableEq (n i)]
  (ρ : ∀ i, MatrixRepresentation G (n i))

/-- The extended direct sum has the block diagonal affine matrices of the extended factors. -/
theorem directSum_baseChange_affineMatrix_val
    (A : CommAlgCat.{u} (CommRingCat.of K))
    (x : (algSpec (CommRingCat.of K)).obj (op A) ⟶
      ((GroupScheme.baseChange (algebraBaseMap k K)).obj G).X) :
    (((directSum ρ).baseChange (algebraBaseMap k K)).affineMatrix A x :
      Matrix (Σ i, n i) (Σ i, n i) A) =
      Matrix.blockDiagonal' fun i =>
        (((ρ i).baseChange (algebraBaseMap k K)).affineMatrix A x :
          Matrix (n i) (n i) A) := by
  let : Algebra k A := ((algebraMap K A).comp (algebraMap k K)).toAlgebra
  let : IsScalarTower k K A := IsScalarTower.of_algebraMap_eq' rfl
  rw [affineMatrix_baseChange_fintype, directSum_affineMatrix_val]
  congr 1
  funext i
  exact (affineMatrix_baseChange_fintype (ρ i) A x).symm

/-- The identity matrix identifies the sum of the extended factors with the extended sum. -/
theorem intertwines_directSum_baseChange :
    (directSum (fun i => (ρ i).baseChange (algebraBaseMap k K))).Intertwines
      ((directSum ρ).baseChange (algebraBaseMap k K)) 1 := by
  intro A x
  rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul, Matrix.mul_one,
    directSum_affineMatrix_val, directSum_baseChange_affineMatrix_val]

end BaseChange

end Langlands.GroupScheme.MatrixRepresentation
