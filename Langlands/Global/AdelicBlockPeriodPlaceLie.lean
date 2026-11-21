import Langlands.Automorphic.BlockShapeRealPeriodLie
import Langlands.Global.Factors.CuspidalSupportIdentityEvaluation
import Langlands.Representation.Geometric.WeylUniquenessProof

/-! # Upper triangular place directions in the Lie algebra of a block period -/

noncomputable section

open scoped BigOperators TensorProduct Matrix.Norms.Operator

namespace Langlands.Global.ArchimedeanGL

open Langlands.Automorphic Langlands.GeneralLinear Langlands.Geometric NumberField

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 650000

attribute [local instance 100] LieRing.ofAssociativeRing

universe u

variable (F : Type u) [Field F] {n : ℕ} (B : BlockShape n)

local notation "RP" => {v : InfinitePlace F // InfinitePlace.IsReal v}
local notation "CP" => {v : InfinitePlace F // InfinitePlace.IsComplex v}
local notation "RM" => Matrix (Fin n) (Fin n) ℝ
local notation "CM" => Matrix (Fin n) (Fin n) ℂ
local notation "L" => RealLieAlgebra F

/-- Take the diagonal block of an actual archimedean real Lie direction. -/
def blockShapeRealLieDiagonal (X : L n) (i : Fin B.length) : L (B.size i) :=
  (realLieAlgebraToMatrix F (B.size i)).symm
    ((realLieAlgebraToMatrix F n X).submatrix (B.index i) (B.index i))

private theorem sum_blockInclusion (D : ∀ i, ArchimedeanMatrix F (B.size i)) :
    (∑ i, archimedeanBlockMatrixInclusion F B i (D i)) =
      Matrix.reindex B.indexEquiv B.indexEquiv (Matrix.blockDiagonal' D) := by
  classical
  let blockDiagonal : (∀ i, ArchimedeanMatrix F (B.size i)) →ₗ[ℝ] ArchimedeanMatrix F n :=
    (Matrix.reindexLinearEquiv ℝ (mixedEmbedding.mixedSpace F) B.indexEquiv B.indexEquiv).toLinearMap
      ∘ₗ { toFun := Matrix.blockDiagonal'
           map_add' := Matrix.blockDiagonal'_add
           map_smul' := Matrix.blockDiagonal'_smul }
  change (∑ i, blockDiagonal (Pi.single i (D i))) = blockDiagonal D
  rw [← map_sum, Finset.univ_sum_single]

private theorem blockDiagonal_entry (X : ArchimedeanMatrix F n) (a b : Fin n) :
    Matrix.reindex B.indexEquiv B.indexEquiv
      (Matrix.blockDiagonal' (fun i => X.submatrix (B.index i) (B.index i))) a b =
      if blockIndex B a = blockIndex B b then X a b else 0 := by
  obtain ⟨⟨i, a⟩, rfl⟩ := B.indexEquiv.surjective a
  obtain ⟨⟨j, b⟩, rfl⟩ := B.indexEquiv.surjective b
  change Matrix.blockDiagonal' (fun i => X.submatrix (B.index i) (B.index i))
    (B.indexEquiv.symm (B.indexEquiv ⟨i, a⟩)) (B.indexEquiv.symm (B.indexEquiv ⟨j, b⟩)) = _
  simp only [blockIndex, Equiv.symm_apply_apply]
  by_cases hij : i = j
  · subst j
    rw [Matrix.blockDiagonal'_apply_eq, ite_eq_left rfl]
    rfl
  · simp only [Matrix.blockDiagonal'_apply_ne _ _ _ hij, ite_eq_right hij]

private theorem exists_blockShapeRealLie_upper_split (X : L n)
    (hX : (realLieAlgebraToMatrix F n X).IsUpperTriangular) :
    ∃ U : L n, IsStrictUpperBlockLie F B U ∧
      X = (∑ i, blockShapeRealLieInclusion F B i (blockShapeRealLieDiagonal F B X i)) + U := by
  let D := ∑ i, blockShapeRealLieInclusion F B i (blockShapeRealLieDiagonal F B X i)
  let e := realLieAlgebraToMatrix F n
  have hD : e D = Matrix.reindex B.indexEquiv B.indexEquiv
      (Matrix.blockDiagonal' (fun i => (e X).submatrix (B.index i) (B.index i))) := by
    change realLieAlgebraToMatrix F n (∑ i, blockShapeRealLieInclusion F B i
      (blockShapeRealLieDiagonal F B X i)) = _
    rw [map_sum]
    simp only [blockShapeRealLieInclusion_matrix, blockShapeRealLieDiagonal,
      LinearEquiv.apply_symm_apply]
    exact sum_blockInclusion F B _
  refine ⟨X - D, ?_, (add_sub_cancel D X).symm⟩
  intro a b hab
  change e (X - D) a b = 0
  rw [map_sub, Matrix.sub_apply, hD, blockDiagonal_entry]
  by_cases he : blockIndex B a = blockIndex B b
  · rw [ite_eq_left he, sub_self]
  · have hlt : blockIndex B b < blockIndex B a := lt_of_le_of_ne hab (fun h => he h.symm)
    have hba : b < a := lt_of_not_ge fun hle => (not_le_of_gt hlt) (blockIndex_monotone B hle)
    rw [ite_eq_right he, sub_zero]
    exact hX hba

private theorem blockShapeRealLieDiagonal_realInclusion (v : RP) (X : RM) (i : Fin B.length) :
    blockShapeRealLieDiagonal F B (realPlaceLieInclusion F n v X) i =
      realPlaceLieInclusion F (B.size i) v (X.submatrix (B.index i) (B.index i)) := by
  apply (realLieAlgebraToMatrix F (B.size i)).injective
  rw [blockShapeRealLieDiagonal, LinearEquiv.apply_symm_apply,
    realLieAlgebraToMatrix_realPlaceLieInclusion, realLieAlgebraToMatrix_realPlaceLieInclusion]
  rfl

private theorem blockShapeRealLieDiagonal_complexInclusion (v : CP) (X : CM) (i : Fin B.length) :
    blockShapeRealLieDiagonal F B (complexPlaceLieInclusion F n v X) i =
      complexPlaceLieInclusion F (B.size i) v (X.submatrix (B.index i) (B.index i)) := by
  apply (realLieAlgebraToMatrix F (B.size i)).injective
  rw [blockShapeRealLieDiagonal, LinearEquiv.apply_symm_apply,
    realLieAlgebraToMatrix_complexPlaceLieInclusion, realLieAlgebraToMatrix_complexPlaceLieInclusion]
  rfl

/-- An upper triangular direction at a real place is the sum of the local
Levi directions and a strict upper block direction in the actual global Lie algebra. -/
theorem realPlaceLieInclusion_split_upper_blocks (v : RP) (X : RM) (hX : X.IsUpperTriangular) :
    ∃ U : L n, IsStrictUpperBlockLie F B U ∧
      realPlaceLieInclusion F n v X = (∑ i, blockShapeRealLieInclusion F B i
        (realPlaceLieInclusion F (B.size i) v (X.submatrix (B.index i) (B.index i)))) + U := by
  classical
  have hx : (realLieAlgebraToMatrix F n (realPlaceLieInclusion F n v X)).IsUpperTriangular := by
    rw [realLieAlgebraToMatrix_realPlaceLieInclusion]
    intro a b hb
    change ((Pi.single v (X a b) : RP → ℝ), (0 : CP → ℂ)) = 0
    rw [hX hb, Pi.single_zero]
    rfl
  obtain ⟨U, hU, h⟩ := exists_blockShapeRealLie_upper_split F B _ hx
  exact ⟨U, hU, by simpa only [blockShapeRealLieDiagonal_realInclusion F B] using h⟩

/-- The analogous split at a complex place is real-linear in its complex matrix direction. -/
theorem complexPlaceLieInclusion_split_upper_blocks (v : CP) (X : CM) (hX : X.IsUpperTriangular) :
    ∃ U : L n, IsStrictUpperBlockLie F B U ∧
      complexPlaceLieInclusion F n v X = (∑ i, blockShapeRealLieInclusion F B i
        (complexPlaceLieInclusion F (B.size i) v (X.submatrix (B.index i) (B.index i)))) + U := by
  classical
  have hx : (realLieAlgebraToMatrix F n (complexPlaceLieInclusion F n v X)).IsUpperTriangular := by
    rw [realLieAlgebraToMatrix_complexPlaceLieInclusion]
    intro a b hb
    change ((0 : RP → ℝ), (Pi.single v (X a b) : CP → ℂ)) = 0
    rw [hX hb, Pi.single_zero]
    rfl
  obtain ⟨U, hU, h⟩ := exists_blockShapeRealLie_upper_split F B _ hx
  exact ⟨U, hU, by simpa only [blockShapeRealLieDiagonal_complexInclusion F B] using h⟩

end Langlands.Global.ArchimedeanGL

namespace Langlands.Global

open Langlands.Automorphic Langlands.GeneralLinear ArchimedeanGL FiniteParametrizedBlockInduction

universe u

variable {F : Type u} [Field F] [NumberField F] {n : ℕ} (B : BlockShape n)
  {W : Type u} [AddCommGroup W] [Module ℂ W]
  {V : Fin B.length → Type u} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]

local instance periodPlaceLieRationalGroup : AddCommGroup (RationalInvariantFunctions F n) :=
  Submodule.addCommGroup _
local instance periodPlaceLieContinuousGroup : AddCommGroup (ContinuousRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance periodPlaceLieSmoothGroup : AddCommGroup (FiniteSmoothRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance periodPlaceLieAlgebraRing : Ring (automorphicOperatorAlgebra F n) :=
  Subalgebra.toRing _

attribute [local instance 100] LieRing.ofAssociativeRing

variable (A : automorphicOperatorAlgebra F n →ₐ[ℂ] Module.End ℂ W)

/-- The actual operator of a full archimedean real Lie direction on the source. -/
def periodRealLieOperator : RealLieAlgebra F n →ₗ[ℝ] Module.End ℂ W :=
  (((A.comp (differentialOperator F n)).toLieHom.comp
    (envelopingGenerator F n)).toLinearMap.restrictScalars ℝ).comp (complexify F n).toLinearMap

variable (ev : W →ₗ[ℂ] (⨂[ℂ] (i : Fin B.length), V i))
  (op : ∀ i, RealLieAlgebra F (B.size i) → Module.End ℂ (V i))

local notation "D" => periodRealLieOperator A

private theorem periodEvaluation_upper_lie
    (hU : ∀ X, IsStrictUpperBlockLie F B X → ∀ w, ev (D X w) = 0)
    (hD : ∀ i X w, ev (D (blockShapeRealLieInclusion F B i X) w) =
      PiTensorProduct.map (Function.update (fun _ => LinearMap.id) i (op i X)) (ev w))
    (X : RealLieAlgebra F n) (x : ∀ i, RealLieAlgebra F (B.size i))
    (h : ∃ U : RealLieAlgebra F n, IsStrictUpperBlockLie F B U ∧
      X = (∑ i, blockShapeRealLieInclusion F B i (x i)) + U) (w : W) :
    ev (D X w) = ∑ i, PiTensorProduct.map (Function.update (fun _ => LinearMap.id) i (op i (x i))) (ev w) := by
  obtain ⟨U, hrad, rfl⟩ := h
  rw [map_add, LinearMap.add_apply, map_add, hU U hrad w, add_zero]
  simp only [map_sum, LinearMap.sum_apply, hD]

/-- The global block derivative and radical vanishing give the unnormalized
block Lie equation at any real place. -/
theorem isUnnormalizedBlockLieEvaluation_real_of_period
    (v : {v : NumberField.InfinitePlace F // v.IsReal})
    (hU : ∀ X, IsStrictUpperBlockLie F B X → ∀ w, ev (D X w) = 0)
    (hD : ∀ i X w, ev (D (blockShapeRealLieInclusion F B i X) w) =
      PiTensorProduct.map (Function.update (fun _ => LinearMap.id) i (op i X)) (ev w)) :
    IsUnnormalizedBlockLieEvaluation B (sourceRealPlaceLie A v)
      (fun i X => op i (realPlaceLieInclusion F (B.size i) v X)) ev := by
  intro X hX w
  exact periodEvaluation_upper_lie B A ev op hU hD _ _
    (realPlaceLieInclusion_split_upper_blocks F B v X hX) w

/-- The full real Lie algebra of a complex place obeys the same equation. -/
theorem isUnnormalizedBlockLieEvaluation_complex_of_period
    (v : {v : NumberField.InfinitePlace F // v.IsComplex})
    (hU : ∀ X, IsStrictUpperBlockLie F B X → ∀ w, ev (D X w) = 0)
    (hD : ∀ i X w, ev (D (blockShapeRealLieInclusion F B i X) w) =
      PiTensorProduct.map (Function.update (fun _ => LinearMap.id) i (op i X)) (ev w)) :
    IsUnnormalizedBlockLieEvaluation B (sourceComplexPlaceLie A v)
      (fun i X => op i (complexPlaceLieInclusion F (B.size i) v X)) ev := by
  intro X hX w
  exact periodEvaluation_upper_lie B A ev op hU hD _ _
    (complexPlaceLieInclusion_split_upper_blocks F B v X hX) w

end Langlands.Global
