import Langlands.Global.InfiniteAdelicGroupProduct
import Langlands.GroupScheme.AffineLinearEmbeddingProof
import Langlands.GroupScheme.AffinePointClosedImmersion
import Langlands.GroupScheme.GeneralLinearPointTopology

/-! # Closed matrix realizations of actual infinite-place points -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Topology
open scoped CategoryTheory.MonObj Matrix

namespace Langlands.GroupScheme.MatrixRepresentation

variable {R : CommRingCat.{u}} {G : GroupScheme (Spec R)}
  {n : Type} [Fintype n] [DecidableEq n]
  (ρ : MatrixRepresentation G n) (A : CommAlgCat.{u} R) [TopologicalSpace A]

/-- An algebraic coefficient representation is continuous on actual affine points. -/
theorem continuous_affineMatrix : Continuous (ρ.affineMatrix A) := by
  exact (GeneralLinear.continuous_affinePointsEquiv n R A).comp
    (G.continuous_affinePointsTarget A ρ)

/-- The actual coefficient representation as a continuous group homomorphism. -/
def affineMatrixContinuous : G.affinePoints A →ₜ* GL n A where
  toMonoidHom := ρ.affineMatrix A
  continuous_toFun := ρ.continuous_affineMatrix A

@[simp] theorem affineMatrixContinuous_apply (x : G.affinePoints A) :
    ρ.affineMatrixContinuous A x = ρ.affineMatrix A x := rfl

/-- A scheme-theoretic closed linear embedding gives a closed embedding on
actual coefficient points with the regular-function evaluation topology. -/
theorem isClosedEmbedding_affineMatrix [IsAffine G.X.left]
    [IsTopologicalRing A] [T2Space A] (hρ : IsClosedSubgroup ρ) :
    IsClosedEmbedding (ρ.affineMatrix A) := by
  have : IsClosedImmersion ρ.hom.hom.left := hρ
  exact (GeneralLinear.affinePointsHomeomorph n R A).isClosedEmbedding.comp
    (isClosedEmbedding_affinePointsTarget G (GeneralLinear.groupScheme n R) A ρ)

end Langlands.GroupScheme.MatrixRepresentation

namespace Langlands.Global.InfinitePlaceGroupPoints

variable {F : Type u} [Field F]
  (G : GroupScheme (Spec (CommRingCat.of F)))

/-- The actual completion-point coefficient map, with its existing topology. -/
def matrixHom {n : Type} [Fintype n] [DecidableEq n]
    (ρ : Langlands.GroupScheme.MatrixRepresentation G n)
    (v : NumberField.InfinitePlace F) :
    InfinitePlaceGroupPoints F G v →ₜ* GL n v.Completion :=
  ρ.affineMatrixContinuous (CommAlgCat.of F v.Completion)

@[simp] theorem matrixHom_apply {n : Type} [Fintype n] [DecidableEq n]
    (ρ : Langlands.GroupScheme.MatrixRepresentation G n)
    (v : NumberField.InfinitePlace F) (x : InfinitePlaceGroupPoints F G v) :
    matrixHom G ρ v x = ρ.affineMatrix (CommAlgCat.of F v.Completion) x := rfl

/-- Affineness and finite type construct one algebraic representation that is a
faithful closed topological realization at every infinite place. -/
theorem exists_closedMatrixRealization_of_finiteType
    (hAff : IsAffineHom G.X.hom) (hLFT : LocallyOfFiniteType G.X.hom) :
    ∃ (N : ℕ) (ρ : Langlands.GroupScheme.MatrixRepresentation G (Fin N)),
      Langlands.GroupScheme.IsClosedSubgroup ρ ∧
      ∀ v : NumberField.InfinitePlace F, IsClosedEmbedding (matrixHom G ρ v) := by
  obtain ⟨N, ρ, hρ⟩ :=
    Langlands.GroupScheme.affineLinearEmbeddingStatement F G hAff hLFT
  have : IsAffineHom G.X.hom := hAff
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  exact ⟨N, ρ, hρ, fun v =>
    ρ.isClosedEmbedding_affineMatrix (CommAlgCat.of F v.Completion) hρ⟩

/-- Every actual connected reductive group in the Iwasawa target has a faithful
closed matrix realization on its actual completion points, without extra inputs. -/
theorem exists_closedMatrixRealization
    (hG : Langlands.GroupScheme.IsConnectedReductive G) :
    ∃ (N : ℕ) (ρ : Langlands.GroupScheme.MatrixRepresentation G (Fin N)),
      Langlands.GroupScheme.IsClosedSubgroup ρ ∧
      ∀ v : NumberField.InfinitePlace F, IsClosedEmbedding (matrixHom G ρ v) := by
  have : Smooth G.X.hom := hG.smooth
  exact exists_closedMatrixRealization_of_finiteType G hG.isAffineHom inferInstance

end Langlands.Global.InfinitePlaceGroupPoints
