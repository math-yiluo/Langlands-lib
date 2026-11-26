import Langlands.Global.AdelicGroupProduct
import Langlands.Global.RepresentationGrowth
import Langlands.GroupScheme.AffinePointClosedImmersion
import Langlands.GroupScheme.AffineLinearEmbeddingCorepresentedProof
import Langlands.Representation.CompactRepresentativeWeights
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
import Mathlib.Data.Matrix.Block
import Mathlib.Topology.Instances.Matrix

/-! # Dense finite left-translation weights on archimedean compact subgroups

A compact subgroup `C` of `G(𝔸)` contained in the archimedean factor `G(F_∞)` has a faithful
continuous finite-dimensional complex representation: compose a closed linear embedding
`G → GL_N` with the complex embeddings `F_v → ℂ` of the archimedean completions. By the
Stone–Weierstrass theorem (`Langlands.CompactRepresentativeWeights.dense_finiteWeights`),
the continuous functions on `C` with finite-dimensional left-translation orbit are uniformly
dense in `C(C, ℂ)`. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField
open scoped CategoryTheory.MonObj Classical

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Langlands.Global.AdelicGroupPoints

open Langlands.GroupScheme

variable (F : Type u) [Field F] [NumberField F]

/-- The complex coordinate of an infinite adele at an archimedean place `v`, through the
embedding `F_v → ℂ` of the completion. -/
def placeRingHom (v : InfinitePlace F) : InfiniteAdeleRing F →+* ℂ :=
  (InfinitePlace.Completion.extensionEmbedding v).comp
    (Pi.evalRingHom (fun w : InfinitePlace F => w.Completion) v)

theorem continuous_placeRingHom (v : InfinitePlace F) : Continuous (placeRingHom F v) :=
  (InfinitePlace.Completion.isometry_extensionEmbedding v).continuous.comp (continuous_apply v)

/-- Matrices over the infinite adeles as block-diagonal complex matrices, one block for each
archimedean place. -/
def placeMatrixRingHom (N : ℕ) :
    Matrix (Fin N) (Fin N) (InfiniteAdeleRing F) →+*
      Matrix (Fin N × InfinitePlace F) (Fin N × InfinitePlace F) ℂ :=
  (Matrix.blockDiagonalRingHom (Fin N) (InfinitePlace F) ℂ).comp
    (RingHom.pi fun v => (placeRingHom F v).mapMatrix)

theorem placeMatrixRingHom_apply (N : ℕ) (X : Matrix (Fin N) (Fin N) (InfiniteAdeleRing F)) :
    placeMatrixRingHom F N X = Matrix.blockDiagonal fun v => X.map (placeRingHom F v) := rfl

theorem placeMatrixRingHom_injective (N : ℕ) : Function.Injective (placeMatrixRingHom F N) := by
  intro X Y hXY
  apply Matrix.ext
  intro i j
  funext v
  have h := congrFun (congrFun hXY (i, v)) (j, v)
  rw [placeMatrixRingHom_apply, placeMatrixRingHom_apply, Matrix.blockDiagonal_apply_eq,
    Matrix.blockDiagonal_apply_eq, Matrix.map_apply, Matrix.map_apply] at h
  exact (InfinitePlace.Completion.extensionEmbedding v).injective h

variable (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
  {N : ℕ} (rho : MatrixRepresentation G (Fin N))

theorem infiniteMatrix_injective [IsClosedImmersion rho.hom.hom.left] :
    Function.Injective (RepresentationGrowth.infiniteMatrix F G rho) := by
  let : IsAffine (GeneralLinear.groupScheme (Fin N) (CommRingCat.of F)).X.left :=
    GeneralLinear.isAffine_groupScheme (Fin N) (CommRingCat.of F)
  exact (GeneralLinearGroupPoints.infiniteHomeomorph F N).injective.comp
    (G.isEmbedding_affinePointsTarget _ (CommAlgCat.of F (InfiniteAdeleRing F)) rho).injective

/-- The representation of a subgroup `C` of `G(𝔸)` on `ℂ^(N × places)` obtained from the
archimedean component, the matrix representation `rho` and the place embeddings. -/
def archimedeanMatrixRepresentation (C : Subgroup (AdelicGroupPoints F G)) :
    Representation ℂ C (Fin N × InfinitePlace F → ℂ) :=
  (Matrix.toLinAlgEquiv' : Matrix (Fin N × InfinitePlace F) (Fin N × InfinitePlace F) ℂ ≃ₐ[ℂ]
      _).toAlgHom.toRingHom.toMonoidHom.comp
    ((placeMatrixRingHom F N).toMonoidHom.comp
      ((Units.coeHom _).comp
        ((RepresentationGrowth.infiniteMatrix F G rho).toMonoidHom.comp
          ((infinite F G).toMonoidHom.comp C.subtype))))

theorem archimedeanMatrixRepresentation_apply (C : Subgroup (AdelicGroupPoints F G)) (c : C)
    (w : Fin N × InfinitePlace F → ℂ) :
    archimedeanMatrixRepresentation F G rho C c w =
      (placeMatrixRingHom F N
        (RepresentationGrowth.infiniteMatrix F G rho (infinite F G c) :
          Matrix (Fin N) (Fin N) (InfiniteAdeleRing F))).mulVec w := rfl

theorem continuous_archimedeanMatrixRepresentation (C : Subgroup (AdelicGroupPoints F G))
    (w : Fin N × InfinitePlace F → ℂ) :
    Continuous fun c : C => archimedeanMatrixRepresentation F G rho C c w := by
  simp only [archimedeanMatrixRepresentation_apply, placeMatrixRingHom_apply]
  apply Continuous.matrix_mulVec _ continuous_const
  apply Continuous.matrix_blockDiagonal
  apply continuous_pi
  intro v
  apply Continuous.matrix_map _ (continuous_placeRingHom F v)
  exact Units.continuous_val.comp ((RepresentationGrowth.infiniteMatrix F G rho).continuous.comp
    ((infinite F G).continuous.comp continuous_subtype_val))

theorem archimedeanMatrixRepresentation_injective [IsClosedImmersion rho.hom.hom.left]
    (C : Subgroup (AdelicGroupPoints F G)) (hC : ∀ c ∈ C, finite F G c = 1) :
    Function.Injective (archimedeanMatrixRepresentation F G rho C) := by
  intro c d hcd
  have h1 : placeMatrixRingHom F N
        (RepresentationGrowth.infiniteMatrix F G rho (infinite F G c) :
          Matrix (Fin N) (Fin N) (InfiniteAdeleRing F)) =
      placeMatrixRingHom F N
        (RepresentationGrowth.infiniteMatrix F G rho (infinite F G d) :
          Matrix (Fin N) (Fin N) (InfiniteAdeleRing F)) :=
    (Matrix.toLinAlgEquiv' : Matrix (Fin N × InfinitePlace F) (Fin N × InfinitePlace F) ℂ ≃ₐ[ℂ]
      _).injective hcd
  have h3 := infiniteMatrix_injective F G rho (Units.ext (placeMatrixRingHom_injective F N h1))
  apply Subtype.ext
  rw [← pair_projections F G (c : AdelicGroupPoints F G),
    ← pair_projections F G (d : AdelicGroupPoints F G), h3, hC c c.2, hC d d.2]

variable [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]

/-- On a compact subgroup of `G(𝔸)` contained in the archimedean factor, the continuous
functions with finite-dimensional left-translation orbit are uniformly dense. -/
theorem dense_archimedean_finiteWeights (C : Subgroup (AdelicGroupPoints F G)) [CompactSpace C]
    (hC : ∀ c ∈ C, finite F G c = 1) :
    Dense (Langlands.CompactRepresentativeWeights.finiteWeights (K := C) : Set C(C, ℂ)) := by
  obtain ⟨N, rho, hrho⟩ := affineLinearEmbeddingStatement_viaCorepresented F G
    (inferInstance : IsAffineHom G.X.hom) (inferInstance : LocallyOfFiniteType G.X.hom)
  let : IsClosedImmersion rho.hom.hom.left := hrho
  exact Langlands.CompactRepresentativeWeights.dense_finiteWeights
    (archimedeanMatrixRepresentation F G rho C) (continuous_archimedeanMatrixRepresentation F G rho C)
    (archimedeanMatrixRepresentation_injective F G rho C hC)

end Langlands.Global.AdelicGroupPoints
