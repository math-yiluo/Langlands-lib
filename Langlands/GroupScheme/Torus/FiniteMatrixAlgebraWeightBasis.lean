import Langlands.GroupScheme.Torus.FiniteAlgebraWeightIdempotents
import Langlands.GroupScheme.Torus.MatrixIdempotentBasis

/-! # A generating weight basis for a finite matrix algebra torus -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry
open scoped Matrix

namespace Langlands.GroupScheme.FiniteMatrixAlgebraTorusWeights

open FiniteAlgebraUnits FiniteAlgebraTorusWeights SplitTorusRepresentationWeights

variable {K L : Type u} [Field K] [Field L] [Algebra K L]
  {N d : ℕ} {b : Module.Basis (Fin d) K (Matrix (Fin N) (Fin N) L)}
  {I : Type u} [Fintype I] [DecidableEq I]
  (i : splitTorus (Spec (CommRingCat.of K)) I ⟶ groupScheme b)

/-- The columns of the matrix coefficients of the inverse universal torus unit. -/
def weightColumn (q : (I → ℤ) × Fin N) : Fin N → L :=
  MatrixIdempotentBasis.columnFamily (weightElement i) q

/-- There is an L-basis of projector columns whose integral weights generate
all characters, and every projector acts with its indicated weight label. -/
theorem exists_weightBasis (hi : Mono i.hom.hom.left) :
    ∃ (v : Module.Basis (Fin N) L (Fin N → L)) (q : Fin N → (I → ℤ) × Fin N),
      (∀ j, v j = weightColumn i (q j)) ∧
      AddSubgroup.closure (Set.range (fun j => (q j).1)) = ⊤ ∧
      ∀ m j, weightElement i m *ᵥ v j = if m = (q j).1 then v j else 0 := by
  classical
  obtain ⟨v, q, hv, hcover⟩ := MatrixIdempotentBasis.exists_columnBasis_with_labels
    (weightElement i) (weightElement_mul i)
    (weightSupport (rightRegularRepresentation b) I i) (sum_weightElement i)
  refine ⟨v, q, hv, ?_, ?_⟩
  · apply top_unique
    rw [← closure_weightSupport i hi]
    apply AddSubgroup.closure_mono
    intro m hm
    exact hcover m (weightElement_ne_zero i hm)
  · intro m j
    simpa only [hv] using MatrixIdempotentBasis.mulVec_columnFamily
      (weightElement i) (weightElement_mul i) m (q j)

end Langlands.GroupScheme.FiniteMatrixAlgebraTorusWeights
