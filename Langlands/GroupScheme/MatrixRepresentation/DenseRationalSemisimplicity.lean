import Langlands.GroupScheme.Reductive.AbstractGroupSemisimpleTransport
import Langlands.GroupScheme.Reductive.CharZeroSemisimplicity.TangentStability
import Langlands.GroupScheme.MatrixRepresentationTensor

/-! # Semisimplicity detected on a dense rational-point family -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped Matrix Kronecker CategoryTheory.MonObj

namespace Langlands.GroupScheme.MatrixRepresentation

variable {k : Type u} [Field k] {I : Type v}
  {J : GroupScheme (Spec (CommRingCat.of k))}
  {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-- Semisimplicity as the sum of simple subspaces invariant on every affine test. -/
def IsSemisimpleOnTests (ρ : MatrixRepresentation J n) : Prop :=
  sSup {W : Submodule k (n → k) | ρ.IsStableSubspace W ∧ W ≠ ⊥ ∧
    ∀ U : Submodule k (n → k), ρ.IsStableSubspace U → U ≤ W → U = ⊥ ∨ U = W} = ⊤

section Density

variable [Monoid I] [IsReduced J.X.left] [IsAffineHom J.X.hom]

/-- All-test stability is exactly stability under the given dense monoid family. -/
theorem isStableSubspace_iff_denseRationalAction (ρ : MatrixRepresentation J n)
    (α : I →* Langlands.AlgebraicGeometry.PointTopology.RationalPoint k J.X)
    (hα : Langlands.AlgebraicGeometry.PointTopology.HasDenseRationalPointFamily α)
    (W : Submodule k (n → k)) :
    ρ.IsStableSubspace W ↔
      Langlands.RepresentationSemisimpleTransport.IsStable (ρ.rationalAction.comp α) W := by
  constructor
  · intro h i _ hv
    exact h.rationalMatrix_mulVec_mem (α i) hv
  · exact isStableSubspace_of_denseRationalFamily ρ α hα W

/-- A dense monoid family detects the sum-of-simple-subspaces definition of
semisimplicity, with no algebraic-closedness or characteristic assumption. -/
theorem isSemisimpleOnTests_iff_denseRationalAction (ρ : MatrixRepresentation J n)
    (α : I →* Langlands.AlgebraicGeometry.PointTopology.RationalPoint k J.X)
    (hα : Langlands.AlgebraicGeometry.PointTopology.HasDenseRationalPointFamily α) :
    ρ.IsSemisimpleOnTests ↔
      Representation.IsSemisimpleRepresentation (ρ.rationalAction.comp α) := by
  rw [Langlands.RepresentationSemisimpleTransport.isSemisimple_iff_sSup_simples]
  unfold IsSemisimpleOnTests Langlands.RepresentationSemisimpleTransport.IsSimple
  simp_rw [isStableSubspace_iff_denseRationalAction ρ α hα]

end Density

/-- The ordinary matrix of the rational-point linear action is its rational matrix. -/
@[simp]
theorem rationalAction_toMatrix (ρ : MatrixRepresentation J n)
    (g : Langlands.AlgebraicGeometry.PointTopology.RationalPoint k J.X) :
    LinearMap.toMatrix' (ρ.rationalAction g) = (ρ.rationalMatrix g : Matrix n n k) :=
  LinearMap.toMatrix'_toLin' _

/-- Evaluating the actual tensor representation on rational points gives the
full tensor representation in the published product coordinates. -/
theorem rationalAction_tensor (ρ : MatrixRepresentation J n) (σ : MatrixRepresentation J m) :
    (ρ.tensor σ).rationalAction =
      CoordinateTensor.representation ρ.rationalAction σ.rationalAction := by
  apply MonoidHom.ext
  intro g
  apply LinearMap.ext
  intro x
  change ((ρ.tensor σ).rationalMatrix g : Matrix (n × m) (n × m) k) *ᵥ x = _
  rw [CoordinateTensor.representation_matrix,
    rationalAction_toMatrix, rationalAction_toMatrix]
  congr 1
  ext ⟨i, j⟩ ⟨r, s⟩
  change (Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom
      ((ρ.tensor σ).pointMatrix _ g (i, j) (r, s)) =
    (Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom (ρ.pointMatrix _ g i r) *
      (Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom (σ.pointMatrix _ g j s)
  rw [tensor_pointMatrix_entry, map_mul]

/-- Tensor evaluation commutes with restriction to any monoid family of rational points. -/
theorem rationalAction_tensor_comp [Monoid I]
    (ρ : MatrixRepresentation J n) (σ : MatrixRepresentation J m)
    (α : I →* Langlands.AlgebraicGeometry.PointTopology.RationalPoint k J.X) :
    (ρ.tensor σ).rationalAction.comp α =
      CoordinateTensor.representation (ρ.rationalAction.comp α) (σ.rationalAction.comp α) := by
  rw [rationalAction_tensor]
  rfl

end Langlands.GroupScheme.MatrixRepresentation
