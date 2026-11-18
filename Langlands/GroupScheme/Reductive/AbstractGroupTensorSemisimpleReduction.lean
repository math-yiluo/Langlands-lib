import Langlands.GroupScheme.MatrixRepresentation.DenseRationalSemisimplicity
import Langlands.GroupScheme.Reductive.AbstractGroupTensorSemisimpleStatement
import Langlands.GroupScheme.Reductive.SemisimpleRepresentationIdentityComponentStatement

/-! # Conditional reduction from abstract groups to algebraic envelopes -/

noncomputable section

universe u v w₁ w₂

open CategoryTheory AlgebraicGeometry
open scoped Matrix CategoryTheory.MonObj

namespace Langlands.GroupScheme.AbstractGroupTensorReduction

open MatrixRepresentation

variable {k : Type u} [Field k] {G : Type v} [Group G]

/-- The invertible matrices of a representation in finite coordinates. -/
def matrixHom {n : Type} [Fintype n] [DecidableEq n]
    (r : Representation k G (n → k)) : G →* Matrix.GeneralLinearGroup n k :=
  Matrix.GeneralLinearGroup.toLin.symm.toMonoidHom.comp r.asGroupHom

@[simp]
theorem matrixHom_val {n : Type} [Fintype n] [DecidableEq n]
    (r : Representation k G (n → k)) (g : G) :
    (matrixHom r g : Matrix n n k) = LinearMap.toMatrix' (r g) := rfl

/-- The simultaneous algebraic envelope needed for two finite coordinate actions. -/
def HasFiniteCoordinateEnvelopes (k : Type u) [Field k] (G : Type v) [Group G] : Prop :=
  ∀ (n m : ℕ) (r : G →* Matrix.GeneralLinearGroup (Fin n) k)
    (s : G →* Matrix.GeneralLinearGroup (Fin m) k),
    ∃ (H : GroupScheme (Spec (CommRingCat.of k)))
      (_ : IsReduced H.X.left) (_ : IsAffineHom H.X.hom)
      (_ : LocallyOfFiniteType H.X.hom)
      (p : MatrixRepresentation H (Fin n)) (q : MatrixRepresentation H (Fin m))
      (α : G →* Langlands.AlgebraicGeometry.PointTopology.RationalPoint k H.X),
      Langlands.AlgebraicGeometry.PointTopology.HasDenseRationalPointFamily α ∧
        (∀ g, p.rationalMatrix (α g) = r g) ∧
        (∀ g, q.rationalMatrix (α g) = s g)

/-- Equality of the invertible matrices identifies the restricted rational action. -/
theorem rationalAction_comp_eq_of_matrix
    {H : GroupScheme (Spec (CommRingCat.of k))}
    {n : Type} [Fintype n] [DecidableEq n]
    (p : MatrixRepresentation H n)
    (α : G →* Langlands.AlgebraicGeometry.PointTopology.RationalPoint k H.X)
    (r : Representation k G (n → k))
    (h : ∀ g, p.rationalMatrix (α g) = matrixHom r g) :
    p.rationalAction.comp α = r := by
  apply MonoidHom.ext
  intro g
  apply LinearMap.toMatrix'.injective
  change LinearMap.toMatrix' (p.rationalAction (α g)) = LinearMap.toMatrix' (r g)
  rw [rationalAction_toMatrix, h, matrixHom_val]

/-- The algebraic tensor assertion gives semisimplicity on every supplied dense
reduced affine envelope. The sibling assertion is an explicit premise. -/
theorem coordinate_tensor_semisimple_of_dense_envelope
    [CharZero k]
    (h : CharZeroSemisimpleRepresentationIdentityComponentStatement.{u})
    {H : GroupScheme (Spec (CommRingCat.of k))}
    [IsReduced H.X.left] [IsAffineHom H.X.hom] [LocallyOfFiniteType H.X.hom]
    {n m : ℕ}
    (p : MatrixRepresentation H (Fin n)) (q : MatrixRepresentation H (Fin m))
    (α : G →* Langlands.AlgebraicGeometry.PointTopology.RationalPoint k H.X)
    (hα : Langlands.AlgebraicGeometry.PointTopology.HasDenseRationalPointFamily α)
    (hp : Representation.IsSemisimpleRepresentation (p.rationalAction.comp α))
    (hq : Representation.IsSemisimpleRepresentation (q.rationalAction.comp α)) :
    (CoordinateTensor.representation
      (p.rationalAction.comp α) (q.rationalAction.comp α)).IsSemisimpleRepresentation := by
  have hp' := (isSemisimpleOnTests_iff_denseRationalAction p α hα).mpr hp
  have hq' := (isSemisimpleOnTests_iff_denseRationalAction q α hα).mpr hq
  have ht : (p.tensor q).IsSemisimpleOnTests := (h k H).2 n m p q hp' hq'
  have ht' := (isSemisimpleOnTests_iff_denseRationalAction (p.tensor q) α hα).mp ht
  rwa [rationalAction_tensor_comp] at ht'

/-- A fieldwise simultaneous-envelope construction and the algebraic tensor
assertion imply the exact abstract-group statement in four independent universes. -/
theorem abstractGroupTensorSemisimple_of_envelopes
    (h : CharZeroSemisimpleRepresentationIdentityComponentStatement.{u})
    (henv : ∀ (k : Type u) [Field k] [CharZero k] (G : Type v) [Group G],
      HasFiniteCoordinateEnvelopes k G) :
    CharZeroAbstractGroupTensorSemisimpleStatement.{u, v, w₁, w₂} := by
  intro k _ _ G _ V _ _ _ W _ _ _ r s hr hs
  apply Langlands.RepresentationSemisimpleTransport.tensor_semisimple_of_coordinates
    (k := k) (G := G) ?_ r s hr hs
  intro n m r s hr hs
  obtain ⟨H, hred, haff, hft, p, q, α, hα, hp, hq⟩ :=
    henv k G n m (matrixHom r) (matrixHom s)
  let := hred
  let := haff
  let := hft
  have hpr := rationalAction_comp_eq_of_matrix p α r hp
  have hqs := rationalAction_comp_eq_of_matrix q α s hq
  rw [← hpr] at hr
  rw [← hqs] at hs
  rw [← hpr, ← hqs]
  exact coordinate_tensor_semisimple_of_dense_envelope h p q α hα hr hs

end Langlands.GroupScheme.AbstractGroupTensorReduction
