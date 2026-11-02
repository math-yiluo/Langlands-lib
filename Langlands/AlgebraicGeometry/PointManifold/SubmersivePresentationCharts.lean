import Langlands.AlgebraicGeometry.PointManifold.PolynomialFibreCharts
import Langlands.AlgebraicGeometry.PointManifold.PresentationPoints
import Langlands.AlgebraicGeometry.PointManifold.RegularCharts
import Mathlib.RingTheory.Smooth.StandardSmooth

/-! # Regular charts from submersive algebra presentations -/

noncomputable section

open CategoryTheory
open _root_.AlgebraicGeometry
open scoped ContDiff Classical

namespace Langlands.AlgebraicGeometry.PointManifold

open MvPolynomial PointTopology

variable {k : Type} [RCLike k]
variable {X : Over (Spec (CommRingCat.of k))} [IsAffine X.left]
variable {d : ℕ} {σ : Type*} [Fintype σ]

/-- The dependent Jacobian of a split submersive presentation is nonsingular
at every solution of its equations. -/
theorem submersivePresentation_jacobian_ne_zero
    (P : Algebra.SubmersivePresentation k (AffineCoordinateRing k X) (Fin d ⊕ σ) σ)
    (hmap : ∀ j, P.map j = Sum.inr j)
    (x : (Fin d ⊕ σ) → k) (hx : polynomialRelations P.relation x = 0) :
    (polynomialRelationJacobian P.relation x).det ≠ 0 := by
  let q := presentationSolutionPoint P.toPresentation ⟨x, hx⟩
  have hmat : polynomialRelationJacobian P.relation x =
      ((eval x).mapMatrix P.jacobiMatrix).transpose := by
    ext i j
    simp [polynomialRelationJacobian, Algebra.PreSubmersivePresentation.jacobiMatrix_apply,
      hmap, Matrix.transpose_apply]
  have hdet : (polynomialRelationJacobian P.relation x).det = q P.jacobian := by
    rw [hmat, Matrix.det_transpose, ← RingHom.map_det,
      Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det, P.algebraMap_apply]
    exact (presentationSolutionPoint_aeval P.toPresentation ⟨x, hx⟩ P.jacobiMatrix.det).symm
  rw [hdet]
  exact (P.jacobian_isUnit.map q.toAlgHom).ne_zero

private def splitPresentationPointHomeomorph
    (P : Algebra.SubmersivePresentation k (AffineCoordinateRing k X) (Fin d ⊕ σ) σ) :
    RingPoint k X k ≃ₜ PresentationSolution P.toPresentation :=
  (affineSchemePointHomeomorph k X k).trans (presentationPointHomeomorph P.toPresentation)

private theorem splitPresentationPointHomeomorph_symm_eval
    (P : Algebra.SubmersivePresentation k (AffineCoordinateRing k X) (Fin d ⊕ σ) σ)
    (x : PresentationSolution P.toPresentation) (a : AffineCoordinateRing k X) :
    regularEvaluation ((splitPresentationPointHomeomorph P).symm x) a =
      eval x.val (P.σ a) := by
  change ((affineSchemePointHomeomorph k X k)
    ((affineSchemePointHomeomorph k X k).symm
      ((presentationPointHomeomorph P.toPresentation).symm x))) a = _
  rw [Homeomorph.apply_symm_apply]
  exact presentationSolutionPoint_apply P.toPresentation x a

/-- A split submersive presentation gives a regular chart at each actual point. -/
def RegularChart.ofSubmersivePresentation
    (P : Algebra.SubmersivePresentation k (AffineCoordinateRing k X) (Fin d ⊕ σ) σ)
    (hmap : ∀ j, P.map j = Sum.inr j) (p₀ : RingPoint k X k) : RegularChart k X d := by
  let e := splitPresentationPointHomeomorph P
  let C := polynomialFibreChart P.relation (submersivePresentation_jacobian_ne_zero P hmap) (e p₀)
  refine {
    homeomorph := e.toOpenPartialHomeomorph.trans C
    numerator := fun i => P.val (Sum.inl i)
    denominator := fun _ => 1
    denominator_ne_zero := ?_
    apply_eq := ?_
    contDiffOn_inverse_evaluation := ?_
  }
  · intro p hp i
    simp
  · intro p hp i
    simp only [map_one, div_one]
    rfl
  · intro a
    have hs := (polynomialFibreChart_contDiffOn_symm_eval P.relation
      (submersivePresentation_jacobian_ne_zero P hmap) (e p₀) (P.σ a)).restrict_scalars ℝ
    have heq : (fun v => regularEvaluation
        ((e.toOpenPartialHomeomorph.trans C).symm v) a) =
        (fun v => eval (C.symm v).val (P.σ a)) := by
      funext v
      exact splitPresentationPointHomeomorph_symm_eval P (C.symm v) a
    rw [heq]
    exact hs.mono (by intro y hy; exact hy.1)

/-- The chosen point belongs to the chart from its split submersive presentation. -/
theorem RegularChart.mem_ofSubmersivePresentation_source
    (P : Algebra.SubmersivePresentation k (AffineCoordinateRing k X) (Fin d ⊕ σ) σ)
    (hmap : ∀ j, P.map j = Sum.inr j) (p₀ : RingPoint k X k) :
    p₀ ∈ (RegularChart.ofSubmersivePresentation P hmap p₀).homeomorph.source := by
  refine ⟨Set.mem_univ _, ?_⟩
  exact mem_polynomialFibreChart_source P.relation
    (submersivePresentation_jacobian_ne_zero P hmap) (splitPresentationPointHomeomorph P p₀)

end Langlands.AlgebraicGeometry.PointManifold
