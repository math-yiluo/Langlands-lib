import Langlands.AlgebraicGeometry.PointManifold.PolynomialCalculus
import Langlands.AlgebraicGeometry.PointTopology.Affine
import Mathlib.Analysis.RCLike.Lemmas
import Mathlib.RingTheory.Extension.Presentation.Basic

/-! # Presentation solutions and algebraic points with the evaluation topology -/

noncomputable section

namespace Langlands.AlgebraicGeometry.PointManifold

open MvPolynomial PointTopology

variable {k A ι σ : Type*} [RCLike k] [CommRing A] [Algebra k A] [Fintype ι]

/-- The solutions of the relations of a presentation, with the induced topology. -/
abbrev PresentationSolution (P : Algebra.Presentation k A ι σ) :=
  {x : ι → k // (fun j => eval x (P.relation j)) = 0}

private theorem presentationSolution_ker_le (P : Algebra.Presentation k A ι σ)
    (x : PresentationSolution P) :
    P.ker ≤ RingHom.ker (aeval x.val : MvPolynomial ι k →ₐ[k] k) := by
  rw [← P.span_range_relation_eq_ker, Ideal.span_le]
  rintro _ ⟨j, rfl⟩
  exact congrFun x.property j

/-- A solution of the presentation defines an actual algebra-map point. -/
def presentationSolutionPoint (P : Algebra.Presentation k A ι σ)
    (x : PresentationSolution P) : AlgPoint k A k :=
  AlgPoint.ofAlgHom
    ((Ideal.Quotient.liftₐ P.ker (aeval x.val)
      (fun q hq => presentationSolution_ker_le P x hq)).comp
        (P.quotientEquiv.restrictScalars k).symm.toAlgHom)

@[simp] theorem presentationSolutionPoint_apply (P : Algebra.Presentation k A ι σ)
    (x : PresentationSolution P) (a : A) :
    presentationSolutionPoint P x a = eval x.val (P.σ a) := rfl

@[simp] theorem presentationSolutionPoint_aeval (P : Algebra.Presentation k A ι σ)
    (x : PresentationSolution P) (q : MvPolynomial ι k) :
    presentationSolutionPoint P x (aeval P.val q) = eval x.val q := by
  change (Ideal.Quotient.liftₐ P.ker (aeval x.val)
    (fun q hq => presentationSolution_ker_le P x hq))
      ((P.quotientEquiv.restrictScalars k).symm (aeval P.val q)) = _
  have h : (P.quotientEquiv.restrictScalars k).symm (aeval P.val q) =
      Ideal.Quotient.mk P.ker q := by
    apply (P.quotientEquiv.restrictScalars k).injective
    simp
  rw [h]
  rfl

@[simp] theorem presentationSolutionPoint_val (P : Algebra.Presentation k A ι σ)
    (x : PresentationSolution P) (i : ι) :
    presentationSolutionPoint P x (P.val i) = x.val i := by
  simpa only [aeval_X, eval_X] using presentationSolutionPoint_aeval P x (X i)

/-- Coordinates of an actual algebra-map point satisfy the presentation relations. -/
def presentationPointSolution (P : Algebra.Presentation k A ι σ)
    (q : AlgPoint k A k) : PresentationSolution P :=
  ⟨fun i => q (P.val i), by
    funext j
    change aeval (fun i => q.toAlgHom (P.val i)) (P.relation j) = 0
    rw [← comp_aeval_apply, P.aeval_val_relation, map_zero]⟩

@[simp] theorem presentationPointSolution_val (P : Algebra.Presentation k A ι σ)
    (q : AlgPoint k A k) (i : ι) :
    (presentationPointSolution P q).val i = q (P.val i) := rfl

/-- The actual point space is homeomorphic to its finite presentation solution space. -/
def presentationPointHomeomorph (P : Algebra.Presentation k A ι σ) :
    AlgPoint k A k ≃ₜ PresentationSolution P where
  toFun := presentationPointSolution P
  invFun := presentationSolutionPoint P
  left_inv q := by
    apply AlgPoint.ext
    intro a
    change aeval (fun i => q.toAlgHom (P.val i)) (P.σ a) = q a
    rw [← comp_aeval_apply, P.aeval_val_σ]
    rfl
  right_inv x := by
    apply Subtype.ext
    funext i
    exact presentationSolutionPoint_val P x i
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact continuous_pi (fun i => AlgPoint.continuous_eval (P.val i))
  continuous_invFun := by
    apply (AlgPoint.continuous_iff _).mpr
    intro a
    exact (contDiff_polynomial_eval (P.σ a) 0).continuous.comp continuous_subtype_val

@[simp] theorem presentationPointHomeomorph_apply (P : Algebra.Presentation k A ι σ)
    (q : AlgPoint k A k) :
    presentationPointHomeomorph P q = presentationPointSolution P q := rfl

@[simp] theorem presentationPointHomeomorph_symm_apply (P : Algebra.Presentation k A ι σ)
    (x : PresentationSolution P) :
    (presentationPointHomeomorph P).symm x = presentationSolutionPoint P x := rfl

end Langlands.AlgebraicGeometry.PointManifold
