import Langlands.GroupScheme.OddOrthogonalMatrix.Representation
import Langlands.AlgebraicGeometry.SmoothReducedProof

/-! # Triviality from the fixed hyperbolic hyperplane on reduced tests -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

open CategoryTheory AlgebraicGeometry
open scoped Matrix CategoryTheory.MonObj

namespace Langlands.GroupScheme.OddOrthogonalMatrix

open Quaternionic.FirstKindInvolution Quaternionic.ScalarMatrixCoordinates

variable {l : Type} [Fintype l] [DecidableEq l] (K : Type u) [Field K]

/-- The exact quadratic and determinant equations of every actual test point. -/
theorem pointMatrix_equations (T : Over (Spec (CommRingCat.of K)))
    (z : T ⟶ (groupScheme l K).X) :
    OrthogonalMatrix.IsAlt ((pointMatrix K T z : Matrix (Index l) (Index l) Γ(T.left, ⊤)) *
      (formMatrix l K).map (scalarMap T) * (pointMatrix K T z).val.transpose -
        (formMatrix l K).map (scalarMap T)) ∧
      (pointMatrix K T z).val.det = 1 := by
  have hm : z ≫ ((scalar K).normOneIsometryAmbientι (form l K)).hom.hom ∈
      (SubgroupFunctor.range ((scalar K).normOneIsometryAmbientι (form l K))).carrier T :=
    ⟨z, rfl⟩
  rw [mem_range_normOneIsometryAmbientι_iff K (form l K) (formMatrix l K) rfl] at hm
  exact hm

/-- Normal block form of a matrix fixing the hyperbolic hyperplane pointwise. -/
def axisColumnMatrix {R : Type*} [CommRing R] (a : R) (c : l ⊕ l → R) :
    Matrix (Index l) (Index l) R :=
  Matrix.fromBlocks (fun _ _ : Unit => a) 0 (fun i (_ : Unit) => c i) 1

omit [Fintype l] in
/-- Fixing the hyperbolic columns gives the axis-column normal block form. -/
theorem eq_axisColumnMatrix_of_even_columns {R : Type*} [CommRing R]
    (g : Matrix (Index l) (Index l) R)
    (hcol : ∀ (i : Index l) (a : l ⊕ l),
      g i (Sum.inr a) = (1 : Matrix (Index l) (Index l) R) i (Sum.inr a)) :
    g = axisColumnMatrix (g (Sum.inl ()) (Sum.inl ()))
      (fun a => g (Sum.inr a) (Sum.inl ())) := by
  apply Matrix.ext
  intro i j
  rcases i with i | i <;> rcases j with j | j
  · cases i; cases j; rfl
  · simpa [axisColumnMatrix] using hcol (Sum.inl i) j
  · cases j; rfl
  · simpa only [axisColumnMatrix, Matrix.fromBlocks_apply₂₂, Matrix.one_apply, Sum.inr.injEq]
      using hcol (Sum.inr i) j

/-- An odd norm-one matrix over a reduced coefficient algebra that fixes
the hyperbolic hyperplane pointwise is the identity. -/
theorem matrix_eq_one_of_even_columns {R : Type u} [CommRing R] [IsReduced R] (f : K →+* R)
    (g : Matrix (Index l) (Index l) R)
    (hcol : ∀ (i : Index l) (a : l ⊕ l), g i (Sum.inr a) = (1 : Matrix (Index l) (Index l) R) i (Sum.inr a))
    (hQ : OrthogonalMatrix.IsAlt (g * (formMatrix l K).map f * g.transpose -
      (formMatrix l K).map f)) (hdet : g.det = 1) : g = 1 := by
  have hg := eq_axisColumnMatrix_of_even_columns g hcol
  change g = Matrix.fromBlocks (fun _ _ : Unit => g (Sum.inl ()) (Sum.inl ())) 0
      (fun (a : l ⊕ l) (_ : Unit) => g (Sum.inr a) (Sum.inl ())) 1 at hg
  have ha : g (Sum.inl ()) (Sum.inl ()) = 1 := by
    rw [hg, Matrix.det_fromBlocks_zero₁₂, Matrix.det_unique, Matrix.det_one, mul_one] at hdet
    exact hdet
  have hc (a : l ⊕ l) : g (Sum.inr a) (Sum.inl ()) = 0 := by
    have hd := ((OrthogonalMatrix.isAlt_iff _).mp hQ).2 (Sum.inr a)
    rw [hg] at hd
    have hs : g (Sum.inr a) (Sum.inl ()) * g (Sum.inr a) (Sum.inl ()) = 0 := by
      simpa [formMatrix, Matrix.mul_apply, Fintype.sum_sum_type,
        OrthogonalMatrix.formMatrix, Matrix.one_apply] using hd
    exact eq_zero_of_pow_eq_zero (by simpa only [pow_two] using hs :
      g (Sum.inr a) (Sum.inl ()) ^ 2 = 0)
  apply Matrix.ext
  intro i j
  rcases j with j | a
  · cases j
    rcases i with i | a
    · cases i; simpa using ha
    · simpa using hc a
  · exact hcol i a

/-- A smooth group acting through the odd norm-one model and fixing the
hyperbolic basis pointwise has the trivial actual underlying morphism. -/
theorem hom_eq_one_of_even_fixed {H : GroupScheme (Spec (CommRingCat.of K))}
    [Smooth H.X.hom] (j : H ⟶ groupScheme l K)
    (hfix : ∀ a : l ⊕ l, Pi.single (Sum.inr a) (1 : K) ∈
      MatrixRepresentation.fixedSubmodule (j ≫ inclusion K)) : j.hom.hom = 1 := by
  have : AlgebraicGeometry.IsReduced H.X.left :=
    Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field K _ H.X.hom
  have hcol (i : Index l) (a : l ⊕ l) :
      pointMatrix K H.X j.hom.hom i (Sum.inr a) = (1 : Matrix (Index l) (Index l) Γ(H.X.left, ⊤)) i (Sum.inr a) := by
    have h := hfix a H.X (𝟙 H.X)
    rw [MatrixRepresentation.pointMatrix_apply, Grp.comp_hom_hom, ← Category.assoc,
      Category.id_comp, pointsEquiv_inclusion] at h
    have hs : (fun i => scalarMap H.X ((Pi.single (Sum.inr a) (1 : K) : Index l → K) i)) =
        Pi.single (Sum.inr a) 1 := by
      funext b
      by_cases hb : b = Sum.inr a <;> simp [hb]
    rw [hs, Matrix.mulVec_single_one] at h
    simpa [Matrix.col, Matrix.one_apply, Pi.single_apply, eq_comm] using congrFun h i
  have hmat := matrix_eq_one_of_even_columns K (scalarMap H.X) (pointMatrix K H.X j.hom.hom).val hcol
    (pointMatrix_equations K H.X j.hom.hom).1 (pointMatrix_equations K H.X j.hom.hom).2
  apply (cancel_mono (inclusion K).hom.hom).mp
  rw [MonObj.one_comp]
  apply (GeneralLinear.pointsEquiv (Index l) (CommRingCat.of K) H.X).injective
  rw [pointsEquiv_inclusion, _root_.map_one]
  exact Units.ext hmat

end Langlands.GroupScheme.OddOrthogonalMatrix
