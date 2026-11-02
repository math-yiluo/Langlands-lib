import Langlands.GroupScheme.AffinePointCoordinateSmooth
import Langlands.GroupScheme.GeneralLinearPointTopology
import Mathlib.Analysis.Matrix.Normed

/-! # Coordinate-smooth families and the actual general-linear manifold -/

noncomputable section

universe u v w

open CategoryTheory Opposite AlgebraicGeometry MvPolynomial
open scoped CategoryTheory.MonObj Manifold ContDiff Matrix.Norms.Operator

namespace Langlands.GroupScheme.GeneralLinear

set_option backward.isDefEq.respectTransparency false

variable (n : Type) [Fintype n] [DecidableEq n]
  (R : CommRingCat.{u}) (A : CommAlgCat.{u} R)
  {B : Type u} [NormedCommRing B] [NormedAlgebra ℝ B] [CompleteSpace B]
  (c : A →+* B)
  {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type v} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {M : Type w} [TopologicalSpace M] [ChartedSpace H M]

local instance matrixComplete : CompleteSpace (Matrix n n B) :=
  inferInstanceAs (CompleteSpace (n → n → B))

/-- Actual general-linear points, in the specified real coefficient coordinates. -/
def coefficientCoordinates : (groupScheme n R).affinePoints A →* GL n B :=
  (Matrix.GeneralLinearGroup.map c).comp (affinePointsEquiv n R A).toMonoidHom

omit [NormedAlgebra ℝ B] [CompleteSpace B] in
@[simp] theorem coefficientCoordinates_entry
    (p : (groupScheme n R).affinePoints A) (i j : n) :
    coefficientCoordinates n R A c p i j =
      c ((groupScheme n R).affinePointEvaluation A p (entrySection n R i j)) := by
  exact congrArg c (affinePointsEquiv_entry_evaluation n R A p i j)

private def matrixEntry (i j : n) : Matrix n n B →L[ℝ] B where
  toLinearMap :=
    { toFun := fun x => x i j
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  cont := (continuous_apply j).comp (continuous_apply i)

private def matrixAssemble : (n → n → B) →L[ℝ] Matrix n n B where
  toLinearMap := LinearMap.id
  cont := continuous_id

omit [DecidableEq n] [CompleteSpace B] in
private theorem contMDiff_matrix_of_entries {f : M → Matrix n n B}
    (hf : ∀ i j, ContMDiff I 𝓘(ℝ, B) ∞ (fun x => f x i j)) :
    ContMDiff I 𝓘(ℝ, Matrix n n B) ∞ f := by
  have h : ContMDiff I 𝓘(ℝ, n → n → B) ∞ (fun x => fun i j => f x i j) :=
    contMDiff_pi_space.mpr (fun i => contMDiff_pi_space.mpr (hf i))
  exact (matrixAssemble n (B := B)).contDiff.contMDiff.comp h

private theorem contMDiff_entries_of_units {g : M → GL n B}
    (hg : ContMDiff I 𝓘(ℝ, Matrix n n B) ∞ g) (i j : n) :
    ContMDiff I 𝓘(ℝ, B) ∞ (fun x => g x i j) :=
  (matrixEntry n (B := B) i j).contDiff.contMDiff.comp (Units.contMDiff_val.comp hg)

private theorem contMDiff_classify {g : M → GL n A}
    (hg : ContMDiff I 𝓘(ℝ, Matrix n n B) ∞
      (fun x => Matrix.GeneralLinearGroup.map c (g x))) (a : CoordinateRing n R) :
    ContMDiff I 𝓘(ℝ, B) ∞ (fun x => c (classify (R := R) (g x) a)) := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
  change ContMDiff I 𝓘(ℝ, B) ∞ (fun x => c (classify (g x) (quotient n R p)))
  simp_rw [classify_quotient]
  induction p using MvPolynomial.induction_on with
  | C r => simpa only [aeval_C] using
      (contMDiff_const : ContMDiff I 𝓘(ℝ, B) ∞ (fun _ : M => c (algebraMap R A r)))
  | add p q hp hq =>
      simpa only [map_add, Function.comp_def] using
        (contDiff_add (𝕜 := ℝ) (F := B)).contMDiff.comp (hp.prodMk_space hq)
  | mul_X p i hp =>
      have hi : ContMDiff I 𝓘(ℝ, B) ∞ (fun x => c (values (g x) i)) := by
        cases i with
        | entry i j =>
            exact contMDiff_entries_of_units n I hg i j
        | inverseEntry i j =>
            have h := contMDiff_entries_of_units n I hg.inv i j
            simpa only [← map_inv, Matrix.GeneralLinearGroup.map_apply, values] using h
      simpa only [map_mul, aeval_X, Function.comp_def] using
        (contDiff_mul (𝕜 := ℝ) (𝔸 := B)).contMDiff.comp (hp.prodMk_space hi)

/-- Testing all actual regular functions is exactly smoothness into the existing
matrix-units manifold after the specified coefficient map. -/
theorem coordinateSmooth_iff_contMDiff (p : M → (groupScheme n R).affinePoints A) :
    (groupScheme n R).CoordinateSmooth A c I p ↔
      ContMDiff I 𝓘(ℝ, Matrix n n B) ∞
        (fun x => coefficientCoordinates n R A c (p x)) := by
  constructor
  · intro hp
    apply ContMDiff.of_comp_isOpenEmbedding Units.isOpenEmbedding_val
    apply contMDiff_matrix_of_entries n I
    intro i j
    simpa only [Function.comp_def, coefficientCoordinates_entry] using hp (entrySection n R i j)
  · intro hp a
    have he (x : M) :
        (groupScheme n R).affinePointEvaluation A (p x) a =
          classify (affinePointsEquiv n R A (p x))
            ((Scheme.ΓSpecIso (CommRingCat.of (CoordinateRing n R))).hom a) := by
      have h := affinePointEvaluation_map_classify n R A (affinePointsEquiv n R A (p x)) a
      rw [← affinePointsEquiv_symm_apply, MulEquiv.symm_apply_apply] at h
      exact h
    simp_rw [he]
    exact contMDiff_classify n R A c I hp _

end Langlands.GroupScheme.GeneralLinear
