import Langlands.GroupScheme.Examples.HermitianHyperbolicGramCoordinates
import Langlands.GroupScheme.Examples.HermitianHyperbolicSplitTorus
import Langlands.GroupScheme.Examples.HermitianMatrixNondegenerate

/-! # Isotropic subspaces and actual Hermitian split-rank lower bounds -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.HermitianMatrix

open SU3Root

section Ring

variable {A : Type u} [CommRing A] {Idx : Type v} [Fintype Idx] [DecidableEq Idx]
  {c : RingInvolution A}

/-- Conjugate transpose sends an actual invertible matrix to an invertible matrix. -/
def adjointGL (c : RingInvolution A) (P : Matrix.GeneralLinearGroup Idx A) :
    Matrix.GeneralLinearGroup Idx A where
  val := adjoint c (P : Matrix Idx Idx A)
  inv := adjoint c (P⁻¹ : Matrix.GeneralLinearGroup Idx A)
  val_inv := by
    rw [← adjoint_mul]
    change adjoint c ((P⁻¹ * P : Matrix.GeneralLinearGroup Idx A) : Matrix Idx Idx A) = 1
    simp
  inv_val := by
    rw [← adjoint_mul]
    change adjoint c ((P * P⁻¹ : Matrix.GeneralLinearGroup Idx A) : Matrix Idx Idx A) = 1
    simp

@[simp] theorem adjointGL_val (P : Matrix.GeneralLinearGroup Idx A) :
    (adjointGL c P : Matrix Idx Idx A) = adjoint c (P : Matrix Idx Idx A) := rfl

namespace Form

/-- Pull back the actual nonsingular Gram form along a coordinate automorphism. -/
def pullback (H : Form c Idx) (P : Matrix.GeneralLinearGroup Idx A) : Form c Idx where
  gram := adjointGL c P * H.gram * P
  hermitian := by
    change adjoint c (adjoint c (P : Matrix Idx Idx A) *
        (H.gram : Matrix Idx Idx A) * (P : Matrix Idx Idx A)) =
      adjoint c (P : Matrix Idx Idx A) * (H.gram : Matrix Idx Idx A) * (P : Matrix Idx Idx A)
    simp only [adjoint_mul, adjoint_adjoint, H.hermitian, Matrix.mul_assoc]

@[simp] theorem pullback_gram (H : Form c Idx) (P : Matrix.GeneralLinearGroup Idx A) :
    ((H.pullback P).gram : Matrix Idx Idx A) =
      adjoint c (P : Matrix Idx Idx A) * (H.gram : Matrix Idx Idx A) * (P : Matrix Idx Idx A) := rfl

end Form
end Ring

namespace SchemeModel

variable {K L : Type u} [Field K] [Field L] [Algebra K L]
  [Algebra.IsQuadraticExtension K L] [Algebra.IsSeparable K L]
  {Idx : Type v} [Fintype Idx] [DecidableEq Idx]
  {H : Form (fieldInvolution K L) Idx}
  {G : GroupScheme (Spec (CommRingCat.of K))}

namespace Presentation

/-- Transport the full all-test presentation to the pulled-back Gram form. -/
def pullback (e : Presentation K L H G) (P : Matrix.GeneralLinearGroup Idx L) :
    Presentation K L (H.pullback P) G :=
  e.isometry P⁻¹ (gramCongruence_inv (H := H.pullback P) (J := H) P rfl)

variable [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]

/-- A supplied hyperbolic decomposition gives a closed split torus of that rank. -/
theorem planes_le_splitRank (e : Presentation K L H G) {r : ℕ}
    (d : HermitianRoot.HyperbolicDecomposition H.linearFirst r) :
    (r : ℕ∞) ≤ splitRank G := by
  let P := HermitianRoot.MultiHyperbolic.coordinateMatrix d.basisCoordinates
  let J := (H.pullback P).reindex d.indexEquiv
  have hJ : (J.gram : Matrix _ _ L) =
      HermitianRoot.MultiHyperbolic.gram (α := Fin r) d.middleGram := by
    change Matrix.reindex d.indexEquiv d.indexEquiv
      (adjoint (fieldInvolution K L) (P : Matrix Idx Idx L) *
        (H.gram : Matrix Idx Idx L) * (P : Matrix Idx Idx L)) = _
    dsimp only [P, adjoint]
    rw [d.gram_congruence H.gram H.linearFirst_eq_dotProduct]
    ext i j
    simp
  exact HermitianRoot.MultiHyperbolic.planes_le_splitRank J d.middleGram hJ
    ((e.pullback P).reindex d.indexEquiv)

/-- Every actual totally isotropic subspace gives the corresponding lower bound. -/
theorem finrank_le_splitRank (e : Presentation K L H G) (W : Submodule L (Idx → L))
    (hW : H.IsTotallyIsotropic W) : (Module.finrank L W : ℕ∞) ≤ splitRank G := by
  obtain ⟨d⟩ := HermitianRoot.nonempty_hyperbolicDecomposition_of_totallyIsotropic
    H.linearFirst H.bar_linearFirst H.linearFirst_nondegenerate W
    (fun a b => (H.totallyIsotropic_iff_linearFirst W).mp hW a a.property b b.property)
  exact e.planes_le_splitRank d

/-- The attained maximum isotropic dimension is bounded by actual split rank. -/
theorem wittIndex_le_splitRank (e : Presentation K L H G) :
    (H.wittIndex : ℕ∞) ≤ splitRank G := by
  obtain ⟨W, hW, hdim⟩ := H.exists_totallyIsotropic_finrank_eq_wittIndex
  rw [← hdim]
  exact e.finrank_le_splitRank W hW

end Presentation
end SchemeModel
end Langlands.GroupScheme.HermitianMatrix
