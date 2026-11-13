import Langlands.GroupScheme.Torus.HermitianLaurentOrthogonality
import Langlands.GroupScheme.Torus.HermitianWeightIsotropy
import Langlands.GroupScheme.Examples.HermitianMatrixNondegenerate

/-! # Isotropic dimension bound for a faithful Hermitian matrix torus -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry
open scoped Matrix

namespace Langlands.GroupScheme.FiniteMatrixAlgebraTorusWeights

open FiniteAlgebraUnits HermitianMatrix

variable {K L : Type u} [Field K] [Field L] [Algebra K L]
  {N d : ℕ} {b : Module.Basis (Fin d) K (Matrix (Fin N) (Fin N) L)}
  {I : Type u} [Fintype I] [DecidableEq I]
  (i : splitTorus (Spec (CommRingCat.of K)) I ⟶ groupScheme b)

/-- If the inverse universal Laurent matrix is a full Hermitian isometry,
faithfulness bounds the torus dimension by the attained Witt index. -/
theorem exists_totallyIsotropic_finrank_ge_card
    (hi : Mono i.hom.hom.left) (c : SU3Root.RingInvolution L)
    (H : Form c (Fin N))
    (hP : (((inverseUniversalMatrix i : Matrix (Fin N) (Fin N)
        (AddMonoidAlgebra L (I → ℤ))).map (HermitianLaurent.coefficientInvolution c).bar).transpose) *
        (H.gram : Matrix (Fin N) (Fin N) L).map (AddMonoidAlgebra.single 0) *
        (inverseUniversalMatrix i : Matrix (Fin N) (Fin N) (AddMonoidAlgebra L (I → ℤ))) =
      (H.gram : Matrix (Fin N) (Fin N) L).map (AddMonoidAlgebra.single 0)) :
    ∃ W : Submodule L (Fin N → L), H.IsTotallyIsotropic W ∧
      Fintype.card I ≤ Module.finrank L W := by
  classical
  obtain ⟨v, q, hv, hgen, hact⟩ := exists_weightBasis i hi
  have heig (j : Fin N) := inverseUniversalMatrix_mulVec i
    (mem_weightSupport_of_basis_column i v q hv j) (v j) (fun m => hact m j)
  obtain ⟨W, hW, hdim⟩ := HermitianWeights.exists_isotropic_of_weightBasis
    H.linearFirst v (fun j => (q j).1) hgen (by
      intro j k hjk
      rw [H.linearFirst_eq_dotProduct]
      exact HermitianLaurent.pairing_eq_zero_of_eigenvectors c _ _ hP
        (q k).1 (q j).1 (by simpa only [add_comm] using hjk)
        (v k) (v j) (heig k) (heig j))
  refine ⟨W, ?_, hdim⟩
  apply (H.totallyIsotropic_iff_linearFirst W).mpr
  intro x hx y hy
  exact hW ⟨x, hx⟩ ⟨y, hy⟩

/-- The actual isotropic submodule selected from the torus weight basis. -/
def weightIsotropicSubmodule
    (hi : Mono i.hom.hom.left) (c : SU3Root.RingInvolution L)
    (H : Form c (Fin N))
    (hP : (((inverseUniversalMatrix i : Matrix (Fin N) (Fin N)
        (AddMonoidAlgebra L (I → ℤ))).map (HermitianLaurent.coefficientInvolution c).bar).transpose) *
        (H.gram : Matrix (Fin N) (Fin N) L).map (AddMonoidAlgebra.single 0) *
        (inverseUniversalMatrix i : Matrix (Fin N) (Fin N) (AddMonoidAlgebra L (I → ℤ))) =
      (H.gram : Matrix (Fin N) (Fin N) L).map (AddMonoidAlgebra.single 0)) :
    Submodule L (Fin N → L) :=
  Classical.choose (exists_totallyIsotropic_finrank_ge_card i hi c H hP)

/-- Faithful Hermitian tori are bounded by the attained Witt index. -/
theorem card_le_wittIndex_of_inverseUniversalMatrix_isometry
    (hi : Mono i.hom.hom.left) (c : SU3Root.RingInvolution L)
    (H : Form c (Fin N))
    (hP : (((inverseUniversalMatrix i : Matrix (Fin N) (Fin N)
        (AddMonoidAlgebra L (I → ℤ))).map (HermitianLaurent.coefficientInvolution c).bar).transpose) *
        (H.gram : Matrix (Fin N) (Fin N) L).map (AddMonoidAlgebra.single 0) *
        (inverseUniversalMatrix i : Matrix (Fin N) (Fin N) (AddMonoidAlgebra L (I → ℤ))) =
      (H.gram : Matrix (Fin N) (Fin N) L).map (AddMonoidAlgebra.single 0)) :
    Fintype.card I ≤ H.wittIndex := by
  obtain ⟨W, hW, hdim⟩ := exists_totallyIsotropic_finrank_ge_card i hi c H hP
  exact hdim.trans (H.finrank_le_wittIndex W hW)

end Langlands.GroupScheme.FiniteMatrixAlgebraTorusWeights
