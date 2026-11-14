import Langlands.GroupScheme.Quaternionic.OrthogonalMoritaRepresentationStatement
import Langlands.GroupScheme.Quaternionic.OrthogonalMoritaAffine
import Langlands.GroupScheme.Quaternionic.OrthogonalMoritaRowBasis
import Langlands.GroupScheme.Quaternionic.OrthogonalMoritaSplitUnits

/-! # Orthogonal Morita comparison retaining the all-coefficient row representation -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry Matrix Module
open scoped TensorProduct CategoryTheory.MonObj

namespace Langlands.GroupScheme.Quaternionic
namespace OrthogonalMorita

variable {K D L : Type u} [Field K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Field L] [Algebra K L]
  {m degree n : ℕ}
  (e : L ⊗[K] D ≃ₐ[L] Matrix (Fin degree) (Fin degree) L)
  (σ : FirstKindInvolution K D)
  (hσ : finrank K σ.symmetricSubspace = degree * (degree + 1) / 2)
  (q : σ.QuadraticForms (Fin m))
  (P : Matrix (Fin n ⊕ Fin n) (Fin m × Fin degree) L)
  (P' : Matrix (Fin m × Fin degree) (Fin n ⊕ Fin n) L)
  (hPP' : P * P' = 1) (hP'P : P' * P = 1)
  (hPQ : OrthogonalMatrix.IsAlt (P * DegreeSplitting.splitGram e σ (Quotient.out q) * Pᵀ -
    OrthogonalMatrix.formMatrix (Fin n) L))

/-- The natural unit comparison supplied by the fixed splitting and hyperbolic basis. -/
def splittingUnitComparison : UnitComparison σ q L n where
  equiv R := splitUnitsEquiv e σ (by simpa using hσ) R P P' (Quotient.out q) hPP' hP'P hPQ
  naturality φ y := splitUnitsEquiv_naturality e σ (by simpa using hσ)
    _ P P' (Quotient.out q) hPP' hP'P hPQ φ y

/-- Reconstruct the group scheme and retain the actual inverse-right row action. -/
def comparisonOfSplitting : OrthogonalMoritaComparison σ q L degree n where
  groupIso := (splittingUnitComparison e σ hσ q P P' hPP' hP'P hPQ).groupIso
  rowEquiv := basisRowEquiv e hPP' hP'P
  intertwines := by
    intro R _ _ _ _ a z
    let c := splittingUnitComparison e σ hσ q P P' hPP' hP'P hPQ
    let y := isometryAffineUnitsEquiv σ q (CommAlgCat.of (CommRingCat.of K) R) a
    have hmat := c.affineMatrix_splitPoint R a
    have hi : (((MatrixRepresentation.affineMatrix
          (OrthogonalMatrix.inclusion (Fin n) (CommRingCat.of L))
          (CommAlgCat.of (CommRingCat.of L) R)
          (splitPoint σ q c.groupIso R a))⁻¹) :
          Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R) =
        conjugatedMatrix e R P P' (y⁻¹).1 := by
      rw [hmat, ← GeneralLinearGroup.coe_inv, ← map_inv, ← map_inv,
        OrthogonalMatrix.coe_toGL]
      exact coe_splitUnitsEquiv e σ (by simpa using hσ) R P P' (Quotient.out q)
        hPP' hP'P hPQ (y⁻¹)
    rw [hi]
    have hy : ((y⁻¹).1 : R ⊗[K] Matrix (Fin m) (Fin m) D) =
        (((σ.isometryAffineUnitsOver q (CommAlgCat.of (CommRingCat.of K) R) a)⁻¹ :
          (R ⊗[K] Matrix (Fin m) (Fin m) D)ˣ) : R ⊗[K] Matrix (Fin m) (Fin m) D) := by
      rw [Subgroup.coe_inv]
      rw [show y.1 = σ.isometryAffineUnitsOver q (CommAlgCat.of (CommRingCat.of K) R) a
        from coe_isometryAffineUnitsEquiv σ q _ a]
    rw [conjugatedMatrix, hy]
    exact basisRowEquiv_rightAction e hPP' hP'P R _ z

end OrthogonalMorita

/-- The orthogonal Morita comparison with the actual all-coefficient row representation. -/
theorem orthogonalMoritaRepresentation : OrthogonalMoritaRepresentationStatement.{u} := by
  intro K D _ _ _ _ _ degree m n _ _ hD hdim σ hσ q hq L _ _ _
  obtain ⟨d, _, ⟨e⟩⟩ := CentralSimple.exists_matrix_chart K D L
  have hd : d = degree := by
    have h := CentralSimple.finrank_eq_matrix_size K D L d e
    rw [hD, pow_two] at h
    exact Nat.mul_self_inj.mp h.symm
  subst d
  have hpolar := OrthogonalMorita.isUnit_splitGram_polar e σ (by simpa using hσ)
    q (Quotient.out q) (Quotient.out_eq q) hq
  have hcard : Fintype.card (Fin m × Fin degree) = 2 * n := by simpa using hdim
  obtain ⟨P, P', hPP', hP'P, hPQ⟩ := OrthogonalMatrix.exists_hyperbolic_matrix
    hcard (DegreeSplitting.splitGram e σ (Quotient.out q)) hpolar
  exact ⟨OrthogonalMorita.comparisonOfSplitting e σ hσ q P P' hPP' hP'P hPQ⟩

end Langlands.GroupScheme.Quaternionic
