import Langlands.Global.AdelicGLIwasawa
import Langlands.Global.AdelicGLSiegelShape
import Langlands.Global.PrincipalAdelesDiscreteProof

/-! # Compact diagonal parameters in adelic Iwasawa decomposition -/

noncomputable section
universe u
open Set Topology
open scoped Pointwise

namespace Langlands.Global.PrimitiveAdelicHeight

variable (F : Type u) [Field F] [NumberField F] (n : ℕ)

/-- The tuple of diagonal ideles of an upper triangular adelic matrix. -/
def upperTriangularDiagonal
    (b : GeneralLinear.upperTriangularSubgroup n (Adeles F)) : Fin n → Ideles F :=
  diagonalUnit b.1 b.2

theorem continuous_upperTriangularDiagonal :
    Continuous (upperTriangularDiagonal F n) := by
  apply continuous_pi
  intro i
  apply Units.continuous_iff.mpr
  exact ⟨(Units.continuous_val.comp continuous_subtype_val).matrix_elem i i,
    (Units.continuous_coe_inv.comp continuous_subtype_val).matrix_elem i i⟩

theorem isClosed_adelicUpperTriangular :
    IsClosed (GeneralLinear.upperTriangularSubgroup n (Adeles F) :
      Set (AdelicGL F n)) := by
  let : T2Space (Adeles F) := adeles_t2Space F
  exact isClosed_setOfPred_blockTriangular.preimage Units.continuous_val

/-- On each compact subset of the adelic general linear group, Iwasawa
factorizations can be chosen with their diagonal idele tuples in one compact set. -/
theorem exists_compact_iwasawaDiagonal {C : Set (AdelicGL F n)} (hC : IsCompact C) :
    ∃ D : Set (Fin n → Ideles F), IsCompact D ∧
      ∀ g ∈ C, ∃ d ∈ D, ∃ u k : AdelicGL F n,
        IsUnitriangular u.val ∧ k ∈ standardCompact F n ∧
          g = u * diagonalGL d * k := by
  let B := GeneralLinear.upperTriangularSubgroup n (Adeles F)
  let S : Set B := Subtype.val ⁻¹'
    (C * (standardCompact F n : Set (AdelicGL F n))⁻¹)
  have hS : IsCompact S :=
    (isClosed_adelicUpperTriangular F n).isClosedEmbedding_subtypeVal.isCompact_preimage
      (hC.mul (isCompact_standardCompact F n).inv)
  refine ⟨upperTriangularDiagonal F n '' S,
    hS.image (continuous_upperTriangularDiagonal F n), ?_⟩
  intro g hg
  obtain ⟨b, k, hgb, hb, hk⟩ := exists_isStandardIwasawaFactorization F n g
  let b' : B := ⟨b, hb⟩
  let d := upperTriangularDiagonal F n b'
  have hbS : b' ∈ S := by
    change b ∈ C * (standardCompact F n : Set (AdelicGL F n))⁻¹
    exact ⟨g, hg, k⁻¹, hk, by rw [hgb]; group⟩
  refine ⟨d, ⟨b', hbS, rfl⟩, b * (diagonalGL d)⁻¹, k, ?_, hk, ?_⟩
  · change IsUnitriangular (b.val *
      Matrix.diagonal fun i => (((d i)⁻¹ : (Adeles F)ˣ) : Adeles F))
    exact isUnitriangular_mul_diagonal hb d (fun _ => rfl)
  · simpa only [mul_assoc, inv_mul_cancel, mul_one] using hgb

end Langlands.Global.PrimitiveAdelicHeight
