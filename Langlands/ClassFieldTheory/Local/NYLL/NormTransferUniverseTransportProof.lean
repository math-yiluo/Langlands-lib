import Langlands.ClassFieldTheory.Local.NYLL.UniverseTransportStatement
import Langlands.ClassFieldTheory.Local.NYLL.UniverseZeroModel

/-! # Universe transport of the finite norm and transfer diagrams -/

namespace Langlands.LocalClassField.NYLL

universe u v w

/-- The finite norm and transfer diagrams at field universes zero imply them at
arbitrary independent field universes. -/
theorem finiteAbelianNormTransferUniverseTransport :
    FiniteAbelianNormTransferUniverseTransportStatement.{u, v, w} := by
  intro H p _ F E L _ _ _ _ _ _ _ _ _ _ _ TF TE
  let := universeZeroAlgebra F E
  let := universeZeroAlgebra F L
  let := universeZeroAlgebra E L
  have := universeZeroAlgebra_isScalarTower F E
  have := universeZeroAlgebra_isScalarTower F L
  have := universeZeroAlgebra_isScalarTower E L
  have := universeZeroAlgebra_isScalarTower_tower F E L
  have := universeZeroAlgebra_finiteDimensional F E
  have := universeZeroAlgebra_finiteDimensional F L
  have := universeZeroAlgebra_finiteDimensional E L
  have := universeZeroAlgebra_isAbelianGalois F L
  let TF₀ := (universeZeroModel F).canonicalTopologicalData
  let TE₀ := (universeZeroModel E).canonicalTopologicalData
  obtain ⟨rF₀, rE₀, hnorm, htr⟩ :=
    H p (universeZeroModel F) (universeZeroModel E) (universeZeroModel L) TF₀ TE₀
  let := TF₀.topology
  let := TE₀.topology
  let := TF.topology
  let := TE.topology
  let QF := universeZeroNormQuotientEquiv F L TF₀ TF
  let QE := universeZeroNormQuotientEquiv E L TE₀ TE
  let GF := universeZeroGaloisEquiv F L
  let GE := universeZeroGaloisEquiv E L
  have hres : ∀ τ : Gal((universeZeroModel L).Carrier/(universeZeroModel E).Carrier),
      GF (τ.restrictScalars (universeZeroModel F).Carrier) =
        (GE τ).restrictScalars F.Carrier :=
    universeZeroGaloisEquiv_restrictScalars F E L
  refine ⟨QF.symm.trans (rF₀.trans GF), QE.symm.trans (rE₀.trans GE), ?_, ?_⟩
  · intro a
    have hN : QF.symm (QuotientGroup.mk (Units.map (Algebra.norm F.Carrier (S := E.Carrier)) a)) =
        QuotientGroup.mk (Units.map (Algebra.norm (universeZeroModel F).Carrier
          (S := (universeZeroModel E).Carrier))
            (Units.mapEquiv (universeZeroEquiv E).toRingEquiv.symm.toMulEquiv a)) := by
      rw [universeZeroNormQuotientEquiv_symm_mk F L TF₀ TF]
      congr 1
      apply Units.ext
      apply (universeZeroEquiv F).injective
      change universeZeroEquiv F ((universeZeroEquiv F).symm
          (Algebra.norm F.Carrier (a : E.Carrier))) =
        universeZeroEquiv F (Algebra.norm (universeZeroModel F).Carrier
          ((universeZeroEquiv E).symm (a : E.Carrier)))
      rw [universeZeroEquiv_norm F E, AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply]
    change GF (rF₀ (QF.symm _)) = (GE (rE₀ (QE.symm _))).restrictScalars F.Carrier
    rw [hN, hnorm, hres]
    rfl
  · intro a
    have hι : QE.symm (QuotientGroup.mk
          (Units.map (algebraMap F.Carrier E.Carrier).toMonoidHom a)) =
        QuotientGroup.mk (Units.map
          (algebraMap (universeZeroModel F).Carrier (universeZeroModel E).Carrier).toMonoidHom
            (Units.mapEquiv (universeZeroEquiv F).toRingEquiv.symm.toMulEquiv a)) := by
      rw [universeZeroNormQuotientEquiv_symm_mk E L TE₀ TE]
      congr 1
      apply Units.ext
      exact universeZeroEquiv_symm_algebraMap F E (a : F.Carrier)
    change (GE (rE₀ (QE.symm _))).restrictScalars F.Carrier = (GF (rF₀ (QF.symm _))) ^ _
    rw [hι, ← hres, htr, map_pow, universeZeroAlgebra_finrank F E]
    rfl

end Langlands.LocalClassField.NYLL
