import Langlands.ClassFieldTheory.Local.NYLL.UniverseTransportStatement
import Langlands.ClassFieldTheory.Local.NYLL.UniverseZeroModel

/-! # Universe transport of the finite tower restriction diagram -/

namespace Langlands.LocalClassField.NYLL

universe u v w

/-- The finite tower restriction diagram at field universes zero implies it at
arbitrary independent field universes. -/
theorem finiteAbelianRestrictionUniverseTransport :
    FiniteAbelianRestrictionUniverseTransportStatement.{u, v, w} := by
  intro H p _ F E L _ _ _ _ _ _ _ _ _ _ TF
  let := universeZeroAlgebra F E
  let := universeZeroAlgebra F L
  let := universeZeroAlgebra E L
  have := universeZeroAlgebra_isScalarTower F E
  have := universeZeroAlgebra_isScalarTower F L
  have := universeZeroAlgebra_isScalarTower E L
  have := universeZeroAlgebra_isScalarTower_tower F E L
  have := universeZeroAlgebra_finiteDimensional F E
  have := universeZeroAlgebra_finiteDimensional F L
  have := universeZeroAlgebra_isAbelianGalois F L
  let TF₀ := (universeZeroModel F).canonicalTopologicalData
  obtain ⟨rE₀, rL₀, hres₀⟩ :=
    H p (universeZeroModel F) (universeZeroModel E) (universeZeroModel L) TF₀
  let := TF₀.topology
  let := TF.topology
  have : IsAbelianGalois F.Carrier E.Carrier :=
    IsAbelianGalois.tower_bot F.Carrier E.Carrier L.Carrier
  have : IsAbelianGalois (universeZeroModel F).Carrier (universeZeroModel E).Carrier :=
    IsAbelianGalois.tower_bot (universeZeroModel F).Carrier (universeZeroModel E).Carrier
      (universeZeroModel L).Carrier
  let QE := universeZeroNormQuotientEquiv F E TF₀ TF
  let QL := universeZeroNormQuotientEquiv F L TF₀ TF
  let gE := universeZeroGaloisEquiv F E
  let gL := universeZeroGaloisEquiv F L
  refine ⟨QE.symm.trans (rE₀.trans gE), QL.symm.trans (rL₀.trans gL), fun a => ?_⟩
  change AlgEquiv.restrictNormalHom (F := F.Carrier) (K₁ := L.Carrier) E.Carrier
      (gL (rL₀ (QL.symm (QuotientGroup.mk a)))) = gE (rE₀ (QE.symm (QuotientGroup.mk a)))
  rw [universeZeroGaloisEquiv_restrictNormalHom F E L]
  exact congrArg gE
    (hres₀ (Units.mapEquiv (universeZeroEquiv F).toRingEquiv.symm.toMulEquiv a))

end Langlands.LocalClassField.NYLL
