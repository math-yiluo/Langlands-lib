import Langlands.ClassFieldTheory.Local.FiniteGeometricQuotient
import Langlands.ClassFieldTheory.Local.UniverseZero.TypeZeroStatement

/-! # The finite tower restriction diagram at field universes zero -/

namespace Langlands.LocalClassField.UniverseZero

open FiniteArtinSystemExistence

/-- The finite tower restriction diagram at field universes zero, with the
quotients of the Library's geometric finite Artin symbols. -/
theorem finiteAbelianRestrictionTypeZero : FiniteAbelianRestrictionTypeZeroStatement := by
  intro p _ F E L _ _ _ _ _ _ _ _ _ _ TF
  let := TF.topology
  have : IsAbelianGalois F.Carrier E.Carrier :=
    IsAbelianGalois.tower_bot F.Carrier E.Carrier L.Carrier
  obtain ⟨rE, hrE⟩ := exists_quotientEquiv_geometricSymbol F E.Carrier
    (continuous_geometricArtin F TF E E.canonicalTopologicalData)
  obtain ⟨rL, hrL⟩ := exists_quotientEquiv_geometricSymbol F L.Carrier
    (continuous_geometricArtin F TF L L.canonicalTopologicalData)
  refine ⟨rE, rL, fun a => ?_⟩
  rw [hrE, hrL]
  exact restrictNormalHom_geometricSymbol F L.Carrier E.Carrier a

end Langlands.LocalClassField.UniverseZero
