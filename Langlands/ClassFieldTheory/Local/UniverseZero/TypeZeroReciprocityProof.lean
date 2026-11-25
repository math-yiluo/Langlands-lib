import Langlands.ClassFieldTheory.Local.FiniteGeometricQuotient
import Langlands.ClassFieldTheory.Local.UniverseZero.InertiaFromGeometricProof
import Langlands.ClassFieldTheory.Local.UniverseZero.TypeZeroStatement

/-! # Finite abelian local reciprocity at field universes zero -/

namespace Langlands.LocalClassField.UniverseZero

open FiniteArtinSystemExistence

/-- Finite abelian local reciprocity at field universes zero, with the quotient
of the Library's geometric finite Artin symbol as the reciprocity isomorphism. -/
theorem finiteAbelianReciprocityTypeZero : FiniteAbelianReciprocityTypeZeroStatement := by
  intro p _ F E _ _ _ _ TF TE
  let := TF.topology
  obtain ⟨r, hr⟩ := exists_quotientEquiv_geometricSymbol F E.Carrier
    (continuous_geometricArtin F TF E TE)
  have hgeom : ∀ a : F.Carrierˣ, TF.ord (a : F.Carrier) = 1 →
      ∀ x : E.Carrier, TE.discreteValuation x ≤ 1 →
        TE.discreteValuation
          ((r (QuotientGroup.mk a)).symm x - x ^ TF.residueCardinality) < 1 := by
    intro a ha x hx
    rw [hr a]
    exact ramified_normalization F TF E TE a ha x hx
  exact ⟨r, hgeom, inertiaFromGeometric p F E TF TE r.toMulEquiv hgeom⟩

end Langlands.LocalClassField.UniverseZero
