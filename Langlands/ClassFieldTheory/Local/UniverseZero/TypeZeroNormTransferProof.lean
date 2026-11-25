import Langlands.ClassFieldTheory.Local.FiniteGeometricQuotient
import Langlands.ClassFieldTheory.Local.FiniteArtinNorm
import Langlands.ClassFieldTheory.Local.FiniteAbelianizedArtin
import Langlands.ClassFieldTheory.Local.UniverseZero.NormTransferReductionProof
import Langlands.ClassFieldTheory.Local.UniverseZero.TypeZeroStatement

/-! # The finite norm and transfer diagrams at field universes zero -/

namespace Langlands.LocalClassField.UniverseZero

open FiniteArtinSystemExistence Langlands.ClassFieldTheory.Local.FiniteArtinSymbol

open scoped IsMulCommutative in
/-- On a group with commutative multiplication, the abelianization map is injective. -/
theorem abelianization_of_injective_of_isMulCommutative {G : Type*} [Group G]
    [IsMulCommutative G] : Function.Injective (Abelianization.of : G →* Abelianization G) := by
  intro x y h
  have hx : Abelianization.lift (MonoidHom.id G) (Abelianization.of x) = x :=
    Abelianization.lift_apply_of _ x
  have hy : Abelianization.lift (MonoidHom.id G) (Abelianization.of y) = y :=
    Abelianization.lift_apply_of _ y
  rw [← hx, ← hy, h]

/-- The finite norm and transfer diagrams at field universes zero, with the
quotients of the Library's geometric finite Artin symbols over both base fields. -/
theorem finiteAbelianNormTransferTypeZero : FiniteAbelianNormTransferTypeZeroStatement := by
  intro p _ F E L _ _ _ _ _ _ _ _ _ _ _ TF TE
  let := TF.topology
  let := TE.topology
  have : IsAbelianGalois E.Carrier L.Carrier :=
    IsAbelianGalois.tower_top F.Carrier E.Carrier L.Carrier
  obtain ⟨rF, hrF⟩ := exists_quotientEquiv_geometricSymbol F L.Carrier
    (continuous_geometricArtin F TF L L.canonicalTopologicalData)
  obtain ⟨rE, hrE⟩ := exists_quotientEquiv_geometricSymbol E L.Carrier
    (continuous_geometricArtin E TE L L.canonicalTopologicalData)
  have hnorm : ∀ a : E.Carrierˣ,
      rF (QuotientGroup.mk (Units.map (Algebra.norm F.Carrier (S := E.Carrier)) a)) =
        (rE (QuotientGroup.mk a)).restrictScalars F.Carrier := by
    intro a
    rw [hrF, hrE, geometricSymbol_apply, geometricSymbol_apply]
    have h := abelianizedArtinSymbol_norm F E L.Carrier a⁻¹
    rw [abelianizedArtinSymbol_eq_of_comm, abelianizedArtinSymbol_eq_of_comm,
      Abelianization.map_of] at h
    have h' := abelianization_of_injective_of_isMulCommutative h
    rw [← map_inv (Units.map (Algebra.norm F.Carrier (S := E.Carrier))) a]
    exact h'.symm
  exact ⟨rF, rE, hnorm, normCompatibleTransfer p F E L TF TE rF rE hnorm⟩

end Langlands.LocalClassField.UniverseZero
