import Langlands.ClassFieldTheory.Local.UniverseZero.RamifiedResidueStatement
import Langlands.ClassFieldTheory.Local.UniverseZero.FiniteInertiaFieldUnramifiedProof
import Langlands.ClassFieldTheory.Local.UniverseZero.FiniteInertiaResidueMapProof
import Langlands.ClassFieldTheory.Local.UniverseZero.FiniteInertiaResidueRestrictionProof
import Langlands.ClassFieldTheory.Local.Supplied.SuppliedInverseResiduePowerProof

/-! # Geometric residue normalization at ramified finite abelian levels -/

namespace Langlands.LocalClassField.UniverseZero

universe u v

theorem ramifiedGeometricNormalizationTransfer :
    RamifiedGeometricNormalizationTransferStatement.{u, v} := by
  intro p hp F E alg tower ab TF TU TE Artin
  let := finiteInertiaField_isAbelianGalois F E TF
  intro normalization familyRestriction a ha
  have hU :
      ∀ y : TU.ResidueField,
        (Ramification.Padic.residueHom TU F.Carrier
          (finiteInertiaRestriction F E TF (Artin E TE a)))⁻¹ y =
        y ^ TF.residueCardinality := by
    apply (suppliedInverseResiduePower F (finiteInertiaPadicField F E TF) TU
      (finiteInertiaRestriction F E TF (Artin E TE a)) TF.residueCardinality).mpr
    have hnormalization := normalization (finiteInertiaPadicField F E TF) TU
      (finiteInertiaFieldUnramified F E TF TU) a ha
    have hfamily := DFunLike.congr_fun familyRestriction a
    simp only [MonoidHom.comp_apply] at hfamily
    rw [hfamily]
    exact hnormalization
  apply (suppliedInverseResiduePower F E TE (Artin E TE a) TF.residueCardinality).mp
  intro z
  obtain ⟨y, rfl⟩ := (finiteInertiaResidueMapBijective F E TF TU TE).surjective z
  calc
    (Ramification.Padic.residueHom TE F.Carrier (Artin E TE a))⁻¹
        (finiteInertiaResidueMap F E TF TU TE y) =
        finiteInertiaResidueMap F E TF TU TE
          ((Ramification.Padic.residueHom TU F.Carrier
            (finiteInertiaRestriction F E TF (Artin E TE a)))⁻¹ y) := by
      simpa only [map_inv] using
        (finiteInertiaResidueRestriction F E TF TU TE (Artin E TE a)⁻¹ y).symm
    _ = finiteInertiaResidueMap F E TF TU TE (y ^ TF.residueCardinality) :=
      congrArg (finiteInertiaResidueMap F E TF TU TE) (hU y)
    _ = (finiteInertiaResidueMap F E TF TU TE y) ^ TF.residueCardinality :=
      map_pow (finiteInertiaResidueMap F E TF TU TE) y TF.residueCardinality

end Langlands.LocalClassField.UniverseZero
