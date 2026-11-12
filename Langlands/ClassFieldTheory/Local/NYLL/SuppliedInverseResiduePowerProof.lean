import Langlands.ClassFieldTheory.Local.NYLL.RamifiedResidueStatement
import Langlands.ClassFieldTheory.Local.NYLL.SuppliedResidueProof
import Langlands.HarmonicAnalysis.Conductor

/-! # Inverse supplied residue powers and valuation congruences -/

namespace Langlands.LocalClassField.NYLL

universe u v

/-- Inverse action on the supplied residue field is a power map exactly when
the inverse field automorphism satisfies the corresponding congruence. -/
theorem suppliedInverseResiduePower : SuppliedInverseResiduePowerStatement.{u, v} := by
  intro p _ F E _ _ TE σ q
  have representative (x : TE.Integers) :
      (Ramification.Padic.residueHom TE F.Carrier σ)⁻¹ (TE.residue x) =
          (TE.residue x) ^ q ↔
        TE.discreteValuation (σ.symm (x : E.Carrier) - (x : E.Carrier) ^ q) < 1 := by
    rw [← map_inv]
    change TE.residue (Ramification.Padic.integerAutomorphism TE F.Carrier σ⁻¹ x) =
        (TE.residue x) ^ q ↔ _
    rw [← map_pow]
    exact suppliedResidueCongruence E TE
      (Ramification.Padic.integerAutomorphism TE F.Carrier σ⁻¹ x) (x ^ q)
  constructor
  · intro h x hx
    let x' : TE.Integers :=
      ⟨x, (TE.mem_integers_iff_discreteValuation_le_one x).mpr hx⟩
    exact (representative x').mp (h (TE.residue x'))
  · intro h y
    obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective y
    exact (representative x).mpr
      (h x ((TE.mem_integers_iff_discreteValuation_le_one x).mp x.property))

end Langlands.LocalClassField.NYLL
