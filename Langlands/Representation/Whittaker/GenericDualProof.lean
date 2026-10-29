import Langlands.Representation.Whittaker.GenericDualStatement
import Langlands.Representation.Whittaker.GenericDualTransport
import Langlands.Representation.Smooth.Contragredient.GelfandKazhdanProof

/-!
# Genericity of the smooth contragredient

The published Gelfand–Kazhdan theorem supplies an inverse-transpose equivariant
equivalence to the actual smooth dual. Weyl translation transports the given
nonzero Whittaker functional to the inverse character on that dual.
-/

namespace Langlands

universe uF uV

/-- The smooth dual of a generic irreducible admissible representation is
realized by inverse transpose and is generic for the inverse character. -/
theorem genericContragredient : GenericContragredientStatement.{uF,uV} := by
  intro p hp F
  let := hp
  let := F.canonicalNormedField
  intro n V _ _ ρ ψ _hcontinuous _hnontrivial _hunitary hadm hirr hgen
  obtain ⟨E, hE⟩ := gelfandKazhdanContragredient p hp F n V ρ hadm hirr
  obtain ⟨ℓ, hℓ, hcov⟩ := hgen
  constructor
  · refine ⟨E, ?_⟩
    intro g v
    have hmatrix :
        Matrix.GeneralLinearGroup.mkOfDetNeZero (g⁻¹).val.transpose
          (by simpa only [Matrix.det_transpose] using
            Matrix.GeneralLinearGroup.det_ne_zero (g⁻¹)) =
        GeneralLinear.inverseTranspose (n + 1) F.Carrier g := by
      apply Units.ext
      rfl
    change E (ρ (Matrix.GeneralLinearGroup.mkOfDetNeZero _ _) v) = _
    rw [hmatrix]
    exact hE g v
  · exact ⟨Whittaker.explicitSmoothDualFunctional ρ E ℓ,
      Whittaker.explicitSmoothDualFunctional_ne_zero ρ E ℓ hℓ,
      Whittaker.explicitSmoothDualFunctional_covariance ρ E hE ψ ℓ hcov⟩

end Langlands
