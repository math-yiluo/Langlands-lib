import Langlands.Automorphic.DeterminantMultipleSpectrum
import Langlands.Automorphic.Unramified.IsobaricWeilAssociation
import Langlands.ClassField.Global.RelativeWeilUnramifiedTwist

/-! # Weak association passes to twists by every Hecke character

If `S` is weakly associated with the spectral system of a presentation of `T`, and the
realization of `T'` is the determinant multiple of that of `T` by a Hecke character `χ`,
then `(χ ∘ τ_F) ⊗ S` is weakly associated with the spectral system of every presentation
of `T'`.
-/

noncomputable section

universe u uV uP uQ

namespace Langlands.ClassField.Global.RelativeWeilGroup

/-- Henniart (2000), §2.2: weak association passes to twists by every Hecke character,
read through any presentation of the twisted realization. -/
theorem presentedDeterminantMultipleAssociation :
    PresentedDeterminantMultipleAssociationStatement.{u, uV, uP, uQ} := by
  intro c hc F E _ _ _ _ _ _ _ r S T T' P P' χ hTT' hS
  obtain ⟨_, -, -, h, -⟩ := hc
  exact (hS.twist_scale h χ).of_sameEulerPolynomials
    (Automorphic.CuspidalOperatorRealization.sameEulerPolynomials_scale_of_isDeterminantMultiple
      T T' P P' hTT')

end Langlands.ClassField.Global.RelativeWeilGroup
