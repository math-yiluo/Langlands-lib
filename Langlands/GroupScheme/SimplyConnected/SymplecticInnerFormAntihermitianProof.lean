import Langlands.GroupScheme.SimplyConnected.SymplecticInnerFormAntihermitianStatement
import Langlands.GroupScheme.SymplecticInnerForm.GroupDescent
import Langlands.GroupScheme.SymplecticInnerForm.SymplecticInvolutionAntihermitian
import Langlands.GroupScheme.SymplecticInnerForm.AlgebraTransport

/-! # Symplectic inner forms are groups of antihermitian division forms -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

open SymplecticInnerForm

/-- Every inner form of a split symplectic group is the symplectic group of a
trace-valued antihermitian form over a central division algebra. -/
theorem symplecticInnerFormAntihermitian :
    SymplecticInnerFormAntihermitianStatement.{u} := by
  intro K _ G n q hn hq
  obtain ⟨A, _, _, _, _, _, _, τ, hτ, ⟨eG⟩⟩ :=
    symplecticInnerFormInvolution K G n q hn hq
  obtain ⟨L, _, _, _, _, e, he⟩ := hτ
  obtain ⟨degree, m, _, D, _, _, _, _, hd, hmd, hD, σ, hσ, H, hH, hunit, φ, hφ⟩ :=
    symplecticInvolutionAntihermitian K A τ n L e he
  exact ⟨degree, m, inferInstance, D, inferInstance, inferInstance, inferInstance,
    inferInstance, hd, hmd, hD, σ, hσ, H, hH, hunit,
    ⟨eG ≪≫ normOneGroupAlgEquivIso τ σ φ H hunit hφ⟩⟩

end Langlands.GroupScheme
