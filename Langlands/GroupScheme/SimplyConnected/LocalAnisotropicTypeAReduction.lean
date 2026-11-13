import Langlands.GroupScheme.SimplyConnected.LocalAnisotropicAffineDiagramStatement
import Langlands.GroupScheme.SimplyConnected.AffineCartanTransitive

/-!
# Type `A_n` for anisotropic local groups from the affine-diagram input

This module proves `LocalAnisotropicTypeAStatement` from the single unproved input
`LocalAnisotropicAffineDiagramStatement`, which appears as an explicit hypothesis.
The combinatorial step is the proved theorem
`TitsIndexData.exists_equiv_cartanA_of_transitive_extension`.
-/

noncomputable section

universe u

namespace Langlands.GroupScheme

/-- An anisotropic absolutely almost-simple group over a nonarchimedean local field
has type `A_n` for some positive `n`, assuming the affine-diagram input
`LocalAnisotropicAffineDiagramStatement`. -/
theorem localAnisotropicTypeA_of_affineDiagram
    (h : LocalAnisotropicAffineDiagramStatement.{u}) :
    LocalAnisotropicTypeAStatement.{u} := by
  intro K _ _ _ _ G _ _ d hG hA
  obtain ⟨B, hB, hdiag, hoff, hsupp, ⟨m, hm, hker⟩, htrans⟩ := h K G d hG hA
  exact d.exists_equiv_cartanA_of_transitive_extension B hB (hdiag none) hoff
    (fun i j hij => (hsupp i j).mp hij) m hm hker htrans

end Langlands.GroupScheme
