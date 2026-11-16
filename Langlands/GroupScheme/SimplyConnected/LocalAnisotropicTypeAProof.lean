import Langlands.GroupScheme.SimplyConnected.LocalAnisotropicTypeAReduction
import Langlands.GroupScheme.SimplyConnected.LocalAnisotropicAffineDiagramProof

/-!
# Anisotropic absolutely almost-simple groups over local fields have type `A_n`

Proof of `LocalAnisotropicTypeAStatement` (Kaletha–Prasad, Theorem 10.3.1). It applies
the published reduction `localAnisotropicTypeA_of_affineDiagram` to the published proof
`localAnisotropicAffineDiagram` of its only input, `LocalAnisotropicAffineDiagramStatement`.
-/

universe u

namespace Langlands.GroupScheme

/-- **Kaletha–Prasad, Theorem 10.3.1.** Over a nonarchimedean local field, the actual
index of an affine anisotropic absolutely almost-simple group has type `A_n` for some
positive `n`. -/
theorem localAnisotropicTypeA : LocalAnisotropicTypeAStatement.{u} :=
  localAnisotropicTypeA_of_affineDiagram localAnisotropicAffineDiagram

end Langlands.GroupScheme
