import Langlands.GroupScheme.Torus.DiagonalizableActionNilpotentRigidity
import Langlands.GroupScheme.Torus.MultiplicativeTypeRigidityTranslation
import Langlands.GroupScheme.Torus.MultiplicativeTypeRigidityDescent

/-! # Infinitesimal rigidity for homomorphisms from multiplicative-type groups -/

universe u

namespace Langlands.GroupScheme

/-- Infinitesimal rigidity with an arbitrary target group scheme. -/
theorem multiplicativeTypeInfinitesimalRigidity :
    MultiplicativeTypeInfinitesimalRigidityStatement.{u} := by
  apply MultiplicativeTypeRigidity.of_diagonalizable
  intro A _ I hI G H f hH hf
  exact MultiplicativeTypeRigidity.diagonalizable_eq_one_of_action_rigidity f hH I hI
    (fun M _ a h => SchemeAction.hom_eq_snd_of_nilpotent_quotient a I hI h) hf

end Langlands.GroupScheme
