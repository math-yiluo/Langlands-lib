import Langlands.GroupScheme.ImageGenerationNoetherianStatement
import Langlands.GroupScheme.ImageGenerationNoetherian

/-! # Proof of the Noetherian finiteness inputs for image generation -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.ImageGeneration

/-- Antitone prime chains in Noetherian rings stabilize, and closed-immersion
endomorphisms of Noetherian affine schemes are isomorphisms. -/
theorem noetherianImageGenerationFiniteness :
    NoetherianImageGenerationFinitenessStatement.{u} := by
  refine ⟨?_, ?_⟩
  · intro A _ _ p hp hprime
    exact exists_forall_eq_of_antitone_isPrime p hp hprime
  · intro X _ _ φ hφ
    have := hφ
    exact isIso_of_isClosedImmersion_endo φ

end Langlands.GroupScheme.ImageGeneration
