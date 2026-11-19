import Langlands.Algebra.SemisimpleScalarExtensionProof
import Langlands.GroupScheme.Reductive.SemisimpleFieldExtensionReduction

/-! # Simple and semisimple representations under extension of the base field -/

namespace Langlands.GroupScheme

universe u

/-- Milne, *Algebraic Groups* (2017), Proposition 4.19. -/
theorem semisimpleRepresentationFieldExtension :
    SemisimpleRepresentationFieldExtensionStatement.{u} :=
  semisimpleRepresentationFieldExtension_of_algebra
    (Langlands.Algebra.semisimpleScalarExtension.{u,u,u})

end Langlands.GroupScheme
