import Langlands.ClassFieldTheory.Local.FiniteReciprocityStatement
import Langlands.ClassFieldTheory.Local.UniverseZero.TypeZeroReciprocityProof
import Langlands.ClassFieldTheory.Local.UniverseZero.TypeZeroNormTransferProof
import Langlands.ClassFieldTheory.Local.UniverseZero.TypeZeroRestrictionProof
import Langlands.ClassFieldTheory.Local.UniverseZero.ReciprocityUniverseTransportProof
import Langlands.ClassFieldTheory.Local.UniverseZero.NormTransferUniverseTransportProof
import Langlands.ClassFieldTheory.Local.UniverseZero.RestrictionUniverseTransportProof

/-! # Finite abelian local reciprocity, norm, transfer and restriction -/

namespace Langlands.LocalClassField

universe u v w

/-- Finite abelian local reciprocity with geometric normalization and the inertia
clause, the norm and transfer diagrams and restriction compatibility, at arbitrary
independent field universes. -/
theorem finiteAbelianReciprocityTheorems : FiniteAbelianReciprocityTheorems.{u, v, w} :=
  ⟨UniverseZero.finiteAbelianReciprocityUniverseTransport UniverseZero.finiteAbelianReciprocityTypeZero,
    UniverseZero.finiteAbelianNormTransferUniverseTransport UniverseZero.finiteAbelianNormTransferTypeZero,
    UniverseZero.finiteAbelianRestrictionUniverseTransport UniverseZero.finiteAbelianRestrictionTypeZero⟩

end Langlands.LocalClassField
