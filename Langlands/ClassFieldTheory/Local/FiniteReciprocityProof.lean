import Langlands.ClassFieldTheory.Local.FiniteReciprocityStatement
import Langlands.ClassFieldTheory.Local.NYLL.TypeZeroReciprocityProof
import Langlands.ClassFieldTheory.Local.NYLL.TypeZeroNormTransferProof
import Langlands.ClassFieldTheory.Local.NYLL.TypeZeroRestrictionProof
import Langlands.ClassFieldTheory.Local.NYLL.ReciprocityUniverseTransportProof
import Langlands.ClassFieldTheory.Local.NYLL.NormTransferUniverseTransportProof
import Langlands.ClassFieldTheory.Local.NYLL.RestrictionUniverseTransportProof

/-! # Finite abelian local reciprocity, norm, transfer and restriction -/

namespace Langlands.LocalClassField

universe u v w

/-- Finite abelian local reciprocity with geometric normalization and the inertia
clause, the norm and transfer diagrams and restriction compatibility, at arbitrary
independent field universes. -/
theorem finiteAbelianReciprocityTheorems : FiniteAbelianReciprocityTheorems.{u, v, w} :=
  ⟨NYLL.finiteAbelianReciprocityUniverseTransport NYLL.finiteAbelianReciprocityTypeZero,
    NYLL.finiteAbelianNormTransferUniverseTransport NYLL.finiteAbelianNormTransferTypeZero,
    NYLL.finiteAbelianRestrictionUniverseTransport NYLL.finiteAbelianRestrictionTypeZero⟩

end Langlands.LocalClassField
