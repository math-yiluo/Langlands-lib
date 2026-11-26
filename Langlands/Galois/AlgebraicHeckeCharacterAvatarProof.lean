import Langlands.Galois.AlgebraicHeckeAvatarAssemblyProof
import Langlands.Galois.HeckeAvatarFinitePartProof
import Langlands.Galois.HeckeAvatarCorrectionProof
import Langlands.Galois.FiniteHeckeAvatarLiftProof
import Langlands.Galois.HeckeAvatarInverseLimitProof

/-! # Uniform adic avatars of algebraic CM Hecke characters -/

universe uK uL

namespace Langlands.GaloisRepresentation

/-- Every algebraic Hecke character of a CM field, of any weight, has a uniform family of
adic avatars: one coefficient number field with a complex embedding, one conductor support,
common Frobenius values, and a continuous adic character at every finite coefficient place. -/
theorem algebraicHeckeCharacterAvatar : AlgebraicHeckeCharacterAvatarStatement.{uK, uL} :=
  algebraicHeckeAvatarAssembly.{uK, uL} algebraicHeckeFinitePart.{uK, uL}
    heckeAvatarIdeleCorrection.{uK, uL} finiteGeometricArtinLifting.{uK, uL}
    heckeAvatarInverseLimit.{uK, uL}

end Langlands.GaloisRepresentation
