import Langlands.ClassField.Global.IdeleDivisor
import Mathlib.RingTheory.DedekindDomain.Factorization

/-! # The divisor formula for principal ideles -/

universe u

namespace Langlands.ClassField.Global

open NumberField IsDedekindDomain
open scoped NumberField nonZeroDivisors

/-- The local order of a principal idele is the multiplicity of the corresponding
prime in its principal fractional ideal. -/
def PrincipalIdeleDivisorFormula : Prop :=
  ∀ (E : Type u) [Field E] [NumberField E]
    (w : HeightOneSpectrum (𝓞 E)) (a : Eˣ),
    ideleOrder w (IdeleGroup.unitEmbedding (𝓞 E) E a) =
      FractionalIdeal.count E w (FractionalIdeal.spanSingleton (𝓞 E)⁰ (a : E))

end Langlands.ClassField.Global
