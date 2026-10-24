import Langlands.ClassField.Global.IdeleCohomology

/-! # Principal ideles integral and invertible at every finite place -/

universe u

namespace Langlands.ClassField.Global

open NumberField IsDedekindDomain
open scoped NumberField

/-- A principal idele is a valuation unit at every finite place precisely when its
field element comes from a unit of the ring of integers. -/
def PrincipalIdeleUnitCriterion : Prop :=
  ∀ (E : Type u) [Field E] [NumberField E] (a : Eˣ),
    (∀ w : HeightOneSpectrum (𝓞 E),
      Valued.v (ideleCoordinate w (IdeleGroup.unitEmbedding (𝓞 E) E a) :
        w.adicCompletion E) = 1) ↔
    ∃ ε : (𝓞 E)ˣ, Units.map (algebraMap (𝓞 E) E).toMonoidHom ε = a

end Langlands.ClassField.Global
