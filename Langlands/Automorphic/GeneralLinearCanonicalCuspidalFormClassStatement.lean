import Langlands.Automorphic.GeneralLinearDiscreteCuspidalHeckeIsolationStatement

/-! # Square-integrability of descended general linear cusp forms

The existence of classes in canonical `L²([GL_{r+1}])` for a cuspidal realization that is
trivial on the positive split centre. This is the square-integrability and descent part of
Getz–Hahn, Theorem 9.7.3, on the canonical quotient of (2.20). -/

noncomputable section

open NumberField

set_option autoImplicit false

namespace Langlands.Automorphic.DiscreteHeckeIsolation

open Langlands.Global

/-- Every form of a cuspidal operator realization trivial on the positive split centre has a
class for the canonical measure on `[GL_{r+1}]`. -/
def GeneralLinearCanonicalCuspidalFormClassStatement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)] (r : ℕ)
    (S : CuspidalOperatorRealization F r), CuspidalPairPoles.IsTrivialOnSplitCentre S →
      ∀ f : S.Space, ∃ φ, IsCanonicalGeneralLinearFormClass F r φ (S.realization.toContinuous f)

end Langlands.Automorphic.DiscreteHeckeIsolation
