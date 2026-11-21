import Langlands.Automorphic.ConjugateContragredient
import Langlands.Automorphic.SquareIntegrableComponent
import Langlands.Global.Arithmetic.HarrisSetup

/-!
# Square-integrability at the CM-conjugate finite place

Use the local components of a single actual cuspidal spectral presentation
with irreducible admissible factors at every finite place. In particular an
arbitrary presentation of a finite-invariant slice is not sufficient.
-/

universe u uV

set_option autoImplicit false

open NumberField Langlands.Automorphic

namespace Langlands.Global.Harris

/-- For an irreducible admissible cuspidal factorization over a CM field,
square-integrability modulo the center at `v` transfers to the component at
its CM-conjugate place when the global realization is conjugate self-dual. -/
def HarrisSquareIntegrableConjPlaceStatement : Prop :=
  ∀ (E : Type u) [Field E] [NumberField E] [IsCMField E]
    [CompactSpace (AdeleQuotient E)] (r : ℕ) (S : CuspidalOperatorRealization E r)
    (P : CuspidalSpectralPresentation.{u, uV} S) (v : FinitePlace E),
    (∀ w : FinitePlace E,
      (P.localComponent w).IsIrreducible ∧ (P.localComponent w).IsAdmissible) →
    S.isoClass.IsConjugateSelfDual → (P.localComponent v).IsSquareIntegrable →
    (P.localComponent (conjPlace E v)).IsSquareIntegrable

end Langlands.Global.Harris
