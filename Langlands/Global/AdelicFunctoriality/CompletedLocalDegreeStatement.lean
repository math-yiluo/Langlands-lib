import Langlands.Global.AdelicFunctoriality.Extension

/-! # A local arithmetic prerequisite for completed tensor comparison -/

namespace Langlands.Global.AdelicFunctoriality

open NumberField IsDedekindDomain
open scoped NumberField FiniteExtension

universe u v

/-- The ramification-inertia product of actual global primes is bounded by
the degree of the actual completed extension. -/
def CompletedLocalDegreeLowerBound : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L]
    (p : HeightOneSpectrum (𝓞 K)) (q : HeightOneSpectrum (𝓞 L))
    [q.asIdeal.LiesOver p.asIdeal],
    q.asIdeal.ramificationIdx (𝓞 K) * q.asIdeal.inertiaDeg (𝓞 K) ≤
      Module.finrank (p.adicCompletion K) (q.adicCompletion L)

end Langlands.Global.AdelicFunctoriality
