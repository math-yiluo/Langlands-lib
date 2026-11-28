import Langlands.BushnellKutzko.BetaExtension
import Langlands.BushnellKutzko.ElementFieldInvariants

/-! # Existence of `β`-extensions for a maximal order (BK93 (5.2.2)(i) for `𝔅` maximal) -/

open ValuativeRel

namespace Langlands.BushnellKutzko

universe uF uV uW

/-- **BK93 (5.2.2)(i) for a maximal order, via (5.2.3)(i) and (5.2.7).** Let `[𝔄, n, 0, β]` be a
simple stratum for which `𝔅 = 𝔄 ∩ End_{F[β]}(V)` is a maximal hereditary `𝔬_{F[β]}`-order, that is,
the period of the chain of `𝔄` equals the ramification index of `F[β]/F`. Then every
representation `η` of `J¹(β, 𝔄)` over a simple character `θ ∈ C(𝔄, 0, β)` has a `β`-extension. -/
def MaximalOrderBetaExtensionStatement : Prop :=
  ∀ (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (V : Type uV) [AddCommGroup V] [Module F V]
    (ψF : AddChar F ℂ), IsBKAdditiveCharacter ψF →
    ∀ (S : Stratum 𝒪[F] F V), S.r = 0 → S.IsSimple →
      S.chain.period = elementRamificationIndex F S.b →
    ∀ q : S.DefiningSequenceChoice,
    ∀ θ ∈ simpleCharacters ψF S.chain S.n S.b q.tail 0,
    ∀ (W : Type uW) [AddCommGroup W] [Module ℂ W]
      (η : Representation ℂ (simpleJGroup S.chain S.n S.b q.tail 1) W),
      IsHeisenbergRepresentation S.chain S.n S.b q.tail θ η →
      ∃ (d : ℕ) (κ : Representation ℂ (simpleJ S.chain S.n S.b q.tail) (Fin d → ℂ)),
        IsBetaExtension S.chain S.n S.b q.tail η κ

end Langlands.BushnellKutzko
