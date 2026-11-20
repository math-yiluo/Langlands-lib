import Langlands.BushnellKutzko.ElementFieldInvariants

/-! # Simple approximation of a pure stratum (BK93 (2.4.1)(i), printed p. 65) -/

noncomputable section

open ValuativeRel

namespace Langlands.BushnellKutzko

universe uF uV

/-- **BK93 (2.4.1)(i), printed p. 65, first two sentences.** Every pure stratum
`[𝔄,n,r,β]` is equivalent to a simple stratum `[𝔄,n,r,γ]` with the same chain and
integers, such that `e(F[γ]|F)` divides `e(F[β]|F)` and `f(F[γ]|F)` divides `f(F[β]|F)`. -/
def PureStratumSimpleApproximationStatement : Prop :=
  ∀ (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (V : Type uV) [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (S : Stratum 𝒪[F] F V), S.IsPure →
      ∃ T : Stratum 𝒪[F] F V,
        T.chain = S.chain ∧ T.n = S.n ∧ T.r = S.r ∧ T.IsSimple ∧ S.Equivalent T ∧
        elementRamificationIndex F T.b ∣ elementRamificationIndex F S.b ∧
        elementResidueDegree F T.b ∣ elementResidueDegree F S.b

end Langlands.BushnellKutzko
