import Langlands.BushnellKutzko.FormalIntertwining
import Langlands.BushnellKutzko.PureSimpleStratum

/-! # Formal intertwining and conjugacy of simple strata -/

open ValuativeRel

namespace Langlands.BushnellKutzko

universe uF uV

/-- BK93 (2.6.1), printed p. 83, and the same-order consequence of (2.3.2)
and (2.6.2), printed pp. 57 and 86. Formally intertwined simple strata of
the same order and levels are conjugate up to equivalence. A stratum of
depth `n − 1` equivalent to a simple one cannot intertwine with the null
stratum of the same order and levels. -/
def SimpleStratumConjugacyStatement : Prop :=
  ∀ (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (V : Type uV) [AddCommGroup V] [Module F V] [FiniteDimensional F V],
    (∀ (S T : Stratum 𝒪[F] F V),
      S.chain.order = T.chain.order → S.n = T.n → S.r = T.r →
      S.IsSimple → T.IsSimple → (T.formalIntertwining S).Nonempty →
      ∃ u ∈ S.chain.unitFiltration 0,
        (u : Module.End F V) * T.b * ↑(u⁻¹) ∈ S.coset) ∧
    (∀ (S T Z : Stratum 𝒪[F] F V),
      1 ≤ S.n → S.r = S.n - 1 → T.IsSimple → S.Equivalent T →
      Z.chain.order = S.chain.order → Z.n = S.n → Z.r = S.r → Z.b = 0 →
      ¬ (S.formalIntertwining Z).Nonempty)

end Langlands.BushnellKutzko
