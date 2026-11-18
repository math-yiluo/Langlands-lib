import Langlands.BushnellKutzko.ElementFieldInvariants

/-! # Invariants of equivalent strata (BK93 (1.5.2), (2.1.4); T5) -/

open ValuativeRel

namespace Langlands.BushnellKutzko

universe uF uV

/-- **BK93 (1.5.2), p. 43, and (2.1.4), p. 50 (T5).**
Equivalent strata have the same order and depth, and the same level when their
parameters have exact level. For simple strata the centralizer-order residue lattice,
critical exponent, ramification index and residue degree also agree. -/
def StratumEquivalenceStatement : Prop :=
  ∀ (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (V : Type uV) [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (S T : Stratum 𝒪[F] F V),
    S.Equivalent T →
      S.chain.order = T.chain.order ∧ S.r = T.r ∧
      ((S.chain.valuation S.b = (-S.n : WithTop ℤ) ∧
        T.chain.valuation T.b = (-T.n : WithTop ℤ)) → S.n = T.n) ∧
      (S.IsSimple → T.IsSimple →
        centralizerLattice S.chain S.b 0 ⊔ S.chain.endFiltration 1 =
          centralizerLattice T.chain T.b 0 ⊔ T.chain.endFiltration 1 ∧
        criticalExponent S.chain S.b = criticalExponent T.chain T.b ∧
        elementRamificationIndex F S.b = elementRamificationIndex F T.b ∧
        elementResidueDegree F S.b = elementResidueDegree F T.b)

end Langlands.BushnellKutzko
