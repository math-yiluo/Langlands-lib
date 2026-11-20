import Langlands.BushnellKutzko.DefiningSequence

/-! # The derived stratum at the critical level (BK93 (2.4.1)(iii), printed p. 65) -/

noncomputable section

open ValuativeRel

namespace Langlands.BushnellKutzko

universe uF uV

/-- **BK93 (2.4.1)(iii), printed p. 65.** Let `[𝔄,n,r,β]` be pure with
`r = −k₀(β,𝔄)` and `[𝔄,n,r,γ]` an equivalent simple stratum. For every tame
corestriction `s_γ` relative to `F[γ]/F`, the derived stratum
`[𝔅_γ,r,r−1,s_γ(β−γ)]` is equivalent to a simple stratum over `F[γ]`. -/
def CriticalDerivedStratumStatement : Prop :=
  ∀ (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (V : Type uV) [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (S T : Stratum 𝒪[F] F V),
      S.IsPure → criticalExponent S.chain S.b = ((-S.r : ℤ) : WithBot ℤ) →
      T.chain = S.chain → T.n = S.n → T.r = S.r →
      T.IsSimple → S.Equivalent T → T.HasSimpleDerivedStratum (S.b - T.b)

end Langlands.BushnellKutzko
