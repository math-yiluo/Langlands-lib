import Langlands.BushnellKutzko.DefiningSequence
import Langlands.BushnellKutzko.ElementFieldInvariants

/-! # Corestriction congruence for equivalent simple strata (BK93 (2.4.1)(ii)(c), p. 65) -/

noncomputable section

open ValuativeRel

namespace Langlands.BushnellKutzko

universe uF uV

/-- **BK93 (2.4.1)(ii)(c), printed p. 65.** If `[𝔄,n,r,γ₁]` and `[𝔄,n,r,γ₂]` are
equivalent simple strata and `s₁` is a tame corestriction relative to `F[γ₁]/F`, then
`s₁(γ₁ − γ₂) ≡ δ (mod 𝔓^{1−r})` for some `δ ∈ F[γ₁]`. -/
def SimpleStratumCorestrictionCongruenceStatement : Prop :=
  ∀ (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (V : Type uV) [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (S T : Stratum 𝒪[F] F V),
      T.chain = S.chain → T.n = S.n → T.r = S.r →
      S.IsSimple → T.IsSimple → S.Equivalent T →
      ∀ h : IsField (elementAlgebra S.b),
        letI := h.toField
        ∀ s : TameCorestriction 𝒪[F] F (elementAlgebra S.b) V,
          ∃ δ : elementAlgebra S.b,
            (s (S.b - T.b)).restrictScalars F -
                subfieldEmbedding F (elementAlgebra S.b) V δ ∈
              S.chain.endFiltration (1 - S.r)

end Langlands.BushnellKutzko
