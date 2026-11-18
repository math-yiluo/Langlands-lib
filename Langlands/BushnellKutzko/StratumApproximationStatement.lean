import Langlands.BushnellKutzko.DefiningSequence
import Langlands.BushnellKutzko.ElementFieldInvariants

/-! # Approximation of pure strata (BK93 (2.4.1)–(2.4.2), pp. 65–66; T7) -/

noncomputable section

open ValuativeRel

namespace Langlands.BushnellKutzko

universe uF uV

/-- **BK93 (2.4.1), (2.4.2), printed pp. 65–66 (T7).**
Simple approximation, invariant divisibility and minimal degree; corestriction congruence;
simple approximation of the critical derived stratum; and defining-sequence existence.
Parts (2.4.1)(ii)(a),(b) are stated separately in T5. -/
def StratumApproximationStatement : Prop :=
  ∀ (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (V : Type uV) [AddCommGroup V] [Module F V] [FiniteDimensional F V],
    (∀ S : Stratum 𝒪[F] F V, S.IsPure →
      (∃ T : Stratum 𝒪[F] F V,
        T.chain = S.chain ∧ T.n = S.n ∧ T.r = S.r ∧ T.IsSimple ∧ S.Equivalent T) ∧
      (∀ T : Stratum 𝒪[F] F V,
        T.chain = S.chain → T.n = S.n → T.r = S.r →
        T.IsSimple → S.Equivalent T →
        elementRamificationIndex F T.b ∣ elementRamificationIndex F S.b ∧
        elementResidueDegree F T.b ∣ elementResidueDegree F S.b) ∧
      (∀ T : Stratum 𝒪[F] F V,
        T.chain = S.chain → T.n = S.n → T.r = S.r →
        T.IsPure → S.Equivalent T →
        (T.IsSimple ↔ ∀ U : Stratum 𝒪[F] F V,
          U.chain = S.chain → U.n = S.n → U.r = S.r →
          U.IsPure → S.Equivalent U → elementDegree F T.b ≤ elementDegree F U.b))) ∧
    (∀ S T : Stratum 𝒪[F] F V,
      T.chain = S.chain → T.n = S.n → T.r = S.r →
      S.IsSimple → T.IsSimple → S.Equivalent T →
      ∀ h : IsField (elementAlgebra S.b),
        letI := h.toField
        ∀ s : TameCorestriction 𝒪[F] F (elementAlgebra S.b) V,
          ∃ δ : elementAlgebra S.b,
            (s (S.b - T.b)).restrictScalars F -
                subfieldEmbedding F (elementAlgebra S.b) V δ ∈
              S.chain.endFiltration (1 - S.r)) ∧
    (∀ S T : Stratum 𝒪[F] F V,
      S.IsPure → criticalExponent S.chain S.b = ((-S.r : ℤ) : WithBot ℤ) →
      T.chain = S.chain → T.n = S.n → T.r = S.r →
      T.IsSimple → S.Equivalent T → T.HasSimpleDerivedStratum (S.b - T.b)) ∧
    (∀ S : Stratum 𝒪[F] F V, S.IsPure →
      ∃ (s : ℕ) (q : Fin (s + 1) → Stratum 𝒪[F] F V), S.IsDefiningSequence q)

end Langlands.BushnellKutzko
