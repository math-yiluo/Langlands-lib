import Langlands.BushnellKutzko.ClassCoverDecomposition

/-! # Covering simple-character classes: assembly of the reduction -/

open ValuativeRel

namespace Langlands.BushnellKutzko

universe uF uV

/-- `FibreCharacterAt` (the quotient of two extensions, from the proof of BK94 (2.7)) at every
depth. -/
def SimpleCharacterFibreCharacterStatement : Prop :=
  ∀ (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (V : Type uV) [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (ψF : AddChar F ℂ), IsBKAdditiveCharacter ψF →
    ∀ (L : LatticeChain 𝒪[F] F V) (n : ℤ) (k : ℕ), (k : ℤ) + 1 < n →
      FibreCharacterAt ψF L n k

/-- `RefinementSimpleAt` (BK93 (2.2.8), (2.4.1), BK94 (1.8)) at every depth. -/
def SimpleStratumScalarRefinementStatement : Prop :=
  ∀ (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (V : Type uV) [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (L : LatticeChain 𝒪[F] F V) (n : ℤ) (k : ℕ), (k : ℤ) + 1 < n →
      RefinementSimpleAt L n k

/-- The fibre injection of BK94 (2.7)–(2.10) from the Library's statements on simple
characters, the fibre characters and the scalar refinement. -/
theorem simpleCharacterFibreInjection_of
    (hApprox : PureStratumSimpleApproximationStatement.{uF, uV})
    (hConj : SimpleCharacterConjugationStatement.{uF, uV})
    (hChoice : SimpleCharacterChoiceStatement.{uF, uV})
    (hGroups : SimpleStratumGroupPropertiesStatement.{uF, uV})
    (hRestr : SimpleCharacterRestrictionStatement.{uF, uV})
    (hCoh : SimpleCharacterCoherenceStatement.{uF, uV})
    (hTransl : SimpleCharacterTranslationStatement.{uF, uV})
    (hCov : SimpleCharacterCovarianceStatement.{uF, uV})
    (hFib : SimpleCharacterFibreCharacterStatement.{uF, uV})
    (hRef : SimpleStratumScalarRefinementStatement.{uF, uV}) :
    SimpleCharacterFibreInjectionStatement.{uF, uV} := by
  intro F _ _ _ _ V _ _ _ ψF hψ L n k hk
  exact fibreInjectionAt_of_fibreClassInjection ψF hApprox hConj hChoice hGroups hRestr hCoh
    hTransl hψ L n k hk
    (fibreClassInjectionAt_of_twist ψF hGroups hRestr hψ L n k
      (twistConjugacyAt ψF hApprox hConj hChoice hCov hψ L n k hk)
      (fibreTwistCoverAt_of ψF hψ L n k (twistDecompositionAt ψF hApprox hChoice hRestr hψ L n k)
        (hFib F V ψF hψ L n k hk) (hRef F V L n k hk)))

/-- **BK94 (2.3), upper half,** from the Library's statements on simple strata and simple
characters, the fibre characters and the scalar refinement. -/
theorem simpleCharacterClassCover_of
    (hApprox : PureStratumSimpleApproximationStatement.{uF, uV})
    (hConj : SimpleCharacterConjugationStatement.{uF, uV})
    (hChoice : SimpleCharacterChoiceStatement.{uF, uV})
    (hGroups : SimpleStratumGroupPropertiesStatement.{uF, uV})
    (hRestr : SimpleCharacterRestrictionStatement.{uF, uV})
    (hCoh : SimpleCharacterCoherenceStatement.{uF, uV})
    (hTransl : SimpleCharacterTranslationStatement.{uF, uV})
    (hCov : SimpleCharacterCovarianceStatement.{uF, uV})
    (hFib : SimpleCharacterFibreCharacterStatement.{uF, uV})
    (hRef : SimpleStratumScalarRefinementStatement.{uF, uV}) :
    SimpleCharacterClassCoverStatement.{uF, uV} :=
  simpleCharacterClassCover_of_fibreInjection hApprox hConj hChoice hGroups hRestr
    (simpleCharacterFibreInjection_of hApprox hConj hChoice hGroups hRestr hCoh hTransl hCov
      hFib hRef)

end Langlands.BushnellKutzko
