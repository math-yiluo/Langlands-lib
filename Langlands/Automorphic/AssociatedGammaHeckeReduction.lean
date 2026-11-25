import Langlands.Automorphic.AssociatedFactorStatement
import Langlands.Global.Factors.HeckeTwistComparisonProof
import Langlands.Global.Factors.GermRationalComparisonProof
import Langlands.Global.Factors.RelativeGammaComparisonStatement
import Langlands.Global.Arithmetic.RamifiedTwistIsolationProof

/-!
# Pair gamma matching from two Hecke Euler families

A local gamma match at one finite place follows from an automorphic and an
arithmetic Hecke Euler family whose untwisted factors at that place continue
the two actual gamma factors, together with the five analytic, preservation
and stability inputs of the two-twist comparison engine.
-/

noncomputable section

set_option autoImplicit false

universe u uV uE

namespace Langlands.ClassFieldTheory.Global.RelativeWeilGroup

open Langlands.Global Langlands.Global.CompletionPadic
open Langlands.Global.FunctionalEquationComparison

/-- The data used for one self-dual measure: an original bad set containing `v`,
depths, both Hecke Euler families, both actual gamma factors with rational
continuations of the untwisted factors at `v`, and the five engine inputs. -/
def HasHeckeGammaCertificate {F : Type u} [Field F] [NumberField F] (v : FinitePlace F)
    (ψ : Correspondence.NontrivialAdditiveCharacter (padicField v))
    (ν : Correspondence.LocalAdditiveHaarMeasure (padicField v))
    (eC : LocalFactor.CommonClosure.ReciprocityFamily (padicField v))
    (ε : LocalFactor.NonabelianSystem.Assignment.{u, uE} (padicField v))
    (hε : LocalFactor.NonabelianSystem.IsSystem (padicField v) eC ε)
    {r t : ℕ}
    (π : Correspondence.AutomorphicClass.{u, u} (padicField v) r.succPNat)
    (π' : Correspondence.AutomorphicClass.{u, u} (padicField v) t.succPNat)
    (X Y : Correspondence.LocalPairClass.{u, uV} (padicField v)) : Prop :=
  ∃ (T : Finset (FinitePlace F)) (_ : v ∈ T) (depth : FinitePlace F → ℕ)
    (D A : HeckeEulerFamily F) (G H : RatFunc ℂ),
    Correspondence.IsAutomorphicPairGammaFactor (padicField v) ψ ν π π' G ∧
    Correspondence.IsArithmeticPairGammaFactor (padicField v) eC ε hε ψ X Y H ∧
    RankinSelberg.HasRationalContinuation
      (padicField v).canonicalTopologicalData.residueCardinality
      (D.localFactors 1 (.inr v)).gamma G ∧
    RankinSelberg.HasRationalContinuation
      (padicField v).canonicalTopologicalData.residueCardinality
      (A.localFactors 1 (.inr v)).gamma H ∧
    CommonTwistEulerInputs F T D A ∧
    InfinityGammaPreservation F D A ∧
    FiniteGammaPreservation F v D A ∧
    RamifiedGammaStability F T depth D A ∧
    OutsideGammaStability F T D A

/-- The two-twist engine and rational germ comparison turn a certificate for every
self-dual measure into the local pair gamma match. -/
theorem isPairGammaMatch_of_heckeGammaCertificate {F : Type u} [Field F] [NumberField F]
    (v : FinitePlace F)
    (ψ : Correspondence.NontrivialAdditiveCharacter (padicField v))
    (eC : LocalFactor.CommonClosure.ReciprocityFamily (padicField v))
    (ε : LocalFactor.NonabelianSystem.Assignment.{u, uE} (padicField v))
    (hε : LocalFactor.NonabelianSystem.IsSystem (padicField v) eC ε)
    {r t : ℕ}
    (π : Correspondence.AutomorphicClass.{u, u} (padicField v) r.succPNat)
    (π' : Correspondence.AutomorphicClass.{u, u} (padicField v) t.succPNat)
    (X Y : Correspondence.LocalPairClass.{u, uV} (padicField v))
    (hmeasure : ∃ ν : Correspondence.LocalAdditiveHaarMeasure (padicField v),
      Correspondence.IsSelfDualMeasure (padicField v) ψ ν)
    (hdata : ∀ ν : Correspondence.LocalAdditiveHaarMeasure (padicField v),
      Correspondence.IsSelfDualMeasure (padicField v) ψ ν →
      HasHeckeGammaCertificate.{u, uV, uE} v ψ ν eC ε hε π π' X Y) :
    IsPairGammaMatch.{u, uV, uE} (padicField v) eC ε hε ψ π π' X Y := by
  refine ⟨hmeasure, ?_⟩
  intro ν hν
  obtain ⟨T, hv, depth, D, A, G, H, hG, hH, hDG, hAH, hanalytic, hinf, hfinite, hram,
    hout⟩ := hdata ν hν
  obtain ⟨_, _, _, _, _, _, _, hgamma⟩ :=
    heckeTwistComparison Langlands.Global.ramifiedTwistIsolation F T v hv depth
      D A hanalytic hinf hfinite hram hout
  have hequal : G = H :=
    germRationalComparison _
      (padicField v).canonicalTopologicalData.residueCardinality_gt_one
      _ _ _ _ hDG hAH hgamma
  exact ⟨H, hequal ▸ hG, hH⟩

end Langlands.ClassFieldTheory.Global.RelativeWeilGroup
