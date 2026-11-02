import Langlands.Global.Factors.HeckeTwistComparisonStatement
import Langlands.Global.Factors.GermRationalComparisonStatement
import Langlands.Automorphic.AssociatedDeterminantTwistStatement
import Langlands.Automorphic.CuspidalSpectralDeterminantTwist

/-!
# Conditional comparison of actual relative-pair gamma certificates

The original local factors have separate certificates and rational
continuations. Every finite auxiliary factor is explicitly realized on actual
determinant-twisted presentations and arithmetic character twists. Analytic
comparison, preservation and stability remain individual hypotheses.
-/

noncomputable section

set_option autoImplicit false

universe u uV uP uQ uE

namespace Langlands.Global.FunctionalEquationComparison

open scoped NumberField
open Langlands.Global.AdelicFunctoriality Langlands.Global.CompletionPadic
open Langlands.ClassField.Global Langlands.ClassField.Global.RelativeWeilGroup
open Langlands.ClassFieldTheory.Local

variable {F : Type u} [Field F] [NumberField F] (v : FinitePlace F)

/-- Supplied original gamma certificates for the two sides, with a finite
comparison family. The measures and both factor witnesses are actual data. -/
structure RelativeGammaComparisonData
    (ψ : Correspondence.NontrivialAdditiveCharacter (padicField v))
    (ν : Correspondence.LocalAdditiveHaarMeasure (padicField v))
    (eC : LocalFactor.CommonClosure.ReciprocityFamily (padicField v))
    (ε : LocalFactor.NonabelianSystem.Assignment.{u, uE} (padicField v))
    (hε : LocalFactor.NonabelianSystem.IsSystem (padicField v) eC ε)
    {r t : ℕ}
    (π : Correspondence.AutomorphicClass.{u, u} (padicField v) r.succPNat)
    (π' : Correspondence.AutomorphicClass.{u, u} (padicField v) t.succPNat)
    (X Y : Correspondence.LocalPairClass.{u, uV} (padicField v)) where
  badPlaces : Finset (FinitePlace F)
  selected_mem : v ∈ badPlaces
  depth : FinitePlace F → ℕ
  automorphicData : HeckeEulerFamily F
  arithmeticData : HeckeEulerFamily F
  automorphicGamma : RatFunc ℂ
  arithmeticGamma : RatFunc ℂ
  automorphic_spec : Correspondence.IsAutomorphicPairGammaFactor (padicField v)
    ψ ν π π' automorphicGamma
  arithmetic_spec : Correspondence.IsArithmeticPairGammaFactor (padicField v)
    eC ε hε ψ X Y arithmeticGamma
  automorphic_continuation :
    RankinSelberg.HasRationalContinuation
      (padicField v).canonicalTopologicalData.residueCardinality
      (automorphicData.localFactors 1 (.inr v)).gamma automorphicGamma
  arithmetic_continuation :
    RankinSelberg.HasRationalContinuation
      (padicField v).canonicalTopologicalData.residueCardinality
      (arithmeticData.localFactors 1 (.inr v)).gamma arithmeticGamma

/-- The original bad finite set includes every ramified canonical additive
component. Conductor zero alone does not assert epsilon-factor triviality. -/
def FiniteAdditiveSupport
    (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F))
    (B : Finset (FinitePlace F)) : Prop :=
  ∀ z ∉ B, ∃ ψz : Correspondence.NontrivialAdditiveCharacter (padicField z),
    IsCanonicalFiniteAdditiveComponent ψ z ψz ∧
      (padicField z).canonicalTopologicalData.additiveConductor ψz = 0

variable (c : FundamentalClass.ClassFamily.{u})
  (E : Type u) [Field E] [NumberField E] [Algebra F E] [IsGalois F E]
  [CompactSpace (AdeleQuotient F)]
  {r t : ℕ}
  (S S' : FiniteRepresentation.{0, u, uV} ℂ (RelativeWeilGroup c F E))
  (T : Automorphic.CuspidalOperatorRealization F r)
  (T' : Automorphic.CuspidalOperatorRealization F t)
  (P : Automorphic.CuspidalSpectralPresentation.{u, uQ} T)
  (P' : Automorphic.CuspidalSpectralPresentation.{u, uQ} T')

/-- Every finite factor in both families, including all auxiliary places, has
an actual certificate. The first presentation and arithmetic representation
are twisted, the second is retained. All local maps and measure/system
existence witnesses are explicit, with no assumed comparison between sides. -/
def FiniteTwistGammaRealizations
    (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F))
    (D A : HeckeEulerFamily F) : Prop :=
  ∀ (χ : HeckeCharacter F) (hχ : χ.HasFiniteOrder) (z : FinitePlace F),
    ∃ (hI : ((P.determinantTwist χ hχ).localComponent z).IsIrreducible)
      (hA : ((P.determinantTwist χ hχ).localComponent z).IsAdmissible)
      (hI' : (P'.localComponent z).IsIrreducible)
      (hA' : (P'.localComponent z).IsAdmissible)
      (w : FinitePlacesAbove E z)
      (e : LocalFactor.RankOne.ReciprocityCandidate (towerPadicField z w.1))
      (ι : Weil.Local.localWeilGroup (padicField z) →ₜ* RelativeWeilGroup c F E),
      IsLocalRelativeWeilMap z w.1 e ι ∧
    ∃ (ψz : Correspondence.NontrivialAdditiveCharacter (padicField z))
      (νz : Correspondence.LocalAdditiveHaarMeasure (padicField z))
      (eCz : LocalFactor.CommonClosure.ReciprocityFamily (padicField z))
      (εz : LocalFactor.NonabelianSystem.Assignment.{u, uE} (padicField z))
      (hεz : LocalFactor.NonabelianSystem.IsSystem (padicField z) eCz εz),
      IsCanonicalFiniteAdditiveComponent ψ z ψz ∧
      Correspondence.IsSelfDualMeasure (padicField z) ψz νz ∧
    ∃ G H : RatFunc ℂ,
      Correspondence.IsAutomorphicPairGammaFactor (padicField z) ψz νz
        (((P.determinantTwist χ hχ).localComponent z).padicClass hI hA)
        ((P'.localComponent z).padicClass hI' hA') G ∧
      Correspondence.IsArithmeticPairGammaFactor (padicField z) eCz εz hεz ψz
        (localPairClass (FiniteRepresentation.twist (reciprocityCharacter c F E χ) S) ι)
        (localPairClass S' ι) H ∧
      RankinSelberg.HasRationalContinuation
        (padicField z).canonicalTopologicalData.residueCardinality
        (D.localFactors χ (.inr z)).gamma G ∧
      RankinSelberg.HasRationalContinuation
        (padicField z).canonicalTopologicalData.residueCardinality
        (A.localFactors χ (.inr z)).gamma H

/-- A derived conditional adapter in the full context of the existing
AssociatedGammaStatement. It retains individually the analytic, preservation,
stability, realization and existence inputs instead of asserting that global
Rankin--Selberg theory or the published AssociatedFactorStatement is proved. -/
def RelativeGammaComparisonStatement : Prop :=
  RamifiedTwistIsolationStatement.{u} →
  ∀ c : FundamentalClass.ClassFamily.{u}, IsArithmeticClassFamily c →
  ∀ (F E : Type u) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    [IsGalois F E] [CompactSpace (AdeleQuotient F)]
    (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F)),
    (∀ x : F, ψ (diagonal F x) = 1) →
  ∀ {r t : ℕ} (S S' : FiniteRepresentation.{0, u, uV} ℂ (RelativeWeilGroup c F E))
    (T : Automorphic.CuspidalOperatorRealization F r)
    (T' : Automorphic.CuspidalOperatorRealization F t),
    IsWeaklyAssociatedClass.{u, uV, uP} S T.isoClass →
    IsWeaklyAssociatedClass.{u, uV, uP} S' T'.isoClass →
  ∀ (P : Automorphic.CuspidalSpectralPresentation.{u, uQ} T)
    (P' : Automorphic.CuspidalSpectralPresentation.{u, uQ} T') (v : FinitePlace F)
    (hI : (P.localComponent v).IsIrreducible) (hA : (P.localComponent v).IsAdmissible)
    (hI' : (P'.localComponent v).IsIrreducible) (hA' : (P'.localComponent v).IsAdmissible)
    (w : FinitePlacesAbove E v)
    (e : LocalFactor.RankOne.ReciprocityCandidate (towerPadicField v w.1))
    (ι : Weil.Local.localWeilGroup (padicField v) →ₜ* RelativeWeilGroup c F E),
    IsLocalRelativeWeilMap v w.1 e ι →
  ∀ ψv : Correspondence.NontrivialAdditiveCharacter (padicField v),
    IsCanonicalFiniteAdditiveComponent ψ v ψv →
  ∀ (eC : LocalFactor.CommonClosure.ReciprocityFamily (padicField v))
    (ε : LocalFactor.NonabelianSystem.Assignment.{u, uE} (padicField v))
    (hε : LocalFactor.NonabelianSystem.IsSystem (padicField v) eC ε),
    (∃ ν : Correspondence.LocalAdditiveHaarMeasure (padicField v),
      Correspondence.IsSelfDualMeasure (padicField v) ψv ν) →
    (∀ ν : Correspondence.LocalAdditiveHaarMeasure (padicField v),
      Correspondence.IsSelfDualMeasure (padicField v) ψv ν →
      ∃ d : RelativeGammaComparisonData v ψv ν eC ε hε
        ((P.localComponent v).padicClass hI hA) ((P'.localComponent v).padicClass hI' hA')
        (localPairClass S ι) (localPairClass S' ι),
        FiniteAdditiveSupport ψ d.badPlaces ∧
        CommonTwistEulerInputs F d.badPlaces d.automorphicData d.arithmeticData ∧
        InfinityGammaPreservation F d.automorphicData d.arithmeticData ∧
        FiniteGammaPreservation F v d.automorphicData d.arithmeticData ∧
        RamifiedGammaStability F d.badPlaces d.depth d.automorphicData d.arithmeticData ∧
        OutsideGammaStability F d.badPlaces d.automorphicData d.arithmeticData ∧
        FiniteTwistGammaRealizations.{u, uV, uQ, uE} c E S S' T T' P P' ψ
          d.automorphicData d.arithmeticData) →
    IsPairGammaMatch.{u, uV, uE} (padicField v) eC ε hε ψv
      ((P.localComponent v).padicClass hI hA) ((P'.localComponent v).padicClass hI' hA')
      (localPairClass S ι) (localPairClass S' ι)

end Langlands.Global.FunctionalEquationComparison
