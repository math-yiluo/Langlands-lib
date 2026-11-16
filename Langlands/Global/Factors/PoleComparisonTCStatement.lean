import Langlands.Global.Factors.RelativeCertifiedPoleComparisonsStatement
import Langlands.Global.Factors.RelativeIsometryFactorStatement
import Langlands.Global.Factors.HenniartCompositeMapStatement

/-!
# Totally complex forms of the relative pole comparisons, isometry factors and composite map

`RelativeCertifiedPoleComparisonsStatement`, `RelativeIsometryFactorStatement` and
`HenniartCompositeMapStatement`, each with the instance argument
`[NumberField.IsTotallyComplex F]` inserted after `[NumberField F]`, at the same universe
levels, the rest verbatim. Proposition definitions only. See the paired Markdown for the
reason and the sources.
-/

noncomputable section

universe uF uK uW uP uE

namespace Langlands.Global.PoleComparison

open Langlands.VirtualRepresentation Langlands.VirtualRepresentation.RelativeGlobal
open Langlands.Global.CompletionPadic Langlands.ClassField.Global
open Langlands.Global.AdelicFunctoriality

/-- The totally complex form of `RelativeCertifiedPoleComparisonsStatement` (Henniart 2000,
Corollaire 2.4 and Lemme 2.8, in the witnessed relative setting): the same statement for a
totally complex base field `F`; the rest is verbatim. -/
def RelativeCertifiedPoleComparisonsTCStatement : Prop :=
  ∀ (F E : Type uF) [Field F] [NumberField F] [NumberField.IsTotallyComplex F]
    [Field E] [NumberField E] [Algebra F E] [IsGalois F E] [CompactSpace (AdeleQuotient F)]
    (c : FundamentalClass.ClassFamily.{uF}),
    RelativeWeilGroup.IsArithmeticClassFamily c →
  ∀ (v : FinitePlace F) (ψ : Correspondence.NontrivialAdditiveCharacter (padicField v)),
    RelativeCertifiedPoleComparisons.{uF, uW, uP} F E c v ψ

/-- The totally complex form of `RelativeIsometryFactorStatement` (relative analogue of
Henniart 2000, Proposition 2.6 (a), determinant clause, and (b), factor clauses): the same
statement for a totally complex base field `F`; the rest is verbatim. -/
def RelativeIsometryFactorTCStatement : Prop :=
  ∀ (F E : Type uF) [Field F] [NumberField F] [NumberField.IsTotallyComplex F]
    [Field E] [NumberField E] [Algebra F E] [IsGalois F E] [CompactSpace (AdeleQuotient F)]
    (c : FundamentalClass.ClassFamily.{uF}),
    RelativeWeilGroup.IsArithmeticClassFamily c →
  ∀ (v : FinitePlace F) (ψ : Correspondence.NontrivialAdditiveCharacter (padicField v)),
    RelativeCertifiedPoleComparisons.{uF, uW, uP} F E c v ψ →
    ∀ T : weilImage.{uF, uW, uP} F E c v ≃ₗ[ℤ] automorphicImage.{uF, uW, uP} F E c v,
      RelativeGeneratedPositiveIsometry F E c v T →
      RelativeIsometryFactors.{uF, uW, uP, uE} F E c v T

/-- The totally complex form of `HenniartCompositeMapStatement` (Henniart 2000, 3.8): the same
statement for a totally complex base field `F`; the rest is verbatim. -/
def HenniartCompositeMapTCStatement : Prop :=
  ∀ (F E : Type uF) [Field F] [NumberField F] [NumberField.IsTotallyComplex F]
    [Field E] [NumberField E] [Algebra F E] [IsGalois F E] [CompactSpace (AdeleQuotient F)]
    (c : FundamentalClass.ClassFamily.{uF}),
    RelativeWeilGroup.IsArithmeticClassFamily c →
  ∀ (v : FinitePlace F) (ψ : Correspondence.NontrivialAdditiveCharacter (padicField v)),
    RelativeCertifiedPoleComparisons.{uF, uW, uP} F E c v ψ →
    ∀ T : weilImage.{uF, uW, uP} F E c v ≃ₗ[ℤ] automorphicImage.{uF, uW, uP} F E c v,
      RelativeGeneratedPositiveIsometry F E c v T →
      ∀ (p : ℕ) [Fact p.Prime] (h : residuePrime v = p) (K : PadicField.{uK} p)
        (f : letI := (padicFieldAt v h).algebra
          K.Carrier ≃ₐ[Padic p] (padicFieldAt v h).Carrier),
        Correspondence.LatticeMap.HenniartProperties.{uK, uW, uF, uE} K
          (henniartCompositeMap F E c v h K f T)

end Langlands.Global.PoleComparison
