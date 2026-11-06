import Langlands.Correspondence.SupercuspidalEpsilonComparison
import Langlands.Correspondence.ArithmeticSystemComparison
import Langlands.Correspondence.RankOneComparison
import Langlands.Correspondence.AssemblyEpsilonSystemHelpers
import Langlands.ClassFieldTheory.Local.ReciprocitySystemUniquenessProof
import Langlands.HarmonicAnalysis.PadicUnitaryAdditiveCharacterExistsProof
import Langlands.LocalFactor.NonabelianUniquenessStatement

/-!
# Reducing supercuspidal correspondence uniqueness to two open inputs

The two correspondence witnesses may supply different reciprocity families,
base candidates and local-constant assignments. Published reciprocity
uniqueness compares their families. Same-family nonabelian uniqueness and
supercuspidal local converse remain explicit premises.
-/

noncomputable section

namespace Langlands.Correspondence

universe uF uP uA

open LocalFactor LocalFactor.CommonClosure

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

/-- An arithmetic epsilon comparison transports the certificates needed for
common tests even when the two correspondence families use different systems. -/
theorem commonSupercuspidalEpsilonFactors_of_arithmeticComparison
    {eC₁ eC₂ : ReciprocityFamily F}
    {ε₁ ε₂ : NonabelianSystem.Assignment.{uF, uP} F}
    {h₁ : NonabelianSystem.IsSystem F eC₁ ε₁}
    {h₂ : NonabelianSystem.IsSystem F eC₂ ε₂}
    (hcompare : ArithmeticPairEpsilonComparison F eC₁ ε₁ h₁ eC₂ ε₂ h₂)
    {c d : SupercuspidalMap.{uF, uP, uA} F}
    (hc : SupercuspidalPairFactorCompatibility F eC₁ ε₁ h₁ c)
    (hd : SupercuspidalPairFactorCompatibility F eC₂ ε₂ h₂ d)
    (ψ : NontrivialAdditiveCharacter F) (ν : LocalAdditiveHaarMeasure F)
    (hν : IsSelfDualMeasure F ψ ν) :
    CommonSupercuspidalEpsilonFactors F ψ ν c d := by
  intro k r hr σ τ
  obtain ⟨e, he, ha⟩ := ((hc ψ (k + 1) r σ τ).2 ν hν).2
  obtain ⟨e', he', ha'⟩ := ((hd ψ (k + 1) r σ τ).2 ν hν).2
  have ha₂ := (hcompare ψ (weilPairClass F σ) (weilPairClass F τ) e.1 e.2).mp ha
  have heq : e = e' := Prod.ext (ha₂.unique F ha').1 (ha₂.unique F ha').2
  exact ⟨e, he, heq ▸ he'⟩

/-- Uniqueness over one field follows from local converse and uniqueness of
actual local-constant assignments for each fixed supplied reciprocity family.
The correspondence premises supply surjectivity, rank-one compatibility,
pair-factor compatibility and self-dual measure existence. -/
theorem supercuspidalCorrespondenceUniqueness_of_nonabelianUniqueness
    (hconverse : RankinSelberg.SupercuspidalLocalConverseStatement.{uF, uA, uA})
    (hUnique : ∀ eC : ReciprocityFamily F, NonabelianSystem.Unique.{uF, uP} F eC) :
    SupercuspidalCorrespondenceUniqueness.{uF, uP, uA} F := by
  intro c d hc hd
  obtain ⟨ψ⟩ := HarmonicAnalysis.padicUnitaryAdditiveCharacterExists
    F F.canonicalTopologicalData
  obtain ⟨ν, hν⟩ := hc.exists_selfDualMeasure F ψ
  obtain ⟨hbij, _, e₁, _, hOne₁, _, _, eC₁, ε₁, h₁, hbase₁, hpairs₁⟩ := hc
  obtain ⟨_, _, e₂, _, hOne₂, _, _, eC₂, ε₂, h₂, hbase₂, hpairs₂⟩ := hd
  have hRec : ∀ a b : ReciprocityFamily F,
      NormalizedReciprocity F a → NormalizedReciprocity F b → a = b :=
    LocalClassField.commonClosureReciprocityUniqueness p F F.canonicalTopologicalData
  have heC : eC₁ = eC₂ := hRec eC₁ eC₂ h₁.1 h₂.1
  have he : e₁ = e₂ := hbase₁.candidate_eq_of_family_eq F hbase₂ heC
  have hOne : c 1 = d 1 := by
    apply supercuspidalRankOne_eq_of_compatibility F e₁ hOne₁
    exact he ▸ hOne₂
  have hcompare := arithmeticPairEpsilonComparison_of_uniqueness
    F hRec hUnique h₁ h₂
  exact supercuspidalMap_eq_of_commonEpsilonFactors F hconverse ψ ⟨ν, hν⟩
    hOne (fun n => (hbij n).2)
    (commonSupercuspidalEpsilonFactors_of_arithmeticComparison
      F hcompare hpairs₁ hpairs₂ ψ ν hν)

/-- Conditional all-field uniqueness, retaining independent field, parameter
and automorphic carrier universes. Neither antecedent is asserted here. -/
def SupercuspidalCorrespondenceUniquenessReductionStatement : Prop :=
  RankinSelberg.SupercuspidalLocalConverseStatement.{uF, uA, uA} →
    NonabelianSystemUniquenessStatement.{uF, uP} →
      ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p),
        SupercuspidalCorrespondenceUniqueness.{uF, uP, uA} F

/-- The two displayed all-field inputs suffice for uniqueness of the actual
supercuspidal maps; no correspondence existence is concluded. -/
theorem supercuspidalCorrespondenceUniquenessReduction :
    SupercuspidalCorrespondenceUniquenessReductionStatement.{uF, uP, uA} := by
  intro hconverse hUnique p _ F
  exact supercuspidalCorrespondenceUniqueness_of_nonabelianUniqueness
    F hconverse (hUnique p F)

/-- The published generation-to-system-uniqueness reduction gives the
alternative conditional input of actual common-closure degree-zero generation. -/
theorem supercuspidalCorrespondenceUniqueness_of_degreeZeroGeneration
    (hconverse : RankinSelberg.SupercuspidalLocalConverseStatement.{uF, uA, uA})
    (hgen : CommonClosureDegreeZeroGeneration.{uF, uP} F) :
    SupercuspidalCorrespondenceUniqueness.{uF, uP, uA} F :=
  supercuspidalCorrespondenceUniqueness_of_nonabelianUniqueness F hconverse
    (NonabelianSystem.unique_of_commonClosureDegreeZeroGeneration F hgen)

end Langlands.Correspondence
