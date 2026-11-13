import Langlands.Representation.RankinSelberg.UnequalRankSourceLengthBoundStatement
import Langlands.AllField.Representation.RankinSelberg.UnequalRankBilinearUniquenessStatement
/-!
# Uniform source-carrier length bound for unequal-rank Whittaker-type data

An internal intermediate target for the full Whittaker-type
`UnequalRankBilinearUniquenessStatement`: outside finitely many spectral
values, the published space `unequalRankMirabolicForms` on the original
carriers has length at most one. The first representation is restricted to
its mirabolic subgroup; the second stays on `GL_(n+1)`. This is not the
irreducible Lemma or Proposition of JPSS p.399, and it is not proved here.
-/

noncomputable section

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding UnequalRankAnalyticStatement UnequalRankBilinearUniquenessStatement UnequalRankCommonGeneratorStatement UnequalRankSourceLengthBoundStatement normalizedAbsoluteValue normalizedAbsoluteValue_apply
open Langlands.AllField.RankinSelberg

open Langlands.HarmonicAnalysis

universe uF uV uW

/-- For Whittaker-type data, there is a finite set of spectral values
`q^(-s)` outside which the actual unequal-rank covariant forms on the
original carriers, with only the first representation restricted to its
mirabolic subgroup, form a complex module of length at most one. -/
def UnequalRankSourceLengthBoundStatement 
    (F : Type uF) [Field F] (T : LocalFieldData F) (n r : ℕ) : Prop :=
  letI := T.topology
  ∀ (hnr : n < r) (ψ : UnitaryAdditiveCharacter F)
    (V : Type uV) [AddCommGroup V] [Module ℂ V]
    (W : Type uW) [AddCommGroup W] [Module ℂ W]
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W),
    IsOfWhittakerType r (Whittaker.standardCharacter ψ r) π →
    IsOfWhittakerType n (Whittaker.inverseStandardCharacter ψ n) σ →
    ∃ E : Finset ℂ, ∀ s : ℂ, spectralPoint T.residueCardinality s ∉ E →
      Module.length ℂ (unequalRankMirabolicForms hnr ψ
        (normalizedAbsoluteValue T)
        (π.comp (GeneralLinear.mirabolic r F).subtype) σ s) ≤ 1

end Langlands.AllField.RankinSelberg
