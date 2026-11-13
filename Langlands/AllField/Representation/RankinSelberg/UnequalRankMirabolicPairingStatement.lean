import Langlands.Representation.RankinSelberg.UnequalRankMirabolicPairingStatement
import Langlands.AllField.Representation.RankinSelberg.UnequalRankBilinearUniquenessStatement
/-!
# Irreducible unequal-rank mirabolic pairings

The two conclusions of the Lemma in JPSS (1983), Section 2.11, printed
p.399, stated for the published actual covariance space. The parameter `s`
is the integral parameter; the source's twisted-pairing parameter is
`s - (r-n)/2`. These are proposition targets, with no proof or extension
to the full Whittaker-type uniqueness target.
-/

noncomputable section

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding UnequalRankAnalyticStatement UnequalRankBilinearUniquenessStatement UnequalRankCommonGeneratorStatement UnequalRankCompactGenericPairingStatement UnequalRankMirabolicPairingRigidityStatement normalizedAbsoluteValue normalizedAbsoluteValue_apply
open Langlands.AllField.RankinSelberg

open Langlands.HarmonicAnalysis

universe uF uV uW

/-- Outside a finite set of spectral values `q^(-s)`, a nonzero covariant
pairing between a smooth irreducible mirabolic representation and an
admissible irreducible smaller general linear representation forces the
compact standard model and an inverse-standard Whittaker functional. -/
def UnequalRankMirabolicPairingRigidityStatement 
    (F : Type uF) [Field F] (T : LocalFieldData F) (n r : ℕ) : Prop :=
  letI := T.topology
  letI : IsTopologicalRing F := by
    let := T.valuativeRel
    let := T.localField
    infer_instance
  ∀ hnr : n < r,
    ∀ ψ : UnitaryAdditiveCharacter F,
    ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V],
    ∀ (W : Type uW) [AddCommGroup W] [Module ℂ W],
    ∀ (ξ : Representation ℂ (GeneralLinear.mirabolic r F) V)
      (η : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W),
      IsSmooth ξ → Representation.IsIrreducible ξ →
      IsAdmissible η → Representation.IsIrreducible η →
      ∃ E : Finset ℂ, ∀ s : ℂ, spectralPoint T.residueCardinality s ∉ E →
        ∀ B : unequalRankMirabolicForms hnr ψ (normalizedAbsoluteValue T) ξ η s,
          B ≠ 0 →
            Nonempty (ξ.Equiv (Whittaker.mirabolicCompactInduced ψ r)) ∧
            Whittaker.HasFunctional
              (N := GeneralLinear.upperUnipotent (n + 1) F)
              (θ := Whittaker.inverseStandardCharacter ψ n) η

/-- For the actual compact mirabolic model and an admissible irreducible
smaller representation with an inverse-standard Whittaker functional,
the covariant pairing space is linearly equivalent to `ℂ` for every `s`. -/
def UnequalRankCompactGenericPairingStatement 
    (F : Type uF) [Field F] (T : LocalFieldData F) (n r : ℕ) : Prop :=
  letI := T.topology
  letI : IsTopologicalRing F := by
    let := T.valuativeRel
    let := T.localField
    infer_instance
  ∀ hnr : n < r,
    ∀ ψ : UnitaryAdditiveCharacter F,
    ∀ (W : Type uW) [AddCommGroup W] [Module ℂ W],
    ∀ η : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W,
      IsAdmissible η → Representation.IsIrreducible η →
      Whittaker.HasFunctional
        (N := GeneralLinear.upperUnipotent (n + 1) F)
        (θ := Whittaker.inverseStandardCharacter ψ n) η →
      ∀ s : ℂ,
        Nonempty
          ((unequalRankMirabolicForms hnr ψ (normalizedAbsoluteValue T)
            (Whittaker.mirabolicCompactInduced ψ r) η s) ≃ₗ[ℂ] ℂ)

end Langlands.AllField.RankinSelberg
