import Langlands.Representation.Whittaker.MirabolicPairingStatement
import Langlands.AllField.Representation.RankinSelberg.AnalyticStatementSupplement
import Langlands.AllField.Representation.Whittaker.MirabolicPairingStatement
/-!
# Irreducible mirabolic functionals and twisted pairings

Proposition targets for the consequences of JPSS (1983), Proposition 1.4 and
Section 1.5, used in Section 2.10. No classification or proof is asserted here.
-/

noncomputable section

namespace Langlands.AllField.Whittaker
open Langlands.Whittaker hiding MirabolicCompactTwistedPairingStatement MirabolicFunctionalMultiplicityStatement MirabolicTwistedPairingRigidityStatement
open Langlands.AllField.Whittaker

open Langlands.GeneralLinear
open Langlands.HarmonicAnalysis
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement QuotientHaarExistenceStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement normalizedAbsoluteValue normalizedAbsoluteValue_apply
open Langlands.AllField.RankinSelberg

universe uF uV uW

/-- JPSS Section 1.5, Corollary 2: outside finitely many spectral values,
a nonzero twisted bilinear form on two irreducible smooth mirabolic
representations forces both to be equivalent to the actual compact model. -/
def MirabolicTwistedPairingRigidityStatement 
    (F : Type uF) [Field F] (T : LocalFieldData F) (n : ℕ) : Prop :=
  letI := T.topology
  letI : IsTopologicalRing F := by
    let := T.valuativeRel
    let := T.localField
    infer_instance
  ∀ ψ : UnitaryAdditiveCharacter F,
    ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V],
    ∀ (W : Type uW) [AddCommGroup W] [Module ℂ W],
    ∀ (ξ : Representation ℂ (mirabolic n F) V)
      (ξ' : Representation ℂ (mirabolic n F) W),
      IsSmooth ξ → Representation.IsIrreducible ξ →
      IsSmooth ξ' → Representation.IsIrreducible ξ' →
      ∃ E : Finset ℂ, ∀ s : ℂ, spectralPoint T.residueCardinality s ∉ E →
        ∀ β : InvariantBilinear.forms ξ ξ'
          (fun g => determinantWeight (normalizedAbsoluteValue T) g.val (-s)),
          β ≠ 0 →
            Nonempty (ξ.Equiv (mirabolicCompactInduced ψ n)) ∧
            Nonempty (ξ'.Equiv (mirabolicCompactInduced ψ n))

/-- The compact standard representation paired with itself has a nonzero,
exactly one-dimensional twisted form space for every exponent, as used in
JPSS Section 2.10, printed p.398. -/
def MirabolicCompactTwistedPairingStatement 
    (F : Type uF) [Field F] (T : LocalFieldData F) (n : ℕ) : Prop :=
  letI := T.topology
  letI : IsTopologicalRing F := by
    let := T.valuativeRel
    let := T.localField
    infer_instance
  ∀ (ψ : UnitaryAdditiveCharacter F) (s : ℂ),
    Nonempty ((InvariantBilinear.forms
      (mirabolicCompactInduced ψ n) (mirabolicCompactInduced ψ n)
      (fun g => determinantWeight (normalizedAbsoluteValue T) g.val (-s))) ≃ₗ[ℂ] ℂ)

end Langlands.AllField.Whittaker
