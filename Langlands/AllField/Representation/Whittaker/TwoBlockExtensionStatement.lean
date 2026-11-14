import Langlands.Representation.Whittaker.TwoBlockExtensionStatement
import Langlands.AllField.Representation.RankinSelberg.AnalyticStatementSupplement
import Langlands.AllField.Representation.Shahidi.Induction
/-!
# JPSS two-block Whittaker extension

Statement of JPSS Proposition 9.1, printed 452–454, for the actual canonical
normalized upper induction in the ordered blocks `(π₁, π₂)`. The second block
occurs in the leading coordinates of the evaluation formula.
-/

noncomputable section

namespace Langlands.AllField.Whittaker
open Langlands.Whittaker hiding TwoBlockWhittakerExtensionStatement
open Langlands.AllField.Whittaker

open Langlands.HarmonicAnalysis
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement QuotientHaarExistenceStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement normalizedAbsoluteValue normalizedAbsoluteValue_apply
open Langlands.AllField.RankinSelberg

universe uF uV₁ uV₂

/-- Every tail Whittaker coefficient times a Schwartz–Bruhat last-row cutoff,
with the positive half-modulus factor, extends to an actual Whittaker coefficient
of the canonical normalized upper two-block induction. This is a proposition
definition, not a proof of the extension. -/
def TwoBlockWhittakerExtensionStatement : Prop :=
  ∀ (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]
    (ψ : UnitaryAdditiveCharacter F)
    (a b : ℕ)
    {V₁ : Type uV₁} [AddCommGroup V₁] [Module ℂ V₁]
    {V₂ : Type uV₂} [AddCommGroup V₂] [Module ℂ V₂]
    (π₁ : Representation ℂ (Langlands.GeneralLinear (a + 1) F) V₁)
    (π₂ : Representation ℂ (Langlands.GeneralLinear (b + 1) F) V₂),
    (IsOfWhittakerType a (standardCharacter ψ a) π₁) →
    (IsOfWhittakerType b (standardCharacter ψ b) π₂) →
    let π₁' : Representation ℂ (Langlands.GeneralLinear (a + 1) F)
        (ULift.{uV₂} V₁) :=
      (ULift.moduleEquiv.symm.conjRingEquiv.toMonoidHom).comp π₁
    let π₂' : Representation ℂ (Langlands.GeneralLinear (b + 1) F)
        (ULift.{uV₁} V₂) :=
      (ULift.moduleEquiv.symm.conjRingEquiv.toMonoidHom).comp π₂
    let ξ := (⟨⟩ : LocalFieldData F).normalizedProductInduced
      (Shahidi.twoBlocks (a + 1) (b + 1) (Nat.succ_pos a) (Nat.succ_pos b))
      (Shahidi.pairFamily π₁' π₂')
    let e : Langlands.GeneralLinear (b + (a + 1) + 1) F ≃*
        Langlands.GeneralLinear ((a + 1) + (b + 1)) F :=
      GeneralLinear.reindex (finCongr (by omega))
    ∀ W₂ ∈ whittakerSet ψ b π₂,
      ∀ Φ : SchwartzBruhat (Fin (b + 1) → F),
        ∃ W ∈ whittakerSet ψ (a + 1 + b) ξ,
          ∀ g : Langlands.GeneralLinear (b + 1) F,
            W.val (e (appendIdentity b (a + 1) g)) =
              W₂.val g * Φ (lastRow g) *
                (Real.rpow ((⟨⟩ : LocalFieldData F).normalizedAbs (Matrix.det g.val))
                  (((a + 1 : ℕ) : ℝ) / 2) : ℂ)

end Langlands.AllField.Whittaker
