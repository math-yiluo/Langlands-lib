import Langlands.Representation.RankinSelberg.AnalyticStatement
import Langlands.Representation.RankinSelberg.LocalFactor
import Langlands.Representation.Shahidi.Induction
import Mathlib.Algebra.Module.ULift

/-!
# JPSS two-block Whittaker extension

Statement of JPSS Proposition 9.1, printed 452–454, for the actual canonical
normalized upper induction in the ordered blocks `(π₁, π₂)`. The second block
occurs in the leading coordinates of the evaluation formula.
-/

noncomputable section

namespace Langlands.Whittaker

open HarmonicAnalysis RankinSelberg

universe uF uV₁ uV₂

/-- Every tail Whittaker coefficient times a Schwartz–Bruhat last-row cutoff,
with the positive half-modulus factor, extends to an actual Whittaker coefficient
of the canonical normalized upper two-block induction. This is a proposition
definition, not a proof of the extension. -/
def TwoBlockWhittakerExtensionStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p)
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (a b : ℕ)
    {V₁ : Type uV₁} [AddCommGroup V₁] [Module ℂ V₁]
    {V₂ : Type uV₂} [AddCommGroup V₂] [Module ℂ V₂]
    (π₁ : Representation ℂ (Langlands.GeneralLinear (a + 1) F.Carrier) V₁)
    (π₂ : Representation ℂ (Langlands.GeneralLinear (b + 1) F.Carrier) V₂),
    (letI := F.canonicalTopologicalData.topology;
      IsOfWhittakerType a (standardCharacter ψ a) π₁) →
    (letI := F.canonicalTopologicalData.topology;
      IsOfWhittakerType b (standardCharacter ψ b) π₂) →
    letI := F.canonicalTopologicalData.topology
    let π₁' : Representation ℂ (Langlands.GeneralLinear (a + 1) F.Carrier)
        (ULift.{uV₂} V₁) :=
      (ULift.moduleEquiv.symm.conjRingEquiv.toMonoidHom).comp π₁
    let π₂' : Representation ℂ (Langlands.GeneralLinear (b + 1) F.Carrier)
        (ULift.{uV₁} V₂) :=
      (ULift.moduleEquiv.symm.conjRingEquiv.toMonoidHom).comp π₂
    let ξ := F.canonicalNormalizedProductInduced
      (Shahidi.twoBlocks (a + 1) (b + 1) (Nat.succ_pos a) (Nat.succ_pos b))
      (Shahidi.pairFamily π₁' π₂')
    let e : Langlands.GeneralLinear (b + (a + 1) + 1) F.Carrier ≃*
        Langlands.GeneralLinear ((a + 1) + (b + 1)) F.Carrier :=
      GeneralLinear.reindex (finCongr (by omega))
    ∀ W₂ ∈ whittakerSet ψ b π₂,
      ∀ Φ : SchwartzBruhat (Fin (b + 1) → F.Carrier),
        ∃ W ∈ whittakerSet ψ (a + 1 + b) ξ,
          ∀ g : Langlands.GeneralLinear (b + 1) F.Carrier,
            W.val (e (appendIdentity b (a + 1) g)) =
              W₂.val g * Φ (lastRow g) *
                (Real.rpow (F.canonicalTopologicalData.normalizedAbs (Matrix.det g.val))
                  (((a + 1 : ℕ) : ℝ) / 2) : ℂ)

end Langlands.Whittaker
