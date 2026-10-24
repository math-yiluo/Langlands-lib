import Langlands.Representation.RankinSelberg.PadicPairFactors
import Langlands.Representation.Shahidi.Induction
import Mathlib.Algebra.Module.ULift

/-!
# Tail L-polynomial divisibility for upper two-block induction

JPSS 1983, Lemma (9.3), printed pages 455–457, with the Whittaker-type extension
of its test representation explained in the paired Markdown from §§2.13, 3.1
and the proof of §9.3. The conclusion uses actual canonical normalized induction
from the upper parabolic in the order `(π₁, π₂)` and asserts `Ptail ∣ Pfull`.
The block carriers are explicitly lifted to a common universe before forming
their published block family; the original carriers have independent universes.
-/

noncomputable section

namespace Langlands.RankinSelberg

open HarmonicAnalysis Whittaker GeneralLinear Polynomial

universe uF uV₁ uV₂ uW

/-- The Whittaker-type extension of JPSS Lemma (9.3): the L-polynomial of the
second block against `σ` divides that of the canonical upper two-block induction
against `σ`. Both certified L-polynomials exist. The three positive ranks are
arbitrary, and no Whittaker-type or existence assumption is made on the induction.
The explicit `ULift` conjugations only place the two block carriers in a common
universe for the published finite block tensor construction. -/
def InducedTailLFactorStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p)
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ)
    (a b t : ℕ)
    {V₁ : Type uV₁} [AddCommGroup V₁] [Module ℂ V₁]
    {V₂ : Type uV₂} [AddCommGroup V₂] [Module ℂ V₂]
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (π₁ : Representation ℂ (Langlands.GeneralLinear (a + 1) F.Carrier) V₁)
    (π₂ : Representation ℂ (Langlands.GeneralLinear (b + 1) F.Carrier) V₂)
    (σ : Representation ℂ (Langlands.GeneralLinear (t + 1) F.Carrier) W),
    (letI := F.canonicalTopologicalData.topology;
      IsOfWhittakerType a (standardCharacter ψ a) π₁) →
    (letI := F.canonicalTopologicalData.topology;
      IsOfWhittakerType b (standardCharacter ψ b) π₂) →
    (letI := F.canonicalTopologicalData.topology;
      IsOfWhittakerType t (standardCharacter ψ t) σ) →
    let π₁' : Representation ℂ (Langlands.GeneralLinear (a + 1) F.Carrier)
        (ULift.{uV₂} V₁) :=
      (ULift.moduleEquiv.symm.conjRingEquiv.toMonoidHom).comp π₁
    let π₂' : Representation ℂ (Langlands.GeneralLinear (b + 1) F.Carrier)
        (ULift.{uV₁} V₂) :=
      (ULift.moduleEquiv.symm.conjRingEquiv.toMonoidHom).comp π₂
    ∃ Pfull Ptail : ℂ[X],
      IsPadicSymmetricLPolynomial F ψ ν.val
        (F.canonicalNormalizedProductInduced
          (Shahidi.twoBlocks (a + 1) (b + 1) (Nat.succ_pos a) (Nat.succ_pos b))
          (Shahidi.pairFamily π₁' π₂')) σ Pfull ∧
      IsPadicSymmetricLPolynomial F ψ ν.val π₂ σ Ptail ∧
      Ptail ∣ Pfull

end Langlands.RankinSelberg
