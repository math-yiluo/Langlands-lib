import Langlands.Representation.Classification.MoeglinWaldspurgerInert
import Langlands.Representation.Classification.MoeglinWaldspurgerZelevinskySocle
import Langlands.Representation.Classification.MoeglinWaldspurgerTopCompatibility
import Langlands.Representation.Classification.MoeglinWaldspurgerChainCompatibility

/-!
# Aubert correctness of the MW recursion from the two representation-theoretic interfaces

The concrete highest left derivative relation `LDrel` satisfies the five derivative facts,
assuming the left cuspidal derivative lemma and the Langlands subrepresentation realization;
together with the two proved combinatorial compatibilities this gives the published universal
Aubert-correctness target.
-/

noncomputable section

namespace Langlands.MoeglinWaldspurger.Derivation

open Langlands.Classification Langlands.Classification.LeftCuspidalDerivative
open Aubert.SegmentPolynomialSurjectivity

universe uF uV

/-- The five derivative facts for the concrete relation `LDrel`. -/
theorem derivativeFacts_LDrel (hL : LeftCuspidalDerivativeLemma.{uF, uV})
    (hLS : LanglandsSubrepresentationRealization.{uF, uV})
    {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)
    (ρ : T.CuspidalDatum.{max uF uV, uF}) (x : ℝ) :
    DerivativeFacts F T ρ x (LDrel F T ρ x) where
  unique c _ _ cls cls' K S h₁ h₂ := LDrel_unique.{uF, uV} F T ρ x hL c cls cls' K S h₁ h₂
  unblocked b c htwo hu _ _ cls S hb hS :=
    unblocked_LDrel.{uF, uV} ρ x hL hLS b c htwo hu cls S hb hS
  inert b c δ hδ _ _ _ _ clsJ SJ cls S K hJ hδS hLD hb hS :=
    inert_LDrel.{uF, uV} ρ x hL hLS b c δ hδ clsJ SJ cls S K hJ hδS hLD hb hS
  zmax β y hβ _ _ cls S hcls hS := zmax_LDrel.{uF, uV} ρ x hL β y hβ cls S hcls hS
  zsocle I ν ν' hν hν' _ _ _ _ cls₁ S₁ cls S K h₁ hLD hS₁ hcls hS :=
    zsocle_LDrel.{uF, uV} ρ x hL I ν ν' hν hν' cls₁ S₁ cls S K h₁ hLD hS₁ hcls hS

/-- **Aubert correctness of the MW recursion, conditional on the two interfaces.** -/
theorem universalAubertCorrectness_of_interfaces (hL : LeftCuspidalDerivativeLemma.{uF, uV})
    (hLS : LanglandsSubrepresentationRealization.{uF, uV}) :
    UniversalAubertCorrectness.{uF, uV} :=
  universalAubertCorrectness_of_labelCorrectness fun _ _ F T =>
    labelCorrectness_of_derivativeFacts
      (fun ρ x => ⟨LDrel F T ρ x, derivativeFacts_LDrel hL hLS F T ρ x⟩)
      topUnmatchedCompatibility chainUnmatchedCompatibility

end Langlands.MoeglinWaldspurger.Derivation
