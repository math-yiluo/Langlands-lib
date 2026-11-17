import Langlands.LocalFactor.Ramification.Herbrand.SubextensionProof
import Langlands.LocalField.Normalization.Definitions
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

/-!
# Kummer-step and Kummer-tower ramification statements

The six proposition definitions below concern the existing absolute upper
ramification groups and relative inverse Herbrand function. They include
non-Galois Kummer steps. No ramification assertion is proved here.
-/

noncomputable section

namespace Langlands.Ramification.Kummer

open LocalClassField HerbrandBridge
open _root_.Langlands.Ramification.Padic

universe u

section Definitions

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p)

/-- The actual simple intermediate field `F(α)`, with its finiteness certificate
from integrality in the algebraic closure. -/
def adjoinFiniteIntermediate (α : AlgebraicClosure F.Carrier) :
    FiniteIntermediateExtension F.Carrier :=
  ⟨IntermediateField.adjoin F.Carrier {α},
    IntermediateField.adjoin.finiteDimensional
      (Algebra.IsIntegral.isIntegral (R := F.Carrier) α)⟩

/-- The first Kummer break `p e / (p - 1)`, with all arithmetic in `ℝ`. -/
def kummerBreak : ℝ :=
  (p : ℝ) * (F.canonicalTopologicalData.ramificationIndex : ℝ) / ((p : ℝ) - 1)

/-- A uniformizer and a compatible sequence of its `p^n`-th roots in the
existing algebraic closure. -/
def IsKummerRootSystem (ϖ : F.Carrier) (πs : ℕ → AlgebraicClosure F.Carrier) : Prop :=
  F.canonicalTopologicalData.ord ϖ = 1 ∧
    πs 0 = algebraMap F.Carrier (AlgebraicClosure F.Carrier) ϖ ∧
    ∀ n : ℕ, πs (n + 1) ^ p = πs n

/-- The finite stage `K_n = F(πs n)` in the fixed algebraic closure. -/
def kummerStage (πs : ℕ → AlgebraicClosure F.Carrier) (n : ℕ) :
    FiniteIntermediateExtension F.Carrier :=
  adjoinFiniteIntermediate F (πs n)

/-- The supremum of the finite stages; for a compatible root system this
is the union of the increasing Kummer tower. -/
def kummerTower (πs : ℕ → AlgebraicClosure F.Carrier) :
    IntermediateField F.Carrier (AlgebraicClosure F.Carrier) :=
  ⨆ n : ℕ, (kummerStage F πs n).field

end Definitions

/-- The upper groups through the first Kummer break act transitively on the
embeddings of the degree-`p` step. This is a statement, not a theorem. -/
def KummerStepUpperSupStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p)
    (ϖ : F.Carrier) (α : AlgebraicClosure F.Carrier),
    F.canonicalTopologicalData.ord ϖ = 1 →
    α ^ p = algebraMap F.Carrier (AlgebraicClosure F.Carrier) ϖ →
    ∀ v : ℝ, -1 ≤ v → v ≤ kummerBreak F →
      (adjoinFiniteIntermediate F α).field.fixingSubgroup ⊔
        absoluteUpperRamificationGroup F v = ⊤

/-- The relative inverse Herbrand function of a Kummer step is the identity
through `p e / (p - 1)` and is `p x - p e` thereafter. -/
def KummerStepHerbrandPsiStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p)
    (ϖ : F.Carrier) (α : AlgebraicClosure F.Carrier),
    F.canonicalTopologicalData.ord ϖ = 1 →
    α ^ p = algebraMap F.Carrier (AlgebraicClosure F.Carrier) ϖ →
    (∀ x : ℝ, -1 ≤ x → x ≤ kummerBreak F →
      relativeHerbrandPsi (adjoinFiniteIntermediate F α) x = x) ∧
    (∀ x : ℝ, kummerBreak F ≤ x →
      relativeHerbrandPsi (adjoinFiniteIntermediate F α) x =
        (p : ℝ) * x - (p : ℝ) * (F.canonicalTopologicalData.ramificationIndex : ℝ))

/-- Transitivity at `μ` forces the relative inverse Herbrand function of a
finite subextension to be the identity on `[-1, μ]`. -/
def HerbrandPsiTruncationStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p)
    (E : FiniteIntermediateExtension F.Carrier) (μ : ℝ),
    E.field.fixingSubgroup ⊔ absoluteUpperRamificationGroup F μ = ⊤ →
    ∀ x : ℝ, -1 ≤ x → x ≤ μ → relativeHerbrandPsi E x = x

/-- The upper groups through the first Kummer break act transitively on
every finite stage, including stage zero. -/
def KummerTowerUpperSupStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p)
    (ϖ : F.Carrier) (πs : ℕ → AlgebraicClosure F.Carrier),
    IsKummerRootSystem F ϖ πs →
    ∀ (n : ℕ) (v : ℝ), -1 ≤ v → v ≤ kummerBreak F →
      (kummerStage F πs n).field.fixingSubgroup ⊔
        absoluteUpperRamificationGroup F v = ⊤

/-- The relative inverse Herbrand function of every finite Kummer stage
is the identity on the common interval `[-1, p e / (p - 1)]`. -/
def KummerTowerHerbrandPsiStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p)
    (ϖ : F.Carrier) (πs : ℕ → AlgebraicClosure F.Carrier),
    IsKummerRootSystem F ϖ πs →
    ∀ (n : ℕ) (x : ℝ), -1 ≤ x → x ≤ kummerBreak F →
      relativeHerbrandPsi (kummerStage F πs n) x = x

/-- The fixing subgroup of the infinite Kummer tower and an upper group
through the first Kummer break generate the whole absolute Galois group. -/
def KummerTowerLimitUpperSupStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p)
    (ϖ : F.Carrier) (πs : ℕ → AlgebraicClosure F.Carrier),
    IsKummerRootSystem F ϖ πs →
    ∀ v : ℝ, -1 ≤ v → v ≤ kummerBreak F →
      (kummerTower F πs).fixingSubgroup ⊔ absoluteUpperRamificationGroup F v = ⊤

end Langlands.Ramification.Kummer
