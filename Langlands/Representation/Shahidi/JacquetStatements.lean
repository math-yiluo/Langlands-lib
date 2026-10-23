import Langlands.Representation.Shahidi.JacquetInduced
import Langlands.Representation.RankinSelberg.Measures
import Langlands.Representation.Whittaker.Transport
import Langlands.HarmonicAnalysis.Conductor

/-!
# Stabilization, Whittaker uniqueness and existence of the local coefficient

The analytic assertions are proposition definitions. Only the algebraic passage
from multiplicity one and nonzero pullback to the inverse scalar is proved.
-/

noncomputable section

namespace Langlands.Shahidi

open Whittaker

universe uG uV uW

/-- The algebraic step in (0.3). Multiplicity one and a nonzero pullback give a
unique nonzero coefficient in the inverse convention. No analytic existence or
rational dependence is asserted by this lemma. -/
theorem existsUnique_inverseScalar_of_multiplicityOne
    {G : Type uG} [Group G] {N : Subgroup G} {θ : N →* ℂˣ}
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ G V} {σ : Representation ℂ G W}
    (A : ρ.IntertwiningMap σ) (Λ : functionals N θ ρ) (Λ' : functionals N θ σ)
    (hΛ : Λ.val ≠ 0) (hA : Λ'.val.comp A.toLinearMap ≠ 0)
    (hmult : ∀ L ∈ functionals N θ ρ, ∃ a : ℂ, L = a • Λ.val) :
    ∃! c : ℂ, c ≠ 0 ∧ Λ'.val.comp A.toLinearMap = c⁻¹ • Λ.val := by
  obtain ⟨a, ha⟩ := hmult _ (functionalsComap A Λ').property
  change Λ'.val.comp A.toLinearMap = a • Λ.val at ha
  have ha0 : a ≠ 0 := by
    intro h
    apply hA
    simpa [h] using ha
  refine ⟨a⁻¹, ⟨inv_ne_zero ha0, by simpa using ha⟩, ?_⟩
  intro c hc
  have heq : c⁻¹ • Λ.val = a • Λ.val := hc.2.symm.trans ha
  have hscalar : c⁻¹ = a := (smul_left_injective ℂ hΛ) heq
  exact inv_injective (by simpa using hscalar)

end Langlands.Shahidi

namespace Langlands.PadicField.TopologicalData

open Langlands.Shahidi MeasureTheory HarmonicAnalysis Whittaker RankinSelberg

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)
variable (m n : ℕ)

/-- Shahidi (1984), (0.2) and the paragraph after (1.1): both induced Jacquet
integrals stabilize, and define nonzero standard Whittaker functionals at every
complex parameter. The two Haar measures are kept explicit and independent. -/
def ShahidiJacquetStabilizationStatement : Prop :=
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  letI := borel F.Carrier
  ∀ (ψ : UnitaryAdditiveCharacter F.Carrier), T.additiveConductor ψ = 0 →
  ∀ (νJ νJ' : AdditiveHaarMeasure F.Carrier),
  ∀ (V₁ V₂ : Type uV) [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup V₂] [Module ℂ V₂]
    (π₁ : Representation ℂ (GeneralLinear (m + 1) F.Carrier) V₁)
    (π₂ : Representation ℂ (GeneralLinear (n + 1) F.Carrier) V₂),
    IsGeneric ψ m π₁ → IsGeneric ψ n π₂ →
    ∀ ℓ₁ ∈ glFunctionals ψ m π₁, ∀ ℓ₂ ∈ glFunctionals ψ n π₂,
      ℓ₁ ≠ 0 → ℓ₂ ≠ 0 → ∀ s : ℂ,
      (∃ Λ : T.ShahidiSourceSpace (Nat.add_one_pos m) (Nat.add_one_pos n) s π₁ π₂ →ₗ[ℂ] ℂ,
        T.IsSourceJacquetFunctional s π₁ π₂ ψ ℓ₁ ℓ₂
          (rectangularMeasure νJ (n + 1) (m + 1)) Λ ∧
        Λ ∈ glFunctionals ψ (m + 1 + n)
          (T.shahidiSource (Nat.add_one_pos m) (Nat.add_one_pos n) s π₁ π₂) ∧ Λ ≠ 0) ∧
      (∃ Λ' : T.ShahidiTargetSpace (Nat.add_one_pos m) (Nat.add_one_pos n) s π₁ π₂ →ₗ[ℂ] ℂ,
        T.IsTargetJacquetFunctional s π₁ π₂ ψ ℓ₁ ℓ₂
          (rectangularMeasure νJ' (m + 1) (n + 1)) Λ' ∧
        Λ' ∈ glFunctionals ψ (m + 1 + n)
          (T.shahidiTarget (Nat.add_one_pos m) (Nat.add_one_pos n) s π₁ π₂) ∧ Λ' ≠ 0)

/-- The induced multiplicity-one input behind (0.3): any nonzero standard
Whittaker functional spans the entire Whittaker space, for either induced
representation and every complex parameter. This is an analytic theorem target,
not an irreducibility assumption on the possibly reducible induced spaces. -/
def ShahidiInducedWhittakerMultiplicityOneStatement : Prop :=
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  ∀ (ψ : UnitaryAdditiveCharacter F.Carrier), T.additiveConductor ψ = 0 →
  ∀ (V₁ V₂ : Type uV) [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup V₂] [Module ℂ V₂]
    (π₁ : Representation ℂ (GeneralLinear (m + 1) F.Carrier) V₁)
    (π₂ : Representation ℂ (GeneralLinear (n + 1) F.Carrier) V₂),
    IsGeneric ψ m π₁ → IsGeneric ψ n π₂ → ∀ s : ℂ,
      (∀ Λ ∈ glFunctionals ψ (m + 1 + n)
          (T.shahidiSource (Nat.add_one_pos m) (Nat.add_one_pos n) s π₁ π₂), Λ ≠ 0 →
        ∀ L ∈ glFunctionals ψ (m + 1 + n)
          (T.shahidiSource (Nat.add_one_pos m) (Nat.add_one_pos n) s π₁ π₂),
          ∃ a : ℂ, L = a • Λ) ∧
      (∀ Λ' ∈ glFunctionals ψ (m + 1 + n)
          (T.shahidiTarget (Nat.add_one_pos m) (Nat.add_one_pos n) s π₁ π₂), Λ' ≠ 0 →
        ∀ L' ∈ glFunctionals ψ (m + 1 + n)
          (T.shahidiTarget (Nat.add_one_pos m) (Nat.add_one_pos n) s π₁ π₂),
          ∃ a : ℂ, L' = a • Λ')

/-- The rational existence assertion for (0.3), with all three Haar measures
explicit. Existence includes the analytic nonzero and rationality input beyond
multiplicity one. It does not assert the normalized gamma comparison. -/
def ShahidiLocalCoefficientExistenceStatement : Prop :=
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  letI := borel F.Carrier
  ∀ (ψ : UnitaryAdditiveCharacter F.Carrier), T.additiveConductor ψ = 0 →
  ∀ (ν νJ νJ' : AdditiveHaarMeasure F.Carrier),
  ∀ (V₁ V₂ : Type uV) [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup V₂] [Module ℂ V₂]
    (π₁ : Representation ℂ (GeneralLinear (m + 1) F.Carrier) V₁)
    (π₂ : Representation ℂ (GeneralLinear (n + 1) F.Carrier) V₂),
    IsGeneric ψ m π₁ → IsGeneric ψ n π₂ →
    ∃ C : RatFunc ℂ, T.IsShahidiLocalCoefficient π₁ π₂ ψ
      (rectangularMeasure ν (n + 1) (m + 1))
      (rectangularMeasure νJ (n + 1) (m + 1))
      (rectangularMeasure νJ' (m + 1) (n + 1)) C

/-- The three remaining analytic obligations for item 3 of the local-coefficient
framework. This conjunction assumes none of its component statements. -/
def ShahidiJacquetAndCoefficientStatement : Prop :=
  T.ShahidiJacquetStabilizationStatement.{uF, uV} m n ∧
  T.ShahidiInducedWhittakerMultiplicityOneStatement.{uF, uV} m n ∧
  T.ShahidiLocalCoefficientExistenceStatement.{uF, uV} m n

end Langlands.PadicField.TopologicalData
