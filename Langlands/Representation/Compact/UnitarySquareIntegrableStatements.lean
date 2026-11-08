import Langlands.Representation.Category.Twist
import Langlands.Representation.MatrixCoefficient.ModuloCenter
import Langlands.Representation.Unitary.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.RepresentationTheory.Semisimple

/-! # Unitary and square-integrable representations (Renard IV.2.2 and IV.3.2–IV.3.3)

For a t.d. group `G`: an admissible unitary representation has one-dimensional endomorphism
algebra exactly when it is irreducible (IV.2.2, Corollary (i)); irreducible essentially
square-integrable representations are admissible (IV.3.2, Proposition); admissible
square-integrable representations are unitary and semisimple (IV.3.2, Lemma); and the Schur
orthogonality relations hold, with a positive formal degree (IV.3.3, Lemma and Corollary).
-/

noncomputable section

universe u v

open CategoryTheory MeasureTheory

namespace Langlands.Renard.CompactRepresentation

/-- Renard IV.2.2, Corollary (i): for a t.d. group `G` with a countable basis of neighbourhoods
of the identity and an admissible unitarizable smooth representation `π`, the space of
`G`-endomorphisms of `π` is one-dimensional if and only if `π` is irreducible. -/
def UnitaryAdmissibleEndomorphismStatement : Prop :=
  ∀ (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    [FirstCountableTopology G] (π : SmoothRep.{0, u, v} ℂ G),
    π.IsAdmissible → IsUnitarizable π.representation →
      (Module.finrank ℂ (π.representation.IntertwiningMap π.representation) = 1 ↔
        π.IsIrreducible)

/-- Renard IV.3.2, Proposition: let `G` be a t.d. group and `μ` a Haar measure on
`G / Z(G)`, also right invariant. If a smooth irreducible representation `π` becomes, after
twisting by some smooth character `ω` of `G`, a representation with a unitary central
character all of whose smooth matrix coefficients are square-integrable on `G / Z(G)`
(essentially square-integrable modulo the centre), then `π` is admissible. -/
def EssentiallySquareIntegrableAdmissibleStatement : Prop :=
  ∀ (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    [MeasurableSpace (G ⧸ Subgroup.center G)] [BorelSpace (G ⧸ Subgroup.center G)]
    (μ : Measure (G ⧸ Subgroup.center G)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]
    (π : SmoothRep.{0, u, v} ℂ G), π.IsIrreducible →
    ∀ (ω : G →* ℂˣ) (hω : IsOpen (ω.ker : Set G)),
      (∃ c : UnitaryCentralCharacter (π.twist ω hω).representation,
        ∀ (ℓ : SmoothDual (π.twist ω hω).representation) (x : π),
          MemLp (c.coefficientNorm ℓ x) 2 μ) →
      π.IsAdmissible

/-- Renard IV.3.2, Lemma: for a t.d. group `G` with a Haar measure `μ` on `G / Z(G)`, also
right invariant, every smooth representation that is admissible and square-integrable modulo
the centre (the published `IsSquareIntegrableModCenter`) is unitarizable and semisimple. No
irreducibility is assumed. -/
def SquareIntegrableUnitarySemisimpleStatement : Prop :=
  ∀ (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    [MeasurableSpace (G ⧸ Subgroup.center G)] [BorelSpace (G ⧸ Subgroup.center G)]
    (μ : Measure (G ⧸ Subgroup.center G)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]
    (π : SmoothRep.{0, u, v} ℂ G),
    IsSquareIntegrableModCenter π.representation μ →
      IsUnitarizable π.representation ∧
        Representation.IsSemisimpleRepresentation π.representation

/-- Renard IV.3.3, Lemma: let `G` be a t.d. group with a Haar measure `μ` on `G / Z(G)`, also
right invariant.

* (i) For a smooth irreducible `π` that is essentially square-integrable modulo the centre
  (some smooth twist `π ⊗ ω` has a unitary central character and square-integrable smooth
  coefficients), there is a real `d > 0`, the formal degree, such that for all vectors
  `x₁, x₂` and smooth functionals `ℓ₁, ℓ₂`, and every function `F` on `G / Z(G)` with
  `F(gZ) = ℓ₁(π(g) x₁) ℓ₂(π(g⁻¹) x₂)`, `F` is integrable and `∫ F dμ = ℓ₁(x₂) ℓ₂(x₁) / d`.
* (ii) For two such representations `π₁`, `π₂` that are not isomorphic and have the same
  central character, `F` is integrable and `∫ F dμ = 0` whenever
  `F(gZ) = ℓ₁(π₁(g) x₁) ℓ₂(π₂(g⁻¹) x₂)`. -/
def SchurOrthogonalityStatement : Prop :=
  ∀ (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    [MeasurableSpace (G ⧸ Subgroup.center G)] [BorelSpace (G ⧸ Subgroup.center G)]
    (μ : Measure (G ⧸ Subgroup.center G)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant],
    let EssSqInt : SmoothRep.{0, u, v} ℂ G → Prop := fun π =>
      ∃ (ω : G →* ℂˣ) (hω : IsOpen (ω.ker : Set G))
        (c : UnitaryCentralCharacter (π.twist ω hω).representation),
        ∀ (ℓ : SmoothDual (π.twist ω hω).representation) (x : π),
          MemLp (c.coefficientNorm ℓ x) 2 μ
    (∀ π : SmoothRep.{0, u, v} ℂ G, π.IsIrreducible → EssSqInt π →
      ∃ d : ℝ, 0 < d ∧
        ∀ (x₁ x₂ : π) (ℓ₁ ℓ₂ : SmoothDual π.representation)
          (F : G ⧸ Subgroup.center G → ℂ),
          (∀ g : G, F (QuotientGroup.mk g) =
            (ℓ₁ : Module.Dual ℂ π) (π.representation g x₁) *
              (ℓ₂ : Module.Dual ℂ π) (π.representation g⁻¹ x₂)) →
          Integrable F μ ∧
            ∫ q, F q ∂μ = (ℓ₁ : Module.Dual ℂ π) x₂ * (ℓ₂ : Module.Dual ℂ π) x₁ / d) ∧
    ∀ π₁ π₂ : SmoothRep.{0, u, v} ℂ G, π₁.IsIrreducible → π₂.IsIrreducible →
      EssSqInt π₁ → EssSqInt π₂ → IsEmpty (π₁ ≅ π₂) →
      (∃ χ : Subgroup.center G →* ℂˣ, ∀ (z : Subgroup.center G) (x₁ : π₁) (x₂ : π₂),
          π₁.representation z x₁ = (χ z : ℂ) • x₁ ∧ π₂.representation z x₂ = (χ z : ℂ) • x₂) →
      ∀ (x₁ : π₁) (x₂ : π₂) (ℓ₁ : SmoothDual π₁.representation)
        (ℓ₂ : SmoothDual π₂.representation) (F : G ⧸ Subgroup.center G → ℂ),
        (∀ g : G, F (QuotientGroup.mk g) =
          (ℓ₁ : Module.Dual ℂ π₁) (π₁.representation g x₁) *
            (ℓ₂ : Module.Dual ℂ π₂) (π₂.representation g⁻¹ x₂)) →
        Integrable F μ ∧ ∫ q, F q ∂μ = 0

/-- Renard IV.3.3, Corollary: for pairwise non-isomorphic smooth irreducible representations
`π₁, …, π_r` of a t.d. group, essentially square-integrable modulo the centre (with respect to
a Haar measure on `G / Z(G)`, also right invariant) and with a common central character, and
nonzero `xᵢ ∈ πᵢ`, nonzero smooth functionals `ℓᵢ` on `πᵢ`, the matrix coefficients
`g ↦ ℓᵢ(πᵢ(g) xᵢ)` are linearly independent functions on `G`. -/
def CoefficientLinearIndependenceStatement : Prop :=
  ∀ (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    [MeasurableSpace (G ⧸ Subgroup.center G)] [BorelSpace (G ⧸ Subgroup.center G)]
    (μ : Measure (G ⧸ Subgroup.center G)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]
    (r : ℕ) (π : Fin r → SmoothRep.{0, u, v} ℂ G),
    (∀ i, (π i).IsIrreducible) →
    (∀ i, ∃ (ω : G →* ℂˣ) (hω : IsOpen (ω.ker : Set G))
        (c : UnitaryCentralCharacter ((π i).twist ω hω).representation),
        ∀ (ℓ : SmoothDual ((π i).twist ω hω).representation) (x : π i),
          MemLp (c.coefficientNorm ℓ x) 2 μ) →
    (∀ i j, i ≠ j → IsEmpty (π i ≅ π j)) →
    (∃ χ : Subgroup.center G →* ℂˣ, ∀ i (z : Subgroup.center G) (x : π i),
        (π i).representation z x = (χ z : ℂ) • x) →
    ∀ (x : ∀ i, π i) (ℓ : ∀ i, SmoothDual (π i).representation),
      (∀ i, x i ≠ 0) → (∀ i, ℓ i ≠ 0) →
      LinearIndependent ℂ (fun i => matrixCoefficient (π i).representation (ℓ i) (x i))

/-- The five statements above. -/
def UnitarySquareIntegrableStatements.{u', v'} : Prop :=
  UnitaryAdmissibleEndomorphismStatement.{u', v'} ∧
    EssentiallySquareIntegrableAdmissibleStatement.{u', v'} ∧
    SquareIntegrableUnitarySemisimpleStatement.{u', v'} ∧
    SchurOrthogonalityStatement.{u', v'} ∧ CoefficientLinearIndependenceStatement.{u', v'}

end Langlands.Renard.CompactRepresentation
