import Langlands.Global.HeckeCharacter
import Langlands.Global.InfinityType
import Langlands.Global.AdelicFunctoriality.Isomorphism

/-!
# CM character globalization with actual arithmetic conjugation

Proposition definitions for the character constructions in Henniart 2000,
Sections 3.5--3.6. The finite-place separation and common positive scaling
remain explicit. Auxiliary norm-stabilizer general position is a separate
obligation, not an assumed predicate in these targets.
-/

noncomputable section

universe u v

namespace Langlands.Global

open NumberField

/-- Realize an anticyclotomic integral infinity type after one common positive
scaling, with conjugate self-duality and unramifiedness at every finite place. -/
def CMUnramifiedInfinityRealizationStatement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K] [IsCMField K]
    (a : InfinityType K), a.IsAnticyclotomic →
    ∃ (m : ℕ) (χ : HeckeCharacter K), 0 < m ∧
      (∀ x, χ (AdelicFunctoriality.ideleClassComplexConj x) = (χ x)⁻¹) ∧
      χ.HasPrescribedInfinityComponent
        (InfinityType.toCharacter (fun σ ↦ (m : ℤ) * a σ)) ∧
      ∀ w : FinitePlace K, χ.IsUnramifiedAt w

/-- Finite-order characters prescribed on a finite set disjoint from its
complex-conjugate set extend to a finite-order conjugate-self-dual character. -/
def CMFiniteCharacterPrescriptionStatement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K] [IsCMField K]
    (S : Finset (FinitePlace K)),
    Disjoint S (S.map
      (AdelicFunctoriality.finitePlaceEquiv
        (IsCMField.complexConj K).toRingEquiv).toEmbedding) →
    ∀ (η : (w : {w // w ∈ S}) → (FiniteCompletion K w.1)ˣ →ₜ* ℂˣ),
      (∀ w, ∃ n : ℕ, 0 < n ∧ η w ^ n = 1) →
      ∃ χ : HeckeCharacter K,
        χ.HasFiniteOrder ∧
        (∀ x, χ (AdelicFunctoriality.ideleClassComplexConj x) = (χ x)⁻¹) ∧
        χ.HasPrescribedInfinityComponent 1 ∧
        χ.HasPrescribedFiniteComponents S η

/-- A continuous character of the actual integral units extends to a
finite-order continuous character of the local multiplicative group. -/
def IntegralUnitCharacterExtensionStatement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K] (w : FinitePlace K)
    (η : (w.adicCompletionIntegers K)ˣ →ₜ* ℂˣ),
    ∃ χ : (FiniteCompletion K w)ˣ →ₜ* ℂˣ,
      (∃ n : ℕ, 0 < n ∧ χ ^ n = 1) ∧
      ∀ a : (w.adicCompletionIntegers K)ˣ,
        χ (Units.map (w.adicCompletionIntegers K).subtype.toMonoidHom a) = η a

/-- Combine regular integral infinity weights with arbitrary continuous
characters on the integral units at separated finite places.
Regularity is measured on embeddings extending a fixed imaginary-quadratic
embedding. Finite components are prescribed on units, not on uniformizers. -/
def CMRegularUnitPrescriptionStatement : Prop :=
  ∀ (E : Type v) [Field E] [NumberField E] [IsTotallyComplex E],
    Module.finrank ℚ E = 2 →
    ∀ (K : Type u) [Field K] [NumberField K] [IsCMField K]
      (ι : E →+* K) (τ : E →+* ℂ) (a : InfinityType K),
      a.IsAnticyclotomic → a.DistinctWeightsAbove ι τ →
      ∀ (S : Finset (FinitePlace K)),
        Disjoint S (S.map
          (AdelicFunctoriality.finitePlaceEquiv
            (IsCMField.complexConj K).toRingEquiv).toEmbedding) →
        ∀ (η : (w : {w // w ∈ S}) →
          (w.1.adicCompletionIntegers K)ˣ →ₜ* ℂˣ),
          ∃ (m : ℕ) (χ : HeckeCharacter K), 0 < m ∧
            (∀ x, χ (AdelicFunctoriality.ideleClassComplexConj x) = (χ x)⁻¹) ∧
            χ.HasPrescribedInfinityComponent
              (InfinityType.toCharacter (fun σ ↦ (m : ℤ) * a σ)) ∧
            InfinityType.DistinctWeightsAbove ι τ (fun σ ↦ (m : ℤ) * a σ) ∧
            ∀ (w : {w // w ∈ S}) (b : (w.1.adicCompletionIntegers K)ˣ),
              χ.finiteComponent w.1
                (Units.map (w.1.adicCompletionIntegers K).subtype.toMonoidHom b) = η w b

/-- The coherent CM-character globalization prerequisites. Their theorem
proofs and the auxiliary local norm-stabilizer construction remain separate. -/
def CMCharacterGlobalizationStatement : Prop :=
  CMUnramifiedInfinityRealizationStatement.{u} ∧
  CMFiniteCharacterPrescriptionStatement.{u} ∧
  IntegralUnitCharacterExtensionStatement.{u} ∧
  CMRegularUnitPrescriptionStatement.{u,v}

end Langlands.Global
