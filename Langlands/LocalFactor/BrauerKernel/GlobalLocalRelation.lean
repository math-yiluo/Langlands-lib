import Langlands.LocalFactor.BrauerKernel.LocalRelation
import Langlands.LocalFactor.BrauerKernel.PlaceEpsilon
import Langlands.ClassField.Global.LocalRelativeWeilMapStatement
import Langlands.VirtualRepresentation.Global.RelativeWeilLocalRestrictionReduction
import Langlands.ClassFieldTheory.Local.CommonClosureGeometricProof
import Langlands.Global.AdelicFunctoriality.LocalDegree

/-! # Local relations at every finite place from a global relation -/

noncomputable section

set_option autoImplicit false

universe uV

namespace Langlands.LocalFactor.NonabelianBrauer

open NumberField IsDedekindDomain
open Langlands.Global Langlands.Global.CompletionPadic Langlands.Global.AdelicFunctoriality
open ClassField.Global ClassField.Global.RelativeWeilGroup VirtualRepresentation
open scoped NumberField

attribute [local instance] relativeGaloisTopology

/-- **Local relations.** Assume the existence of local-to-relative Weil maps and the transfer
reciprocity of extensions of p-adic fields. A relation
`Σ_j r_j Ind_{W_{E/K_j}} ([Λ₁ j ∘ τ] - [Λ₂ j ∘ τ]) = 0` of reciprocity characters in the
continuous virtual group of `W_{E/k}` gives, at every finite place `z₀` of `k` and for every
normalized family of `k_{z₀}`, the local relation `LocalPlaceRelation` of the components of the
`Λ_i j` at the places above `z₀`. -/
theorem localPlaceRelation_of_global
    (hM : LocalRelativeWeilMapExistenceStatement.{0})
    (hsq : LocalClassField.ExtensionWeilTransferReciprocityStatement.{0, 0})
    (I : ∀ (p : ℕ) [Fact p.Prime], ClassFieldTheory.Local.InvariantFamily.{0, 0} p)
    (hI : ∀ (p : ℕ) [Fact p.Prime],
      (I p).RelativeClassFormation ∧ (I p).ArithmeticNormalization)
    (c : FundamentalClass.ClassFamily.{0})
    (hc : FundamentalClass.Generates c ∧ FundamentalClass.Restriction c ∧
      FundamentalClass.Inflation c ∧ FundamentalClass.LocalCompatibility I c)
    {k E : Type} [Field k] [NumberField k] [Field E] [NumberField E] [Algebra k E]
    [IsGalois k E] {J : Type*} [Fintype J] (r : J → ℤ) (K : J → IntermediateField k E)
    (Λ₁ Λ₂ : ∀ j, HeckeCharacter (K j))
    (hrel : ∑ j, r j • ExactGrothendieckGroup.continuousInduceAlong
          (restrictionInclusion c k E (K j) hc.2.1)
          (isOpenEmbedding_restrictionInclusion c k E (K j) hc.2.1)
          (ExactGrothendieckGroup.characterClass.{0, uV}
              (continuousReciprocityCharacter c (K j) E (Λ₁ j)) -
            ExactGrothendieckGroup.characterClass.{0, uV}
              (continuousReciprocityCharacter c (K j) E (Λ₂ j))) =
      (0 : ContinuousVirtual.{0, uV} c k E))
    (z₀ : Langlands.Global.FinitePlace k)
    (eC : LocalFactor.CommonClosure.ReciprocityFamily (padicField z₀))
    (heC : LocalFactor.CommonClosure.NormalizedReciprocity (padicField z₀) eC) :
    LocalPlaceRelation.{0, uV} r K Λ₁ Λ₂ z₀ eC := by
  obtain ⟨w, hw⟩ := placeAbove E z₀
  let ew := LocalClassField.extensionReciprocityCandidate (padicField z₀) (towerPadicField z₀ w)
    (completionPadicAlgHom z₀ w) eC
  have hew : LocalClassField.GeometricWeilReciprocityRelation (towerPadicField z₀ w)
      (towerPadicField z₀ w).canonicalTopologicalData ew :=
    (LocalClassField.commonClosureGeometricProof (residuePrime z₀) (padicField z₀) eC heC).2
      (towerPadicField z₀ w) (completionPadicAlgHom z₀ w)
  obtain ⟨ι, hι⟩ := hM I hI c hc k E z₀ w ew hew
  have hloc : ∀ j, LocalInducedRestriction.{uV, 0} c k (K j) E hc.2.1 z₀
      (discreteLocalMap ι) := fun j =>
    localInducedRestriction_of_extensionSquare hsq c k (K j) E hc.2.1 z₀ w ew ι hι
  exact sum_induce_weilCharacter_eq_zero hc.2.1 LocalClassField.commonClosureGeometricProof
    r K Λ₁ Λ₂ hrel (discreteLocalMap ι) hloc eC heC

end Langlands.LocalFactor.NonabelianBrauer
