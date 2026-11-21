import Langlands.Global.AdelicLeadingCuspidalInjectivityStatement
import Langlands.Global.AdelicEisensteinContinuationReduction

/-! # Vanishing of automorphic forms from their cuspidal pairings -/

noncomputable section
universe u

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Global.StandardParabolicFamily

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (𝓕 : StandardParabolicFamily F G)

local notation "Idx" => StandardIndex F G 𝓕.i 𝓕.ν

/-- All actual norm-one Levi cuspidal pairings of the standard constant terms
converge absolutely and vanish. -/
def HasVanishingCuspidalPairings {N : ℕ} (Kinf : Subgroup (InfiniteAdelicGroupPoints F G))
    (rho : MatrixRepresentation G (Fin N)) (φ : AdelicGroupPoints F G → ℂ) : Prop :=
  ∀ (J : Idx) (ψ : AdelicGroupPoints F (𝓕.M J) → ℂ), 𝓕.IsLeviCuspForm Kinf rho J ψ →
    ∀ g : AdelicGroupPoints F G,
      Integrable (𝓕.leviPairingIntegrand J (𝓕.constantTerm J φ) g ψ)
        (normOneRationalQuotientHaarMeasure F (𝓕.M J)) ∧
      𝓕.leviPairing J (𝓕.constantTerm J φ) g ψ = 0

private theorem constantTerm_zero_for_pairings (J : Idx) : 𝓕.constantTerm J 0 = 0 := by
  funext g
  simp [constantTerm, subgroupConstantTerm]

private theorem zero_hasVanishingCuspidalPairings {N : ℕ}
    (Kinf : Subgroup (InfiniteAdelicGroupPoints F G)) (rho : MatrixRepresentation G (Fin N)) :
    𝓕.HasVanishingCuspidalPairings Kinf rho 0 := by
  intro J ψ _ g
  rw [𝓕.constantTerm_zero_for_pairings J]
  have hzero : 𝓕.leviPairingIntegrand J 0 g ψ = 0 := by
    funext q
    simp [leviPairingIntegrand]
  simp [leviPairing, hzero]

/-- If the cuspidal pairings vanish, zero is a cuspidal projection of each
constant term and has the empty exponent decomposition. -/
theorem isGlobalLeadingCuspidalComponents_zero_of_pairings {N d : ℕ}
    (hsmooth : SmoothOfRelativeDimension d G.X.hom)
    (Kinf : Subgroup (InfiniteAdelicGroupPoints F G)) (rho : MatrixRepresentation G (Fin N))
    {φ : AdelicGroupPoints F G → ℂ} (hφ : 𝓕.HasVanishingCuspidalPairings Kinf rho φ) :
    𝓕.IsGlobalLeadingCuspidalComponents hsmooth Kinf rho φ 0 := by
  intro J
  refine ⟨0, ⟨?_, ?_, ?_⟩, ⟨∅, fun _ => 0, ?_, ?_⟩⟩
  · exact zero_isAutomorphicFunctionOn F G hsmooth
      (adelicDifferentialCommutator_of_smooth F G hsmooth) _ Kinf rho
  · intro Q _
    exact 𝓕.constantTerm_zero_for_pairings Q
  · intro ψ hψ g
    obtain ⟨hi, hz⟩ := hφ J ψ hψ g
    have hzero : 𝓕.leviPairingIntegrand J 0 g ψ = 0 := by
      funext q
      simp [leviPairingIntegrand]
    refine ⟨hi, hzero.symm ▸ integrable_zero _ _ _, ?_⟩
    rw [hz]
    simp [leviPairing, hzero]
  · refine ⟨by simp, ?_, ?_, ?_⟩ <;> simp
  · simp [leadingSum]

/-- Leading cuspidal injectivity gives detection by the actual scalar pairings
on automorphic functions. -/
theorem eq_zero_of_hasVanishingCuspidalPairings
    (hinj : LeadingCuspidalInjectivityStatement.{u})
    (K : Subgroup (AdelicGroupPoints F G)) (hK : IsMaximalCompactSubgroup F G K)
    (hKmin : IsIwasawaCompact (𝓕.p ⟨∅, Set.empty_subset _⟩) K)
    (hKlevi : ∀ J : Idx, IsMaximalCompactSubgroup F (𝓕.M J)
      (K.comap (AdelicGroupPoints.map F (𝓕.M J) G (𝓕.l J ≫ 𝓕.p J)).toMonoidHom))
    {N d : ℕ} (rho : MatrixRepresentation G (Fin N))
    (hsmooth : SmoothOfRelativeDimension d G.X.hom) (hrho : IsClosedSubgroup rho)
    {φ : AdelicGroupPoints F G → ℂ}
    (hauto : IsAutomorphicFunctionOn F G hsmooth (adelicDifferentialCommutator_of_smooth F G hsmooth)
      (rationalSubgroup F G) (K.comap (ofInfinite F G).toMonoidHom) rho φ)
    (hφ : 𝓕.HasVanishingCuspidalPairings (K.comap (ofInfinite F G).toMonoidHom) rho φ) :
    φ = 0 := by
  let Kinf := K.comap (ofInfinite F G).toMonoidHom
  exact hinj F G 𝓕 K hK hKmin hKlevi rho hsmooth hrho φ 0 0 hauto
    (zero_isAutomorphicFunctionOn F G hsmooth
      (adelicDifferentialCommutator_of_smooth F G hsmooth) (rationalSubgroup F G) Kinf rho)
    (𝓕.isGlobalLeadingCuspidalComponents_zero_of_pairings hsmooth Kinf rho hφ)
    (𝓕.isGlobalLeadingCuspidalComponents_zero_of_pairings hsmooth Kinf rho
      (𝓕.zero_hasVanishingCuspidalPairings Kinf rho))

end Langlands.Global.StandardParabolicFamily
