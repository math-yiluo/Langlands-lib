import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalCuspidalConjugationStatement
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSquareIntegrableDecay

/-! # Convergence of actual Schwartz conjugation pairings

Translation stability and the `L²` embedding give absolute convergence for
every conjugator from the local weighted Xi-square integrability estimate.
The resulting pairing is complex bilinear.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.HarishChandraSchwartz

section Generic

variable {Γ : Type*} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
  [MeasurableSpace Γ] [OpensMeasurableSpace Γ]
  [Nonempty (CompactOpenSubgroup Γ)] {Ξ σ : Γ → ℝ} {mu : Measure Γ}

/-- The bilinear conjugation integrand is integrable for every conjugator. -/
theorem Space.integrable_conjugationIntegrand
    (ht : TranslationWeights Ξ σ) (hsq : L2Weights mu Ξ σ)
    (f₁ f₂ : Space Ξ σ) (h : Γ) :
    Integrable (conjugationIntegrand (f₁ : Γ → ℂ) (f₂ : Γ → ℂ) h) mu := by
  have hi := (Space.memLp_two hsq (Space.translate ht h⁻¹ h⁻¹ f₁)).integrable_mul
    (Space.memLp_two hsq f₂)
  change Integrable (fun g => f₁ ((h⁻¹)⁻¹ * g * h⁻¹) * f₂ g) mu at hi
  change Integrable (fun g => f₁ (h * g * h⁻¹) * f₂ g) mu
  simpa only [inv_inv] using hi

end Generic

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace

section Rational

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]
  {i : S.toGrp ⟶ G} {ν : cocharacterLattice S}
  {K : OpenSubgroup (rationalPoints G)}
  (hKc : IsCompact (K : Set (rationalPoints G)))
  (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) K.toSubgroup)
  {N : ℕ} [Nonempty (Fin N)] (ρ : MatrixRepresentation G (Fin N))
  {muG : Measure (rationalPoints G)}
  (hsq : SquareIntegrableWeight muG (rationalXi hKc hPK) (rationalHeight (F := F) ρ))

include hsq

/-- The actual all-conjugators convergence result holds for every pair of
Schwartz functions under weighted Xi-square integrability. -/
theorem integrable_rationalConjugationIntegrand
    (f₁ f₂ : RationalSchwartzSpace hKc hPK ρ) (h : rationalPoints G) :
    Integrable (conjugationIntegrand (f₁ : rationalPoints G → ℂ)
      (f₂ : rationalPoints G → ℂ) h) muG := by
  let : Nonempty (CompactOpenSubgroup (rationalPoints G)) := ⟨⟨K, hKc⟩⟩
  exact Space.integrable_conjugationIntegrand
    (rationalTranslationWeights K.isOpen hKc hPK ρ)
    (rationalL2Weights K.isOpen hKc hPK ρ hsq) f₁ f₂ h

/-- The convergence component of VIII.3.1 follows from the local square
estimate; cuspidality is unnecessary for this component. -/
theorem rationalCuspidalConjugationConverges_of_squareIntegrableWeight :
    RationalCuspidalConjugationConverges hKc hPK ρ muG :=
  fun f₁ _ f₂ h => integrable_rationalConjugationIntegrand hKc hPK ρ hsq f₁ f₂ h

/-- The actual conjugation pairing, packaged as a complex bilinear map. -/
def rationalConjugationPairingBilinear :
    RationalSchwartzSpace hKc hPK ρ →ₗ[ℂ]
      RationalSchwartzSpace hKc hPK ρ →ₗ[ℂ] (rationalPoints G → ℂ) where
  toFun f₁ :=
    { toFun := rationalConjugationPairing hKc hPK ρ muG f₁
      map_add' := fun f₂ f₂' => by
        funext h
        exact conjugationPairing_add_right muG _ _ _ h
          (integrable_rationalConjugationIntegrand hKc hPK ρ hsq f₁ f₂ h)
          (integrable_rationalConjugationIntegrand hKc hPK ρ hsq f₁ f₂' h)
      map_smul' := fun c f₂ => by
        funext h
        exact conjugationPairing_smul_right muG c _ _ h }
  map_add' f₁ f₁' := by
    ext f₂ h
    exact conjugationPairing_add_left muG _ _ _ h
      (integrable_rationalConjugationIntegrand hKc hPK ρ hsq f₁ f₂ h)
      (integrable_rationalConjugationIntegrand hKc hPK ρ hsq f₁' f₂ h)
  map_smul' c f₁ := by
    ext f₂ h
    exact conjugationPairing_smul_left muG c _ _ h

@[simp] theorem rationalConjugationPairingBilinear_apply
    (f₁ f₂ : RationalSchwartzSpace hKc hPK ρ) (h : rationalPoints G) :
    rationalConjugationPairingBilinear hKc hPK ρ hsq f₁ f₂ h =
      rationalConjugationPairing hKc hPK ρ muG f₁ f₂ h := rfl

end Rational

end Langlands.HarishChandraSchwartz
