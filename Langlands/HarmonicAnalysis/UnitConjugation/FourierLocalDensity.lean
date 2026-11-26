import Langlands.HarmonicAnalysis.Bicharacter.FourierRestriction
import Langlands.HarmonicAnalysis.UnitConjugation.FourierRegularityStatement
import Mathlib.MeasureTheory.Group.Integral

/-! # Local density from Fourier agreement on lattice-invariant tests -/

noncomputable section

namespace Langlands.HarmonicAnalysis

open MeasureTheory Function

section Additive

variable {X : Type*} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X]
  [MeasurableSpace X] [BorelSpace X]
  (μ : Measure X) [μ.IsAddHaarMeasure] {e : X → X → ℂ} (he : IsSelfDualBicharacter e)

/-- Agreement of the Fourier transform of `D` with `S` on annihilator-invariant
 tests transfers any locally integrable Fourier density of `S` to a density for `D`
 on tests supported in the original subgroup. -/
def FourierRestrictionDensityStatement (L : AddSubgroup X) (D S : Distribution X) : Prop :=
  (∀ g : SchwartzBruhat X, (∀ t ∈ he.annihilator (L : Set X), ∀ x, g (x + t) = g x) →
    D (bicharacterFourierSB μ he g) = S g) →
  (∃ θ : X → ℂ, LocallyIntegrable θ μ ∧ ∀ g : SchwartzBruhat X,
    S (bicharacterFourierSB μ he g) = ∫ x, θ x * g x ∂μ) →
  ∃ θ : X → ℂ, LocallyIntegrable θ μ ∧ ∀ f : SchwartzBruhat X,
    support (f : X → ℂ) ⊆ L → D f = ∫ x, θ x * f x ∂μ

variable [LocallyCompactSpace X] [SecondCountableTopology X] [CompactOpenExhaustion X]

/-- Inversion evaluates the Fourier density of `S` on the reflected test and scales it
 by the reciprocal of the positive inversion constant for `μ`. -/
theorem fourierRestrictionDensity (L : AddSubgroup X) (D S : Distribution X) :
    FourierRestrictionDensityStatement μ he L D S := by
  rintro hagree ⟨θ, hθ, hS⟩
  obtain ⟨c, hc, hInv⟩ := exists_pos_bicharacterFourier_bicharacterFourier μ he
  have hc' : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc.ne'
  have hneg : LocallyIntegrable (fun x => θ (-x)) μ := by
    rw [locallyIntegrable_iff] at hθ ⊢
    intro K hK
    have hk : IsCompact ((Homeomorph.neg X) ⁻¹' K) := (Homeomorph.neg X).isCompact_preimage.mpr hK
    have h := ((Measure.measurePreserving_neg μ).integrableOn_comp_preimage
      (Homeomorph.neg X).toMeasurableEquiv.measurableEmbedding).2 (hθ _ hk)
    change IntegrableOn (fun x => θ (-x)) ((Neg.neg : X → X) ⁻¹' (Neg.neg ⁻¹' K)) μ at h
    simpa only [Set.preimage_preimage, Function.comp_def, neg_neg, Set.preimage_id'] using h
  refine ⟨fun x => (c : ℂ)⁻¹ * θ (-x), hneg.smul (c : ℂ)⁻¹, fun f hf => ?_⟩
  let r := Hecke.TestFunction.pullback (Homeomorph.neg X) f
  have hr : support (r : X → ℂ) ⊆ L := by
    intro x hx
    have hnegx : -x ∈ L := hf (show f (-x) ≠ 0 from hx)
    change x ∈ L
    simpa only [neg_neg] using L.neg_mem hnegx
  let g := bicharacterFourierSB μ he r
  have hF : bicharacterFourierSB μ he g = (c : ℂ) • f := by
    apply Subtype.ext
    funext x
    change bicharacterFourier μ e (bicharacterFourier μ e (r : X → ℂ)) x = (c : ℂ) * f x
    rw [hInv _ r.property x]
    change (c : ℂ) * f (- -x) = _
    rw [neg_neg]
  have h := hagree g (bicharacterFourierSB_annihilatorInvariant μ he L r hr)
  rw [hF, map_smul, smul_eq_mul, show S g = _ from hS r] at h
  have hReflection : (∫ x, θ x * r x ∂μ) = ∫ x, θ (-x) * f x ∂μ := by
    rw [← integral_neg_eq_self (μ := μ) (f := fun x => θ x * r x)]
    apply integral_congr_ae
    filter_upwards [] with x
    change θ (-x) * f (- -x) = θ (-x) * f x
    rw [neg_neg]
  rw [hReflection] at h
  simp_rw [mul_assoc, integral_const_mul]
  rw [← h, ← mul_assoc, inv_mul_cancel₀ hc', one_mul]

end Additive

section Algebra

open UnitConjugation

universe u v

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] [CharZero F]
  {A : Type v} [Ring A] [Algebra F A] [FiniteDimensional F A] [IsSemisimpleRing A]
  [TopologicalSpace A] [IsModuleTopology F A] [MeasurableSpace A] [BorelSpace A]

/-- The local Fourier step in semisimple descent. If a transform agrees on the
 annihilator-invariant tests with a compact-conjugacy-supported invariant distribution,
 Harish-Chandra's local summability assertion gives a density on the original subgroup. -/
theorem exists_density_on_subgroup_of_fourierAgreement
    (hHC : LieAlgebraFourierRegularityStatement.{u, v})
    (ψ : UnitaryAdditiveCharacter F) {B : LinearMap.BilinForm F A} (hB : IsInvariantPairing B)
    (μ : AdditiveHaarMeasure A) (L : AddSubgroup A) {ω : Set A} (hω : IsCompact ω)
    (D S : Distribution A)
    (hS : letI := IsModuleTopology.isTopologicalRing F A; S ∈ invariantSupportedIn ω)
    (hAgree : ∀ g : SchwartzBruhat A,
      (∀ t ∈ (isSelfDualBicharacter_pairingCharacter ψ hB.isSymm hB.nondegenerate).annihilator
        (L : Set A), ∀ x, g (x + t) = g x) →
      distributionFourier ψ hB.isSymm hB.nondegenerate μ D g = S g) :
    ∃ θ : A → ℂ, LocallyIntegrable θ μ.measure ∧ ∀ f : SchwartzBruhat A,
      support (f : A → ℂ) ⊆ L → D f = ∫ x, θ x * f x ∂μ.measure := by
  let := IsModuleTopology.isTopologicalAddGroup F A
  let := locallyCompactSpace_of_finiteDimensional F A
  let := secondCountableTopology_of_finiteDimensional F A
  let := compactOpenExhaustion_of_finiteDimensional F A
  exact fourierRestrictionDensity μ.measure
    (isSelfDualBicharacter_pairingCharacter ψ hB.isSymm hB.nondegenerate) L D S hAgree
    (hHC F A ψ B hB μ ω hω S hS)

end Algebra

end Langlands.HarmonicAnalysis
