import Langlands.Representation.Conductor.UnramifiedSphericalWhittaker
import Langlands.Representation.Conductor.OrderedUnramifiedSphericalCyclicity
import Langlands.Representation.Conductor.SphericalLFactorGenerationReduction
import Langlands.Representation.RankinSelberg.WhittakerTypeEquivalence
import Langlands.Representation.RankinSelberg.WhittakerGammaAdapters
import Langlands.AllField.Representation.RankinSelberg.NormalizedProductWhittakerTypeProof
import Langlands.AllField.Representation.RankinSelberg.RankOneWhittakerTypeProof
import Langlands.AllField.Representation.Conductor.UnramifiedPrincipalSeriesInduction

/-!
# A normalized inverse-character functional on norm-ordered unramified principal series

Over every nonarchimedean local field, for parameters `z` with nondecreasing norms, the
unramified principal series `I(z)` has a nonzero inverse-character Whittaker functional `ℓ`
whose coefficient of the spherical section `f₀` is Jacquet's spherical function. These are
clauses 1 and 3 of `OrderedUnramifiedWhittakerRealizationStatement`; the injectivity clause 2
is not proved here.
-/

noncomputable section

namespace Langlands.Conductor

open Langlands.GeneralLinear Langlands.HarmonicAnalysis Langlands.Whittaker
open Langlands.Conductor.UnramifiedPrincipalSeries

universe uF

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {ϖ : Fˣ}
  (hϖ : Iwasawa.IsUniformizingElement (ValuativeRel.valuation F) ϖ) (n : ℕ)
  {q : ℕ} (hq : IsResidueCardinality (F := F) q) (z : Fin (n + 1) → ℂˣ)

/-- `I(z)` is of Whittaker type over every nonarchimedean local field: it is equivalent to the
all-field normalized product induction of the rank-one characters `χ_{z_i}`, which are of
Whittaker type, and normalized product induction preserves Whittaker type. -/
theorem isOfWhittakerType_principalSeries (ψ : UnitaryAdditiveCharacter F) :
    RankinSelberg.IsOfWhittakerType n (standardCharacter ψ n) (principalSeries hϖ n hq z) :=
  RankinSelberg.IsOfWhittakerType.of_equiv
    (AllField.RankinSelberg.normalizedProductWhittakerType.{uF, 0} F ψ n (n + 1)
      (fun _ => 0) (by simp) (AllField.Conductor.UnramifiedPrincipalSeries.blocks hϖ n z)
      (fun i => AllField.RankinSelberg.rankOneCharacter_isOfWhittakerType F ψ
        (AllField.Conductor.UnramifiedPrincipalSeries.quasicharacter hϖ (z i))))
    (AllField.Conductor.UnramifiedPrincipalSeries.principalSeriesEquiv hϖ n hq z).symm

/-- `I(z)` has a nonzero inverse-character Whittaker functional. -/
theorem exists_glInverseFunctional_ne_zero (ψ : UnitaryAdditiveCharacter F) :
    ∃ ℓ : glInverseFunctionals ψ n (principalSeries hϖ n hq z), ℓ.val ≠ 0 := by
  obtain ⟨-, -, ⟨e⟩⟩ := (RankinSelberg.isOfWhittakerType_standard_iff_inverse ψ
    (principalSeries hϖ n hq z)).mp (isOfWhittakerType_principalSeries hϖ n hq z ψ)
  refine ⟨e.symm 1, fun h0 => one_ne_zero (e.symm.injective ?_)⟩
  rw [map_zero]
  exact Subtype.ext h0

/-- For nondecreasing norms, a nonzero inverse-character functional does not vanish on the
spherical section: otherwise every coefficient of `f₀` vanishes (Shintani's formula), and
since `f₀` generates `I(z)` (Jacquet's Lemma 1) the functional vanishes. -/
theorem glInverseFunctional_sphericalSection_ne_zero (hmono : Monotone (fun i => ‖(z i : ℂ)‖))
    {ψ : UnitaryAdditiveCharacter F} (hψ : HasIntegerConductor ψ)
    (ℓ : glInverseFunctionals ψ n (principalSeries hϖ n hq z)) (hℓ : ℓ.val ≠ 0) :
    ℓ.val (sphericalSection hϖ n hq z) ≠ 0 := by
  intro h0
  apply hℓ
  refine LinearMap.ext fun v => ?_
  obtain ⟨T, c, hc⟩ := exists_finset_translate_of_cyclic (principalSeries hϖ n hq z) ℓ
    (sphericalSection hϖ n hq z)
    (orderedUnramifiedSphericalCyclicity F ϖ hϖ n q hq z hmono)
    ⟨coefficientMap (principalSeries hϖ n hq z) ℓ v, v, rfl⟩
  have h1 := hc 1
  simp only [coefficientMap_sphericalSection_apply hϖ n hq z hψ ℓ, h0, zero_mul, mul_zero,
    Finset.sum_const_zero] at h1
  change ℓ.val (principalSeries hϖ n hq z 1 v) = 0 at h1
  rw [map_one, Module.End.one_apply] at h1
  rw [h1, LinearMap.zero_apply]

/-- **Clauses 1 and 3 of the ordered Whittaker realization.** For nondecreasing norms there is
a nonzero inverse-character functional `ℓ` on `I(z)` whose coefficient of the spherical section
is Jacquet's spherical function `W(·; z; ψ̄)`. -/
theorem exists_glInverseFunctional_sphericalWhittaker
    (hmono : Monotone (fun i => ‖(z i : ℂ)‖))
    {ψ : UnitaryAdditiveCharacter F} (hψ : HasIntegerConductor ψ) :
    ∃ ℓ : glInverseFunctionals ψ n (principalSeries hϖ n hq z),
      ℓ.val ≠ 0 ∧
      ∀ g : Langlands.GeneralLinear (n + 1) F,
        (coefficientMap (principalSeries hϖ n hq z) ℓ (sphericalSection hϖ n hq z)).val g =
          Spherical.sphericalWhittaker hϖ (inverseStandardCharacter ψ n) q z g := by
  obtain ⟨ℓ₀, hℓ₀⟩ := exists_glInverseFunctional_ne_zero hϖ n hq z ψ
  have hc := glInverseFunctional_sphericalSection_ne_zero hϖ n hq z hmono hψ ℓ₀ hℓ₀
  refine ⟨(ℓ₀.val (sphericalSection hϖ n hq z))⁻¹ • ℓ₀, ?_, fun g => ?_⟩
  · intro h0
    apply hℓ₀
    have h1 := congrArg (fun m => ℓ₀.val (sphericalSection hϖ n hq z) • m) h0
    simpa only [Submodule.coe_smul, smul_smul, mul_inv_cancel₀ hc, one_smul, smul_zero]
      using h1
  · rw [coefficientMap_sphericalSection_apply hϖ n hq z hψ]
    change ((ℓ₀.val (sphericalSection hϖ n hq z))⁻¹ * ℓ₀.val (sphericalSection hϖ n hq z)) *
      (inverseSphericalWhittaker hψ.1 hϖ q z).val g = _
    rw [inv_mul_cancel₀ hc, one_mul]
    rfl

end Langlands.Conductor
