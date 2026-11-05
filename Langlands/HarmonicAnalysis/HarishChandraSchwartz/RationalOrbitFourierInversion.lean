import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSplitCenterFourierInversion
import Langlands.Representation.Plancherel.RationalOrbitIntegration

/-! # Fourier inversion over `A_G` on a discrete-series orbit (Proposition VII.2.1, `M = G`)

Waldspurger, proof of Proposition VII.2.1, case `M = G` (printed pp. 317–318):
`∫_{A_G} χ_{ω'}(a⁻¹) ∫_O (E^G_G ψ_ω)(g) χ_ω(a) dω da` vanishes if the restrictions of `χ_ω` and
`χ_{ω'}` to the compact part of `A_G` differ, and otherwise equals
`∑_{ω ∈ O ; χ_ω = χ_{ω'}} (E^G_G ψ_ω)(g)`. This module proves both statements for an actual
discrete-series orbit `O` with its I.1 orbit measure, for an arbitrary continuous function `Φ` on
`O` in place of `ω ↦ (E^G_G ψ_ω)(g)` and an arbitrary left invariant measure on `A_G`, whose value
on `A_G ∩ G¹` appears as a factor. The central characters `χ_ω` restricted to `A_G` are given as a
function `cc` on `O` obeying the twist law `cc(χ ω₀) = χ|_{A_G} · cc(ω₀)`.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory Set
open Langlands.AlgebraicGeometry.PointTopology Langlands.Plancherel
open Langlands.HarmonicAnalysis.TorusFourier
open scoped CategoryTheory.MonObj

namespace Langlands.HarishChandraSchwartz

/-- **Sums over a finite saturated preimage**: if the fibres of `P` are the left cosets of a
finite subgroup `H`, then summing `Φ ∘ P` over the finite preimage of `X` counts every point of
`X` exactly `|H|` times. -/
theorem finsum_mem_preimage_comp {α β : Type*} [Group α] (H : Subgroup α) [Finite H]
    {P : α → β} (hPsurj : Function.Surjective P) (hP : ∀ x y, P x = P y ↔ x⁻¹ * y ∈ H)
    {X : Set β} (hfin : (P ⁻¹' X).Finite) (Φ : β → ℂ) :
    ∑ᶠ x ∈ P ⁻¹' X, Φ (P x) = (Nat.card H : ℂ) * ∑ᶠ y ∈ X, Φ y := by
  classical
  have hXfin : X.Finite := by
    rw [← image_preimage_eq X hPsurj]
    exact hfin.image P
  set s := hfin.toFinset
  have himage : hXfin.toFinset = s.image P := by
    ext y
    simp only [Finite.mem_toFinset, Finset.mem_image, s, mem_preimage]
    constructor
    · intro hy
      obtain ⟨x, rfl⟩ := hPsurj y
      exact ⟨x, hy, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact hx
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin, finsum_mem_eq_finite_toFinset_sum _ hXfin,
    himage, Finset.sum_comp, Finset.mul_sum]
  refine Finset.sum_congr rfl fun y hy => ?_
  obtain ⟨x₀, hx₀, rfl⟩ := Finset.mem_image.mp hy
  rw [nsmul_eq_mul]
  congr 1
  have hcard : (s.filter fun x => P x = P x₀).card = Nat.card H := by
    rw [← Nat.card_eq_finsetCard]
    refine Nat.card_congr ?_
    refine
      { toFun := fun x => ⟨x₀⁻¹ * x, (hP x₀ x).mp (Finset.mem_filter.mp x.2).2.symm⟩
        invFun := fun h => ⟨x₀ * h, Finset.mem_filter.mpr ⟨?_, ?_⟩⟩
        left_inv := fun x => Subtype.ext (mul_inv_cancel_left x₀ x)
        right_inv := fun h => Subtype.ext (inv_mul_cancel_left x₀ h) }
    · have hx₀' : P x₀ ∈ X := by simpa [s] using hx₀
      have hPh : P (x₀ * h) = P x₀ :=
        ((hP x₀ (x₀ * h)).mpr (by rw [inv_mul_cancel_left]; exact h.2)).symm
      simpa [s, hPh] using hx₀'
    · exact ((hP x₀ (x₀ * h)).mpr (by rw [inv_mul_cancel_left]; exact h.2)).symm
  rw [hcard]

universe u uV

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
variable {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left]
  [LocallyOfFiniteType G.X.hom]

local instance instRationalOrbitFourierInversion1 :
    TopologicalSpace (GroupScheme.rationalPoints G) :=
  rationalPointTopology F G.X
local instance instRationalOrbitFourierInversion2 :
    NonarchimedeanGroup (GroupScheme.rationalPoints G) :=
  rationalPoints_nonarchimedeanGroup G

variable {T : CommGroupScheme (Spec (CommRingCat.of F))} [IsAffine T.X.left]
  (s : T.toGrp ⟶ G) (hs : GroupScheme.IsCentral s)
  [MeasurableSpace (GroupScheme.rationalPoints G ⧸ (GroupScheme.rationalPoints.map s).range)]
  (mu : Measure (GroupScheme.rationalPoints G ⧸ (GroupScheme.rationalPoints.map s).range))
  (hindex : (RenardCartan.splitValuationImage s).FiniteIndex)

omit [LocallyOfFiniteType G.X.hom]
  [MeasurableSpace (GroupScheme.rationalPoints G ⧸ (GroupScheme.rationalPoints.map s).range)] in
include hs hindex in
/-- The characters `χ ∈ Im X(G)` with `χ c = η` on `A_G` form a finite set: it is empty or a
coset of the finite kernel of the restriction `Im X(G) → Im X(T)`. -/
theorem finite_setOf_unitaryUnramifiedCharacter_mul_eq
    (c eta : (GroupScheme.rationalPoints.map s).range →* Circle) :
    Set.Finite {χ : unitaryUnramifiedCharacters (fun ψ => (rationalNormCharacters G ψ).toMul) |
      ∀ a : (GroupScheme.rationalPoints.map s).range,
        ((χ.val (a : GroupScheme.rationalPoints G) : ℂˣ) : ℂ) * (c a : ℂ) = (eta a : ℂ)} := by
  rcases Set.eq_empty_or_nonempty {χ : unitaryUnramifiedCharacters
      (fun ψ => (rationalNormCharacters G ψ).toMul) |
      ∀ a : (GroupScheme.rationalPoints.map s).range,
        ((χ.val (a : GroupScheme.rationalPoints G) : ℂˣ) : ℂ) * (c a : ℂ) = (eta a : ℂ)} with
    h0 | ⟨χ₁, hχ₁⟩
  · rw [h0]
    exact Set.finite_empty
  have := finite_rationalUnitaryUnramifiedCharacterRestrict_ker s hs hindex
  refine (Set.finite_range fun k : (rationalUnitaryUnramifiedCharacterRestrict s).toMonoidHom.ker =>
    χ₁ * k).subset ?_
  intro χ hχ
  refine ⟨⟨χ₁⁻¹ * χ, ?_⟩, mul_inv_cancel_left χ₁ χ⟩
  rw [mem_rationalUnitaryUnramifiedCharacterRestrict_ker]
  intro t
  have h1 := hχ ⟨GroupScheme.rationalPoints.map s t, t, rfl⟩
  have h2 := hχ₁ ⟨GroupScheme.rationalPoints.map s t, t, rfl⟩
  have h3 : ((χ₁.val (GroupScheme.rationalPoints.map s t) : ℂˣ) : ℂ) =
      ((χ.val (GroupScheme.rationalPoints.map s t) : ℂˣ) : ℂ) :=
    mul_right_cancel₀ (Circle.coe_ne_zero _) (h2.trans h1.symm)
  change (χ₁.val (GroupScheme.rationalPoints.map s t))⁻¹ *
    χ.val (GroupScheme.rationalPoints.map s t) = 1
  rw [inv_mul_eq_one]
  exact Units.ext h3

/-- Waldspurger's integrand on a discrete-series orbit `O` of `ω₀ = omega`:
`a ↦ η(a⁻¹) ∫_O Φ(ω) χ_ω(a) dω` on `A_G`, with the I.1 orbit measure
`rationalNormalizedDiscreteSeriesOrbitMeasure` and `cc ω` in place of the restriction `χ_ω` of the
central character of `ω` to `A_G`. In the proof of Proposition VII.2.1, `η = χ_{ω'}` and
`Φ(ω) = (E^G_G ψ_ω)(g)`. -/
def rationalOrbitInversionIntegrand :
    letI := (GroupScheme.rationalPoints.map s).range.normal_of_le_center hs.range_le_center
    ∀ [Measure.IsHaarMeasure mu]
      (omega : DiscreteSeriesClass.{u, uV}
        (GroupScheme.rationalPoints.map s).range hs.range_le_center mu),
      (discreteSeriesOrbit (GroupScheme.rationalPoints.map s).range hs.range_le_center mu
        (fun psi => (rationalNormCharacters G psi).toMul) omega →
          (GroupScheme.rationalPoints.map s).range →* Circle) →
      ((GroupScheme.rationalPoints.map s).range →* Circle) →
      (discreteSeriesOrbit (GroupScheme.rationalPoints.map s).range hs.range_le_center mu
        (fun psi => (rationalNormCharacters G psi).toMul) omega → ℂ) →
      (GroupScheme.rationalPoints.map s).range → ℂ := by
  let := (GroupScheme.rationalPoints.map s).range.normal_of_le_center hs.range_le_center
  intro _ omega cc eta Φ a
  exact ((eta a⁻¹ : Circle) : ℂ) *
    ∫ ω, Φ ω * ((cc ω a : Circle) : ℂ)
      ∂rationalNormalizedDiscreteSeriesOrbitMeasure s hs mu hindex omega

/-- The orbit integrand is `|S|⁻¹` times the integrand on `Im X(G)` of
`RationalSplitCenterFourierInversion` for `f = Φ ∘ P`, where `P : χ ↦ χ ω₀` is the orbit map and
`S` the stabilizer of `ω₀`. -/
theorem rationalOrbitInversionIntegrand_eq (hG : GroupScheme.IsConnectedReductive G) :
    letI := (GroupScheme.rationalPoints.map s).range.normal_of_le_center hs.range_le_center
    ∀ [Measure.IsHaarMeasure mu]
      (omega : DiscreteSeriesClass.{u, uV}
        (GroupScheme.rationalPoints.map s).range hs.range_le_center mu)
      (cc : discreteSeriesOrbit (GroupScheme.rationalPoints.map s).range hs.range_le_center mu
        (fun psi => (rationalNormCharacters G psi).toMul) omega →
          (GroupScheme.rationalPoints.map s).range →* Circle)
      (c eta : (GroupScheme.rationalPoints.map s).range →* Circle),
      (∀ χ a, ((cc (discreteSeriesOrbitMap (GroupScheme.rationalPoints.map s).range
          hs.range_le_center mu (fun psi => (rationalNormCharacters G psi).toMul) omega χ) a :
            Circle) : ℂ) = ((χ.val (a : GroupScheme.rationalPoints G) : ℂˣ) : ℂ) * (c a : ℂ)) →
      ∀ {Φ : discreteSeriesOrbit (GroupScheme.rationalPoints.map s).range hs.range_le_center mu
        (fun psi => (rationalNormCharacters G psi).toMul) omega → ℂ}, Continuous Φ →
      ∀ a, rationalOrbitInversionIntegrand s hs mu hindex omega cc eta Φ a =
        (Nat.card (discreteSeriesStabilizer (GroupScheme.rationalPoints.map s).range
          hs.range_le_center mu (fun psi => (rationalNormCharacters G psi).toMul) omega) : ℂ)⁻¹ *
          rationalSplitCenterInversionIntegrand s hs hindex c eta
            (fun χ => Φ (discreteSeriesOrbitMap (GroupScheme.rationalPoints.map s).range
              hs.range_le_center mu (fun psi => (rationalNormCharacters G psi).toMul) omega χ))
            a := by
  let := (GroupScheme.rationalPoints.map s).range.normal_of_le_center hs.range_le_center
  intro _ omega cc c eta hcc Φ hΦ a
  have := compactSpace_rationalUnitaryUnramifiedCharacters G
  have := compactSpace_rationalDiscreteSeriesOrbit s hs mu omega
  -- evaluation at a point is continuous on `Im X(G)` (through the circle coordinates)
  have hev : Continuous fun χ : unitaryUnramifiedCharacters
      (fun ψ => (rationalNormCharacters G ψ).toMul) =>
        ((χ.val (a : GroupScheme.rationalPoints G) : ℂˣ) : ℂ) := by
    have hfun : (fun χ : unitaryUnramifiedCharacters
        (fun ψ => (rationalNormCharacters G ψ).toMul) =>
          ((χ.val (a : GroupScheme.rationalPoints G) : ℂˣ) : ℂ)) =
        fun χ => torusCharacter (rationalValuationCoordinates G hG a)
          (rationalCanonicalUnitaryUnramifiedCharacterCoordinates G hG χ) := by
      funext χ
      have h1 := rationalUnitaryUnramifiedCharacter_apply G hG
        (rationalCanonicalUnitaryUnramifiedCharacterCoordinates G hG χ) a
      rwa [ContinuousMulEquiv.symm_apply_apply] at h1
    rw [hfun]
    exact (continuous_torusCharacter _).comp
      (rationalCanonicalUnitaryUnramifiedCharacterCoordinates G hG).continuous
  -- hence `ω ↦ cc ω a` is continuous on the quotient topology of the orbit
  have hcc_cont : Continuous fun ω => ((cc ω a : Circle) : ℂ) := by
    refine (isOpenQuotientMap_discreteSeriesOrbitMap _ _ _ _ omega).isQuotientMap.continuous_iff.mpr
      ?_
    have hcomp : (fun ω => ((cc ω a : Circle) : ℂ)) ∘
      discreteSeriesOrbitMap (GroupScheme.rationalPoints.map s).range
      hs.range_le_center mu (fun psi => (rationalNormCharacters G psi).toMul) omega = fun χ =>
        ((χ.val (a : GroupScheme.rationalPoints G) : ℂˣ) : ℂ) * (c a : ℂ) :=
      funext fun χ => hcc χ a
    rw [hcomp]
    exact hev.mul continuous_const
  have h1 := rationalDiscreteSeriesOrbitIntegral_eq_characterIntegral s hs mu hindex omega
    (BoundedContinuousFunction.mkOfCompact
      ⟨fun ω => Φ ω * ((cc ω a : Circle) : ℂ), hΦ.mul hcc_cont⟩)
  rw [rationalDiscreteSeriesOrbitIntegral_apply] at h1
  simp only [BoundedContinuousFunction.mkOfCompact_apply, ContinuousMap.coe_mk] at h1
  simp only [rationalOrbitInversionIntegrand, rationalSplitCenterInversionIntegrand, h1,
    Complex.real_smul]
  simp_rw [hcc]
  push_cast
  ring

/-- **Vanishing for different restrictions to `A_G ∩ G¹`**: if `η ≠ c = χ_{ω₀}` at a point of
`A_G ∩ G¹`, the integral over `A_G` of the orbit integrand vanishes. -/
theorem integral_rationalOrbitInversionIntegrand_eq_zero
    (hG : GroupScheme.IsConnectedReductive G) :
    letI := (GroupScheme.rationalPoints.map s).range.normal_of_le_center hs.range_le_center
    ∀ [Measure.IsHaarMeasure mu]
      (omega : DiscreteSeriesClass.{u, uV}
        (GroupScheme.rationalPoints.map s).range hs.range_le_center mu)
      [MeasurableSpace (GroupScheme.rationalPoints.map s).range]
      [BorelSpace (GroupScheme.rationalPoints.map s).range]
      (ν : Measure (GroupScheme.rationalPoints.map s).range) [ν.IsMulLeftInvariant]
      (cc : discreteSeriesOrbit (GroupScheme.rationalPoints.map s).range hs.range_le_center mu
        (fun psi => (rationalNormCharacters G psi).toMul) omega →
          (GroupScheme.rationalPoints.map s).range →* Circle)
      (c eta : (GroupScheme.rationalPoints.map s).range →* Circle),
      (∀ χ a, ((cc (discreteSeriesOrbitMap (GroupScheme.rationalPoints.map s).range
          hs.range_le_center mu (fun psi => (rationalNormCharacters G psi).toMul) omega χ) a :
            Circle) : ℂ) = ((χ.val (a : GroupScheme.rationalPoints G) : ℂˣ) : ℂ) * (c a : ℂ)) →
      (∃ b : (GroupScheme.rationalPoints.map s).range,
        (b : GroupScheme.rationalPoints G) ∈ rationalCommonNormKernel G ∧ eta b ≠ c b) →
      ∀ {Φ : discreteSeriesOrbit (GroupScheme.rationalPoints.map s).range hs.range_le_center mu
        (fun psi => (rationalNormCharacters G psi).toMul) omega → ℂ}, Continuous Φ →
      ∫ a, rationalOrbitInversionIntegrand s hs mu hindex omega cc eta Φ a ∂ν = 0 := by
  let := (GroupScheme.rationalPoints.map s).range.normal_of_le_center hs.range_le_center
  intro _ omega _ _ ν _ cc c eta hcc h Φ hΦ
  simp_rw [rationalOrbitInversionIntegrand_eq s hs mu hindex hG omega cc c eta hcc hΦ]
  rw [integral_const_mul, integral_rationalSplitCenterInversionIntegrand_eq_zero s hs hindex ν c eta
    _ h, mul_zero]

/-- **Fourier inversion over `A_G` on a discrete-series orbit**: if `η = c = χ_{ω₀}` on
`A_G ∩ G¹`, `Φ` is continuous on the orbit and the orbit integrand is integrable, then
`∫_{A_G} η(a⁻¹) ∫_O Φ(ω) χ_ω(a) dω da = ν(A_G ∩ G¹) ∑_{ω ∈ O ; χ_ω = η} Φ(ω)`, a finite sum. -/
theorem integral_rationalOrbitInversionIntegrand (hG : GroupScheme.IsConnectedReductive G) :
    letI := (GroupScheme.rationalPoints.map s).range.normal_of_le_center hs.range_le_center
    ∀ [Measure.IsHaarMeasure mu]
      (omega : DiscreteSeriesClass.{u, uV}
        (GroupScheme.rationalPoints.map s).range hs.range_le_center mu)
      [MeasurableSpace (GroupScheme.rationalPoints.map s).range]
      [BorelSpace (GroupScheme.rationalPoints.map s).range]
      (ν : Measure (GroupScheme.rationalPoints.map s).range) [ν.IsMulLeftInvariant]
      (cc : discreteSeriesOrbit (GroupScheme.rationalPoints.map s).range hs.range_le_center mu
        (fun psi => (rationalNormCharacters G psi).toMul) omega →
          (GroupScheme.rationalPoints.map s).range →* Circle)
      (c eta : (GroupScheme.rationalPoints.map s).range →* Circle),
      (∀ χ a, ((cc (discreteSeriesOrbitMap (GroupScheme.rationalPoints.map s).range
          hs.range_le_center mu (fun psi => (rationalNormCharacters G psi).toMul) omega χ) a :
            Circle) : ℂ) = ((χ.val (a : GroupScheme.rationalPoints G) : ℂˣ) : ℂ) * (c a : ℂ)) →
      (∀ b : (GroupScheme.rationalPoints.map s).range,
        (b : GroupScheme.rationalPoints G) ∈ rationalCommonNormKernel G → eta b = c b) →
      ∀ {Φ : discreteSeriesOrbit (GroupScheme.rationalPoints.map s).range hs.range_le_center mu
        (fun psi => (rationalNormCharacters G psi).toMul) omega → ℂ}, Continuous Φ →
      Integrable (rationalOrbitInversionIntegrand s hs mu hindex omega cc eta Φ) ν →
      ∫ a, rationalOrbitInversionIntegrand s hs mu hindex omega cc eta Φ a ∂ν =
        ((ν (Subtype.val ⁻¹'
          (rationalCommonNormKernel G : Set (GroupScheme.rationalPoints G)))).toReal : ℂ) *
          ∑ᶠ ω ∈ {ω | cc ω = eta}, Φ ω := by
  let := (GroupScheme.rationalPoints.map s).range.normal_of_le_center hs.range_le_center
  intro _ omega _ _ ν _ cc c eta hcc h Φ hΦ hint
  have := finite_rationalDiscreteSeriesStabilizer s hs mu hindex omega
  have hS0 : (Nat.card (discreteSeriesStabilizer (GroupScheme.rationalPoints.map s).range
      hs.range_le_center mu (fun psi => (rationalNormCharacters G psi).toMul) omega) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hfun := rationalOrbitInversionIntegrand_eq s hs mu hindex hG omega cc c eta hcc hΦ
  have hcont : Continuous fun χ =>
      Φ (discreteSeriesOrbitMap (GroupScheme.rationalPoints.map s).range
      hs.range_le_center mu (fun psi => (rationalNormCharacters G psi).toMul) omega χ) :=
    hΦ.comp (continuous_discreteSeriesOrbitMap _ _ _ _ omega)
  -- integrability and the integral of the integrand on `Im X(G)`
  have hint' : Integrable (rationalSplitCenterInversionIntegrand s hs hindex c eta
      fun χ => Φ (discreteSeriesOrbitMap (GroupScheme.rationalPoints.map s).range
      hs.range_le_center mu (fun psi => (rationalNormCharacters G psi).toMul) omega χ)) ν := by
    refine (hint.const_mul (Nat.card (discreteSeriesStabilizer
      (GroupScheme.rationalPoints.map s).range hs.range_le_center mu
      (fun psi => (rationalNormCharacters G psi).toMul) omega) : ℂ)).congr
      (ae_of_all _ fun a => ?_)
    simp only [hfun a]
    exact mul_inv_cancel_left₀ hS0 _
  have hC := integral_rationalSplitCenterInversionIntegrand hG s hs hindex ν c eta hcont h hint'
  -- the index set on `Im X(G)` is the preimage of `{ω | cc ω = η}` under the orbit map
  have hpre : {χ : unitaryUnramifiedCharacters (fun ψ => (rationalNormCharacters G ψ).toMul) |
      ∀ a : (GroupScheme.rationalPoints.map s).range,
        ((χ.val (a : GroupScheme.rationalPoints G) : ℂˣ) : ℂ) * (c a : ℂ) = (eta a : ℂ)} =
      (discreteSeriesOrbitMap (GroupScheme.rationalPoints.map s).range
      hs.range_le_center mu (fun psi => (rationalNormCharacters G psi).toMul) omega) ⁻¹'
        {ω | cc ω = eta} := by
    ext χ
    simp only [Set.mem_ofPred_eq, Set.mem_preimage]
    constructor
    · intro hχ
      exact MonoidHom.ext fun a => Circle.coe_injective ((hcc χ a).trans (hχ a))
    · intro hχ a
      rw [← hcc χ a, hχ]
  have hP : ∀ x y, discreteSeriesOrbitMap (GroupScheme.rationalPoints.map s).range
      hs.range_le_center mu (fun psi => (rationalNormCharacters G psi).toMul) omega x =
      discreteSeriesOrbitMap (GroupScheme.rationalPoints.map s).range
      hs.range_le_center mu (fun psi => (rationalNormCharacters G psi).toMul) omega y ↔
      x⁻¹ * y ∈ discreteSeriesStabilizer (GroupScheme.rationalPoints.map s).range
      hs.range_le_center mu (fun psi => (rationalNormCharacters G psi).toMul) omega := fun x y =>
    (discreteSeriesOrbitHomeomorph (GroupScheme.rationalPoints.map s).range hs.range_le_center mu
      (fun psi => (rationalNormCharacters G psi).toMul) omega).injective.eq_iff.trans
      QuotientGroup.eq
  have hfin := finite_setOf_unitaryUnramifiedCharacter_mul_eq s hs hindex c eta
  rw [hpre] at hfin hC
  have hsum := finsum_mem_preimage_comp _
    (isOpenQuotientMap_discreteSeriesOrbitMap _ _ _ _ omega).surjective hP hfin Φ
  simp_rw [hfun]
  rw [integral_const_mul, hC, hsum]
  field_simp

end Langlands.HarishChandraSchwartz
