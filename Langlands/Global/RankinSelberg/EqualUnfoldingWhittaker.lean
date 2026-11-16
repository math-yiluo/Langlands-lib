import Langlands.Global.RankinSelberg.EqualUnfoldingKernel

/-! # The mirabolic and Whittaker steps of the equal-rank unfolding -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry NumberField MeasureTheory
open scoped CategoryTheory.MonObj ENNReal Pointwise
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.EqualUnfolding

open Langlands.Global Unfolding

local instance equalWhittakerSchemeAffine (F : Type u) [Field F] (n : ℕ) :
    IsAffine (Scheme F n).X.left := GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance equalWhittakerSchemeSmooth (F : Type u) [Field F] (n : ℕ) :
    Smooth (Scheme F n).X.hom := GroupScheme.GeneralLinear.smoothStatement _ _

variable (F : Type u) [Field F] [NumberField F]

local instance equalWhittakerUnipotentLocallyCompactSpace (n : ℕ) :
    LocallyCompactSpace (unipotentAdelic F n) :=
  (isClosed_upperUnipotent_adelicPoints F n).locallyCompactSpace

variable {r : ℕ}

/-- The kernel with a Whittaker function `W` and an `N_n(F)`-invariant `φ'` is left invariant
under `N_n(F)`. -/
theorem equalKernel_rational_unipotent_mul (ψ₀ : AddChar (Adeles F) ℂ)
    (hψ₀ : IsStandardAdditiveCharacter F ψ₀) {W φ' : Points F (r + 1) → ℂ}
    (Φ : RowVector F (r + 1) → ℂ) (s : ℂ)
    (hφ'Γ : ∀ k ∈ AdelicGroupPoints.rationalSubgroup F (Scheme F (r + 1)), ∀ x,
      φ' (k * x) = φ' x)
    (hWθ : ∀ (n : unipotentAdelic F (r + 1)) (x : Points F (r + 1)),
      W ((n : Points F (r + 1)) * x) = genericCharacter F r ψ₀ (fun _ => 1) n * W x)
    {k : Points F (r + 1)} (hk : k ∈ unipotentRationalImage F (r + 1)) (x : Points F (r + 1)) :
    equalKernel F W φ' Φ s (k * x) = equalKernel F W φ' Φ s x := by
  have hkΓ := unipotentRationalImage_le F (r + 1) hk
  obtain ⟨l, rfl⟩ := (mem_unipotentRationalImage_iff F (r + 1) k).mp hk
  unfold equalKernel
  rw [hWθ, genericCharacter_rational F r ψ₀ hψ₀.2.2.1, one_mul, hφ'Γ _ hkΓ,
    lastRow_unipotent_mul, detPower_unipotent_mul]

/-- The kernel with two Whittaker functions for inverse characters is left invariant under
`N_n(𝔸)`. -/
theorem equalKernel_unipotent_mul (ψ₀ : AddChar (Adeles F) ℂ)
    (hψ₀ : IsStandardAdditiveCharacter F ψ₀) {W W' : Points F (r + 1) → ℂ}
    (Φ : RowVector F (r + 1) → ℂ) (s : ℂ)
    (hWθ : ∀ (n : unipotentAdelic F (r + 1)) (x : Points F (r + 1)),
      W ((n : Points F (r + 1)) * x) = genericCharacter F r ψ₀ (fun _ => 1) n * W x)
    (hW'θ : ∀ (n : unipotentAdelic F (r + 1)) (x : Points F (r + 1)),
      W' ((n : Points F (r + 1)) * x) = (genericCharacter F r ψ₀ (fun _ => 1) n)⁻¹ * W' x)
    (n : unipotentAdelic F (r + 1)) (x : Points F (r + 1)) :
    equalKernel F W W' Φ s ((n : Points F (r + 1)) * x) = equalKernel F W W' Φ s x := by
  have hθ := genericCharacter_ne_zero F r ψ₀ hψ₀ (fun _ => 1) n
  unfold equalKernel
  rw [hWθ, hW'θ, lastRow_unipotent_mul, detPower_unipotent_mul]
  field_simp

/-- The kernel with the cusp form `φ` is the orbit sum over `N_r(F) \ GL_r(F)` of the kernel
with its Whittaker function. -/
theorem hasSum_equalKernel {W φ φ' : Points F (r + 1) → ℂ} (Φ : RowVector F (r + 1) → ℂ)
    (s : ℂ)
    (hφ'Γ : ∀ k ∈ AdelicGroupPoints.rationalSubgroup F (Scheme F (r + 1)), ∀ x,
      φ' (k * x) = φ' x)
    (hE : ∀ g : Points F (r + 1), HasSum (fun q : UnipotentRationalCosets F r =>
      W (cornerAdelicPoint F r q.out * g)) (φ g))
    (x : Points F (r + 1)) :
    HasSum (fun q : UnipotentRationalCosets F r =>
        equalKernel F W φ' Φ s (cornerAdelicPoint F r q.out * x))
      (equalKernel F φ φ' Φ s x) := by
  have h1 := (hE x).mul_right (φ' x * Φ (lastRow F r x) * detPower F (r + 1) x s)
  convert h1 using 1
  · funext q
    have hq := cornerAdelicPoint_mem_mirabolicRationalImage F r q.out
    unfold equalKernel
    rw [hφ'Γ _ (mirabolicRationalImage_le F r hq), lastRow_mirabolic_mul F r hq,
      detPower_rational_mul F (r + 1) (mirabolicRationalImage_le F r hq)]
    ring
  · unfold equalKernel
    ring

/-- Averaging the kernel of `φ'` over `N_n(F) \ N_n(𝔸)` gives the mass times the kernel of
its Whittaker function `W'`. -/
theorem setIntegral_unipotent_equalKernel (ψ₀ : AddChar (Adeles F) ℂ)
    {W φ' W' : Points F (r + 1) → ℂ} (Φ : RowVector F (r + 1) → ℂ) (s : ℂ)
    (hWθ : ∀ (n : unipotentAdelic F (r + 1)) (x : Points F (r + 1)),
      W ((n : Points F (r + 1)) * x) = genericCharacter F r ψ₀ (fun _ => 1) n * W x)
    (hW' : ∀ x : Points F (r + 1), W' x =
      ((AdelicSubgroupPoints.quotientMassNormalizer F (Scheme F (r + 1))
        (upperUnipotent F (r + 1))).toReal : ℂ) *
        ∫ n in unipotentFundamentalDomain F (r + 1),
          φ' ((n : Points F (r + 1)) * x) * genericCharacter F r ψ₀ (fun _ => 1) n
            ∂Measure.haar)
    (x : Points F (r + 1)) :
    ∫ n in unipotentFundamentalDomain F (r + 1),
        equalKernel F W φ' Φ s ((n : Points F (r + 1)) * x) ∂Measure.haar =
      ((Measure.haar : Measure (unipotentAdelic F (r + 1)))
          (unipotentFundamentalDomain F (r + 1))).toReal •
        equalKernel F W W' Φ s x := by
  set a : ℝ := ((Measure.haar : Measure (unipotentAdelic F (r + 1)))
    (unipotentFundamentalDomain F (r + 1))).toReal with ha
  set c : ℝ := (AdelicSubgroupPoints.quotientMassNormalizer F (Scheme F (r + 1))
    (upperUnipotent F (r + 1))).toReal with hc
  have hac : (c : ℂ) * (a : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, ha, hc, quotientMassNormalizer_mul_haar, Complex.ofReal_one]
  have e1 : (fun n : unipotentAdelic F (r + 1) =>
      equalKernel F W φ' Φ s ((n : Points F (r + 1)) * x)) =
      fun n : unipotentAdelic F (r + 1) =>
        (W x * Φ (lastRow F r x) * detPower F (r + 1) x s) *
          (φ' ((n : Points F (r + 1)) * x) * genericCharacter F r ψ₀ (fun _ => 1) n) := by
    funext n
    unfold equalKernel
    rw [hWθ, lastRow_unipotent_mul, detPower_unipotent_mul]
    ring
  rw [e1, integral_const_mul]
  unfold equalKernel
  rw [hW' x, Complex.real_smul]
  linear_combination (-(W x * Φ (lastRow F r x) * detPower F (r + 1) x s *
      ∫ n in unipotentFundamentalDomain F (r + 1),
        φ' ((n : Points F (r + 1)) * x) * genericCharacter F r ψ₀ (fun _ => 1) n
          ∂Measure.haar)) * hac

/-- Step III of the equal-rank unfolding on its own (Cogdell 2004, §2.3, p.210): if `W'` is the
Whittaker coefficient of `φ'` for the inverse character and the kernel
`W φ' Φ(e_n ·) |det|^s` is integrable over `N_n(F) \ GL_n(𝔸)`, then the Whittaker integrand
`W W' Φ(e_n ·) |det|^s` is integrable over `N_n(𝔸) \ GL_n(𝔸)`. No Whittaker expansion of a
cusp form is used. -/
theorem integrable_equalWhittakerIntegrand_of_kernel (ψ₀ : AddChar (Adeles F) ℂ)
    (hψ₀ : IsStandardAdditiveCharacter F ψ₀) {W φ' W' : Points F (r + 1) → ℂ}
    (Φ : RowVector F (r + 1) → ℂ) (s : ℂ)
    (hWm : Measurable W) (hφ'm : Measurable φ') (hW'm : Measurable W')
    (hΦm : Measurable fun x => Φ (lastRow F r x))
    (hφ'Γ : ∀ k ∈ AdelicGroupPoints.rationalSubgroup F (Scheme F (r + 1)), ∀ x,
      φ' (k * x) = φ' x)
    (hWθ : ∀ (n : unipotentAdelic F (r + 1)) (x : Points F (r + 1)),
      W ((n : Points F (r + 1)) * x) = genericCharacter F r ψ₀ (fun _ => 1) n * W x)
    (hW'θ : ∀ (n : unipotentAdelic F (r + 1)) (x : Points F (r + 1)),
      W' ((n : Points F (r + 1)) * x) = (genericCharacter F r ψ₀ (fun _ => 1) n)⁻¹ * W' x)
    (hW' : ∀ x : Points F (r + 1), W' x =
      ((AdelicSubgroupPoints.quotientMassNormalizer F (Scheme F (r + 1))
        (upperUnipotent F (r + 1))).toReal : ℂ) *
        ∫ n in unipotentFundamentalDomain F (r + 1),
          φ' ((n : Points F (r + 1)) * x) * genericCharacter F r ψ₀ (fun _ => 1) n
            ∂Measure.haar)
    (hG : Integrable (fun q : LeftCosetSpace (unipotentRationalImage F (r + 1)) =>
        equalKernel F W φ' Φ s q.out)
      (LeftCosetSpace.haarQuotientMeasure (unipotentRationalImage F (r + 1))
        (isDiscrete_unipotentRationalImage F (r + 1)))) :
    Integrable (equalWhittakerIntegrand F W W' Φ s) (whittakerQuotientMeasure F (r + 1)) := by
  have hΛ' := isDiscrete_unipotentRationalImage F (r + 1)
  have := LeftCosetSpace.countable_of_isDiscrete _ hΛ'
  have hK₀m : Measurable (equalKernel F W φ' Φ s) := measurable_equalKernel F hWm hφ'm hΦm s
  have hK₂m : Measurable (equalKernel F W W' Φ s) := measurable_equalKernel F hWm hW'm hΦm s
  have hK₀Λ : ∀ k ∈ unipotentRationalImage F (r + 1), ∀ x : Points F (r + 1),
      equalKernel F W φ' Φ s (k * x) = equalKernel F W φ' Φ s x :=
    fun k hk x => equalKernel_rational_unipotent_mul F ψ₀ hψ₀ Φ s hφ'Γ hWθ hk x
  have hK₀Λ' : ∀ (k : unipotentRationalImage F (r + 1)) (x : Points F (r + 1)),
      equalKernel F W φ' Φ s ((k : Points F (r + 1)) * x) = equalKernel F W φ' Φ s x :=
    fun k x => hK₀Λ k k.property x
  have hK₀N := (integrable_out_iff _ hK₀m hK₀Λ' _ _).mp hG
  obtain ⟨hK₂N, -⟩ := setIntegral_eq_of_average F hK₀m hK₀Λ hK₀N
    (setIntegral_unipotent_equalKernel F ψ₀ Φ s hWθ hW')
  exact (integrable_and_integral_whittakerQuotient F hK₂m
    (equalKernel_unipotent_mul F ψ₀ hψ₀ Φ s hWθ hW'θ) hK₂N).1

/-- Steps II and III of the equal-rank unfolding (Cogdell 2004, §2.3, p.210): if `φ` is the
orbit sum over `N_r(F) \ GL_r(F)` of its Whittaker function `W`, `W'` is the Whittaker
coefficient of `φ'` for the inverse character, and the kernel `W φ' Φ(e_n ·) |det|^s` is
integrable over `N_n(F) \ GL_n(𝔸)`, then the kernel `φ φ' Φ(e_n ·) |det|^s` is integrable on
the fundamental domain of `P_n(F)`, its integral there is the Whittaker integral
`Ψ(s; W, W', Φ)`, and the Whittaker integrand is integrable. -/
theorem mirabolic_unfolding (ψ₀ : AddChar (Adeles F) ℂ)
    (hψ₀ : IsStandardAdditiveCharacter F ψ₀) {W φ φ' W' : Points F (r + 1) → ℂ}
    (Φ : RowVector F (r + 1) → ℂ) (s : ℂ)
    (hWm : Measurable W) (hφ'm : Measurable φ') (hW'm : Measurable W')
    (hΦm : Measurable fun x => Φ (lastRow F r x))
    (hφ'Γ : ∀ k ∈ AdelicGroupPoints.rationalSubgroup F (Scheme F (r + 1)), ∀ x,
      φ' (k * x) = φ' x)
    (hWθ : ∀ (n : unipotentAdelic F (r + 1)) (x : Points F (r + 1)),
      W ((n : Points F (r + 1)) * x) = genericCharacter F r ψ₀ (fun _ => 1) n * W x)
    (hW'θ : ∀ (n : unipotentAdelic F (r + 1)) (x : Points F (r + 1)),
      W' ((n : Points F (r + 1)) * x) = (genericCharacter F r ψ₀ (fun _ => 1) n)⁻¹ * W' x)
    (hW' : ∀ x : Points F (r + 1), W' x =
      ((AdelicSubgroupPoints.quotientMassNormalizer F (Scheme F (r + 1))
        (upperUnipotent F (r + 1))).toReal : ℂ) *
        ∫ n in unipotentFundamentalDomain F (r + 1),
          φ' ((n : Points F (r + 1)) * x) * genericCharacter F r ψ₀ (fun _ => 1) n
            ∂Measure.haar)
    (hE : ∀ g : Points F (r + 1), HasSum (fun q : UnipotentRationalCosets F r =>
      W (cornerAdelicPoint F r q.out * g)) (φ g))
    (hG : Integrable (fun q : LeftCosetSpace (unipotentRationalImage F (r + 1)) =>
        equalKernel F W φ' Φ s q.out)
      (LeftCosetSpace.haarQuotientMeasure (unipotentRationalImage F (r + 1))
        (isDiscrete_unipotentRationalImage F (r + 1)))) :
    IntegrableOn (equalKernel F φ φ' Φ s)
        (LeftCosetSpace.fundamentalDomain (mirabolicRationalImage F r)
          (isDiscrete_mirabolicRationalImage F r)) Measure.haar ∧
      ∫ x in LeftCosetSpace.fundamentalDomain (mirabolicRationalImage F r)
          (isDiscrete_mirabolicRationalImage F r), equalKernel F φ φ' Φ s x ∂Measure.haar =
        equalWhittakerIntegral F W W' Φ s ∧
      Integrable (equalWhittakerIntegrand F W W' Φ s) (whittakerQuotientMeasure F (r + 1)) := by
  have hΓ := isDiscrete_mirabolicRationalImage F r
  have hΛ' := isDiscrete_unipotentRationalImage F (r + 1)
  have := LeftCosetSpace.countable_of_isDiscrete _ hΛ'
  have hK₀m : Measurable (equalKernel F W φ' Φ s) := measurable_equalKernel F hWm hφ'm hΦm s
  have hK₂m : Measurable (equalKernel F W W' Φ s) := measurable_equalKernel F hWm hW'm hΦm s
  have hK₀Λ : ∀ k ∈ unipotentRationalImage F (r + 1), ∀ x : Points F (r + 1),
      equalKernel F W φ' Φ s (k * x) = equalKernel F W φ' Φ s x :=
    fun k hk x => equalKernel_rational_unipotent_mul F ψ₀ hψ₀ Φ s hφ'Γ hWθ hk x
  have hK₀Λ' : ∀ (k : unipotentRationalImage F (r + 1)) (x : Points F (r + 1)),
      equalKernel F W φ' Φ s ((k : Points F (r + 1)) * x) = equalKernel F W φ' Φ s x :=
    fun k x => hK₀Λ k k.property x
  -- The kernel is integrable on the fundamental domain of `N_n(F)`.
  have hK₀N := (integrable_out_iff _ hK₀m hK₀Λ' _ _).mp hG
  -- Unfold the orbit sum over the fundamental domain of `P_n(F)`.
  set ρ : UnipotentRationalCosets F r → Points F (r + 1) :=
    fun q => cornerAdelicPoint F r q.out with hρdef
  have hρΓ : ∀ q, ρ q ∈ mirabolicRationalImage F r := fun q =>
    cornerAdelicPoint_mem_mirabolicRationalImage F r q.out
  have hρ : ∀ p ∈ mirabolicRationalImage F r,
      ∃! q, p * (ρ q)⁻¹ ∈ unipotentRationalImage F (r + 1) :=
    fun p hp => existsUnique_cornerAdelicPoint F r hp
  have hsPm := LeftCosetSpace.measurableSet_fundamentalDomain (mirabolicRationalImage F r) hΓ
  have hsP := LeftCosetSpace.fundamentalDomain_unique (mirabolicRationalImage F r) hΓ
  have hU := existsUnique_mem_iUnion_smul (unipotentRationalImage_le_mirabolicRationalImage F r)
    hsP ρ hρΓ hρ
  have hUm : MeasurableSet (⋃ q, ρ q •
      LeftCosetSpace.fundamentalDomain (mirabolicRationalImage F r) hΓ) :=
    MeasurableSet.iUnion fun q => hsPm.const_smul _
  have hUfd : IsFundamentalDomain (unipotentRationalImage F (r + 1))
      (⋃ q, ρ q • LeftCosetSpace.fundamentalDomain (mirabolicRationalImage F r) hΓ)
      (Measure.haar : Measure (Points F (r + 1))) :=
    IsFundamentalDomain.mk' hUm.nullMeasurableSet hU
  have hsΛfd := LeftCosetSpace.isFundamentalDomain (unipotentRationalImage F (r + 1)) hΛ'
    (Measure.haar : Measure (Points F (r + 1)))
  have hfU := (hsΛfd.integrableOn_iff hUfd hK₀Λ').mp hK₀N
  obtain ⟨hint₁, hA⟩ := integrableOn_tsum_and_setIntegral_eq
    (Measure.haar : Measure (Points F (r + 1))) hsPm hsP ρ hρΓ hρ hfU
  have htsum : (fun x => ∑' q, equalKernel F W φ' Φ s (ρ q * x)) = equalKernel F φ φ' Φ s :=
    funext fun x => (hasSum_equalKernel F Φ s hφ'Γ hE x).tsum_eq
  rw [htsum] at hint₁ hA
  -- Average over `N_n(F) \ N_n(𝔸)`, then pass to `N_n(𝔸) \ GL_n(𝔸)`.
  obtain ⟨hK₂N, havg⟩ := setIntegral_eq_of_average F hK₀m hK₀Λ hK₀N
    (setIntegral_unipotent_equalKernel F ψ₀ Φ s hWθ hW')
  obtain ⟨hint', hR⟩ := integrable_and_integral_whittakerQuotient F hK₂m
    (equalKernel_unipotent_mul F ψ₀ hψ₀ Φ s hWθ hW'θ) hK₂N
  refine ⟨hint₁, ?_, hint'⟩
  rw [hA, hUfd.setIntegral_eq hsΛfd hK₀Λ', havg]
  exact hR.symm

end Langlands.Global.RankinSelbergGlobal.EqualUnfolding
