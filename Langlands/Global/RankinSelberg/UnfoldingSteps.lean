import Langlands.Global.RankinSelberg.UnfoldingGL

/-! # Generic unfolding steps over `N_m(F) \ GL_m(𝔸)` -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry NumberField MeasureTheory
open scoped CategoryTheory.MonObj ENNReal Pointwise
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.Unfolding

open Langlands.Global

local instance unfoldingStepsSchemeAffine (F : Type u) [Field F] (n : ℕ) :
    IsAffine (Scheme F n).X.left := GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance unfoldingStepsSchemeSmooth (F : Type u) [Field F] (n : ℕ) :
    Smooth (Scheme F n).X.hom := GroupScheme.GeneralLinear.smoothStatement _ _

section InvInvariant

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]

/-- A regular Haar measure which is also right invariant is invariant under inversion. -/
theorem isInvInvariant_of_isMulRightInvariant (mu : Measure G) [mu.IsHaarMeasure] [mu.Regular]
    [mu.IsMulRightInvariant] : mu.IsInvInvariant := by
  constructor
  let c : ℝ≥0∞ := Measure.haarScalarFactor mu.inv mu
  have hc : mu.inv = c • mu := Measure.isMulLeftInvariant_eq_smul_of_regular mu.inv mu
  have h2 : Measure.map Inv.inv (Measure.map Inv.inv mu) = c ^ 2 • mu := by
    rw [← Measure.inv_def mu, hc, Measure.map_smul _ continuous_inv.measurable.aemeasurable,
      ← Measure.inv_def mu, hc, smul_smul, pow_two]
  have hmueq : mu = c ^ 2 • mu := by
    rw [Measure.map_map continuous_inv.measurable continuous_inv.measurable] at h2
    simpa only [inv_involutive, Function.Involutive.comp_self, Measure.map_id] using h2
  have K : TopologicalSpace.PositiveCompacts G := Classical.arbitrary _
  have h3 : c ^ 2 * mu K = 1 ^ 2 * mu K := by
    conv_rhs => rw [hmueq]
    simp
  have h4 : c ^ 2 = 1 ^ 2 :=
    (ENNReal.mul_left_inj (Measure.measure_pos_of_nonempty_interior mu K.interior_nonempty).ne'
      K.isCompact.measure_lt_top.ne).1 h3
  have h5 : c = 1 := (ENNReal.pow_right_strictMono two_ne_zero).injective h4
  rw [hc, h5, one_smul]

end InvInvariant

section Image

variable {H : Type*} [Group H] {N : Subgroup H} (Λ : Subgroup N) (Λ' : Subgroup H)

/-- Transfer a strict fundamental domain property from the image of `Λ` in `H` to `Λ`. -/
theorem existsUnique_of_image (hΛ : ∀ x : H, x ∈ Λ' ↔ ∃ l : Λ, ((l : N) : H) = x)
    {s : Set H} (hs : ∀ x : H, ∃! k : Λ', (k : H) * x ∈ s) (x : H) :
    ∃! l : Λ, ((l : N) : H) * x ∈ s := by
  obtain ⟨k, hk, hku⟩ := hs x
  obtain ⟨l, hl⟩ := (hΛ k).mp k.property
  refine ⟨l, show ((l : N) : H) * x ∈ s by rw [hl]; exact hk, fun l' hl' => ?_⟩
  have hmem : ((l' : N) : H) ∈ Λ' := (hΛ _).mpr ⟨l', rfl⟩
  have h1 := hku ⟨_, hmem⟩ hl'
  have h2 : ((l' : N) : H) = ((l : N) : H) := by
    rw [hl]
    exact congrArg Subtype.val h1
  exact Subtype.ext (Subtype.ext h2)

end Image

section Cosets

variable (F : Type u) [Field F] [NumberField F]

/-- The index set `N_n(F) \ GL_n(F)` of right cosets. -/
abbrev RationalCosetIndex (n : ℕ) :=
  Quotient (QuotientGroup.rightRel ((unipotentRationalImage F n).subgroupOf
    (AdelicGroupPoints.rationalSubgroup F (Scheme F n))))

/-- The chosen representatives of `N_n(F) \ GL_n(F)` in `GL_n(𝔸)`. -/
def rationalCosetRep (n : ℕ) (q : RationalCosetIndex F n) : Points F n :=
  cosetRep (unipotentRationalImage F n) (AdelicGroupPoints.rationalSubgroup F (Scheme F n)) q

instance rationalCosetIndexCountable (n : ℕ) : Countable (RationalCosetIndex F n) := by
  have := LeftCosetSpace.countable_of_isDiscrete
    (AdelicGroupPoints.rationalSubgroup F (Scheme F n))
    (AdelicGroupPoints.isDiscrete_rationalSubgroup F (Scheme F n))
  infer_instance

/-- `N_n(F)` inside `GL_n(𝔸)` is the image of the rational unipotent subgroup of `N_n(𝔸)`. -/
theorem mem_unipotentRationalImage_iff (n : ℕ) (x : Points F n) :
    x ∈ unipotentRationalImage F n ↔
      ∃ l : AdelicSubgroupPoints.rationalSubgroup F (Scheme F n) (upperUnipotent F n),
        ((l : unipotentAdelic F n) : Points F n) = x := by
  constructor
  · rintro ⟨q, rfl⟩
    exact ⟨⟨_, q, rfl⟩, rfl⟩
  · rintro ⟨⟨l, q, rfl⟩, rfl⟩
    exact ⟨q, rfl⟩

/-- Right translation of `N_n(F) \ GL_n(F)` by a rational point. -/
def cosetRightMul (n : ℕ) (k : AdelicGroupPoints.rationalSubgroup F (Scheme F n)) :
    RationalCosetIndex F n ≃ RationalCosetIndex F n where
  toFun := Quotient.map' (fun a => a * k) fun a b hab => by
    rw [QuotientGroup.rightRel_apply] at hab ⊢
    simpa [mul_assoc] using hab
  invFun := Quotient.map' (fun a => a * k⁻¹) fun a b hab => by
    rw [QuotientGroup.rightRel_apply] at hab ⊢
    simpa [mul_assoc] using hab
  left_inv q := by
    induction q using Quotient.inductionOn' with
    | h a => simp [Quotient.map'_mk'']
  right_inv q := by
    induction q using Quotient.inductionOn' with
    | h a => simp [Quotient.map'_mk'']

/-- Representatives are permuted by right translation, up to `N_n(F)`. -/
theorem rationalCosetRep_mul (n : ℕ) (k : AdelicGroupPoints.rationalSubgroup F (Scheme F n))
    (q : RationalCosetIndex F n) :
    ∃ l ∈ unipotentRationalImage F n,
      rationalCosetRep F n q * k = l * rationalCosetRep F n (cosetRightMul F n k q) := by
  have hq : cosetRightMul F n k q =
      Quotient.mk'' ((Quotient.out q : AdelicGroupPoints.rationalSubgroup F (Scheme F n)) * k) := by
    conv_lhs => rw [← Quotient.out_eq q]
    rfl
  have h1 := Quotient.mk_out (s := QuotientGroup.rightRel ((unipotentRationalImage F n).subgroupOf
    (AdelicGroupPoints.rationalSubgroup F (Scheme F n))))
    ((Quotient.out q : AdelicGroupPoints.rationalSubgroup F (Scheme F n)) * k)
  have h2 := QuotientGroup.rightRel_apply.mp h1
  rw [Subgroup.mem_subgroupOf] at h2
  refine ⟨_, h2, ?_⟩
  simp only [rationalCosetRep, cosetRep, hq, Subgroup.coe_mul, Subgroup.coe_inv,
    inv_mul_cancel_right]

end Cosets

section OrbitSum

variable (F : Type u) [Field F] [NumberField F]

/-- A function given as an orbit sum over `N_m(F) \ GL_m(F)` of a left `N_m(F)`-invariant
function is left invariant under `GL_m(F)`. -/
theorem rational_mul_of_hasSum {t : ℕ} {f I : Points F (t + 1) → ℂ}
    (hfΛ : ∀ k ∈ unipotentRationalImage F (t + 1), ∀ x, f (k * x) = f x)
    (hsum : ∀ x, HasSum (fun q => f (rationalCosetRep F (t + 1) q * x)) (I x))
    (k : AdelicGroupPoints.rationalSubgroup F (Scheme F (t + 1))) (x : Points F (t + 1)) :
    I ((k : Points F (t + 1)) * x) = I x := by
  have h1 := hsum ((k : Points F (t + 1)) * x)
  have h2 := hsum x
  set e := cosetRightMul F (t + 1) k
  have h3 : HasSum ((fun q => f (rationalCosetRep F (t + 1) q * x)) ∘ e)
      (I ((k : Points F (t + 1)) * x)) := by
    convert h1 using 1
    funext q
    obtain ⟨l, hl, hlq⟩ := rationalCosetRep_mul F (t + 1) k q
    simp only [Function.comp_apply]
    rw [← mul_assoc, hlq, mul_assoc, hfΛ l hl]
  exact ((Equiv.hasSum_iff e).mp h3).unique h2

/-- An everywhere convergent orbit sum of a measurable function is measurable. -/
theorem measurable_of_hasSum {t : ℕ} {f I : Points F (t + 1) → ℂ} (hfm : Measurable f)
    (hsum : ∀ x, HasSum (fun q => f (rationalCosetRep F (t + 1) q * x)) (I x)) :
    Measurable I := by
  have hlim : ∀ x, Filter.Tendsto (fun S : Finset (RationalCosetIndex F (t + 1)) =>
      ∑ q ∈ S, f (rationalCosetRep F (t + 1) q * x)) Filter.atTop (nhds (I x)) :=
    fun x => hsum x
  refine measurable_of_tendsto_metrizable' Filter.atTop (fun S => ?_) (tendsto_pi_nhds.mpr hlim)
  exact Finset.measurable_sum S fun q _ => hfm.comp (measurable_const_mul _)

omit [NumberField F] in
theorem rationalQuotientHaarMeasure_eq_quotientMeasure [NumberField F] (n : ℕ) :
    AdelicGroupPoints.rationalQuotientHaarMeasure F (Scheme F n) =
      LeftCosetSpace.quotientMeasure (AdelicGroupPoints.rationalSubgroup F (Scheme F n))
        Measure.haar (LeftCosetSpace.fundamentalDomain
          (AdelicGroupPoints.rationalSubgroup F (Scheme F n))
          (AdelicGroupPoints.isDiscrete_rationalSubgroup F (Scheme F n))) := rfl

/-- Unfolding an orbit sum: the integral over `GL_m(F) \ GL_m(𝔸)` of an orbit sum over
`N_m(F) \ GL_m(F)` is the integral of the summand over a fundamental domain of `N_m(F)`. -/
theorem integral_rationalQuotient_eq_of_hasSum {t : ℕ} {f I : Points F (t + 1) → ℂ}
    (hfm : Measurable f)
    (hfΛ : ∀ k ∈ unipotentRationalImage F (t + 1), ∀ x, f (k * x) = f x)
    (hsum : ∀ x, HasSum (fun q => f (rationalCosetRep F (t + 1) q * x)) (I x))
    (hint : IntegrableOn f (LeftCosetSpace.fundamentalDomain (unipotentRationalImage F (t + 1))
        (isDiscrete_unipotentRationalImage F (t + 1))) Measure.haar) :
    ∫ q, I q.out ∂AdelicGroupPoints.rationalQuotientHaarMeasure F (Scheme F (t + 1)) =
      ∫ x in LeftCosetSpace.fundamentalDomain (unipotentRationalImage F (t + 1))
          (isDiscrete_unipotentRationalImage F (t + 1)), f x ∂Measure.haar := by
  have hΓ := AdelicGroupPoints.isDiscrete_rationalSubgroup F (Scheme F (t + 1))
  have hΛ' := isDiscrete_unipotentRationalImage F (t + 1)
  have := LeftCosetSpace.countable_of_isDiscrete _ hΛ'
  have hfΛ' : ∀ (k : unipotentRationalImage F (t + 1)) (x : Points F (t + 1)),
      f ((k : Points F (t + 1)) * x) = f x := fun k x => hfΛ k k.property x
  have hIm := measurable_of_hasSum F hfm hsum
  have hIΓ := rational_mul_of_hasSum F hfΛ hsum
  have hsΓm := LeftCosetSpace.measurableSet_fundamentalDomain
    (AdelicGroupPoints.rationalSubgroup F (Scheme F (t + 1))) hΓ
  have hsΓ := LeftCosetSpace.fundamentalDomain_unique
    (AdelicGroupPoints.rationalSubgroup F (Scheme F (t + 1))) hΓ
  have hρΓ : ∀ q, rationalCosetRep F (t + 1) q ∈
      AdelicGroupPoints.rationalSubgroup F (Scheme F (t + 1)) := fun q => cosetRep_mem _ _ q
  have hρ : ∀ k ∈ AdelicGroupPoints.rationalSubgroup F (Scheme F (t + 1)),
      ∃! q, k * (rationalCosetRep F (t + 1) q)⁻¹ ∈ unipotentRationalImage F (t + 1) :=
    fun k hk => existsUnique_cosetRep _ _ k hk
  have hU := existsUnique_mem_iUnion_smul (unipotentRationalImage_le F (t + 1)) hsΓ
    (rationalCosetRep F (t + 1)) hρΓ hρ
  have hUm : MeasurableSet (⋃ q, rationalCosetRep F (t + 1) q •
      LeftCosetSpace.fundamentalDomain
        (AdelicGroupPoints.rationalSubgroup F (Scheme F (t + 1))) hΓ) :=
    MeasurableSet.iUnion fun q => hsΓm.const_smul _
  have hUfd : IsFundamentalDomain (unipotentRationalImage F (t + 1))
      (⋃ q, rationalCosetRep F (t + 1) q • LeftCosetSpace.fundamentalDomain
        (AdelicGroupPoints.rationalSubgroup F (Scheme F (t + 1))) hΓ)
      (Measure.haar : Measure (Points F (t + 1))) :=
    IsFundamentalDomain.mk' hUm.nullMeasurableSet hU
  have hsΛfd := LeftCosetSpace.isFundamentalDomain (unipotentRationalImage F (t + 1)) hΛ'
    (Measure.haar : Measure (Points F (t + 1)))
  have hfU := (hsΛfd.integrableOn_iff hUfd fun k x => hfΛ' k x).mp hint
  obtain ⟨-, hA⟩ := integrableOn_tsum_and_setIntegral_eq
    (Measure.haar : Measure (Points F (t + 1))) hsΓm hsΓ (rationalCosetRep F (t + 1)) hρΓ hρ hfU
  have hItsum : ∀ x, I x = ∑' q, f (rationalCosetRep F (t + 1) q * x) := fun x =>
    (hsum x).tsum_eq.symm
  rw [rationalQuotientHaarMeasure_eq_quotientMeasure, integral_out_eq _ hIm hIΓ,
    setIntegral_congr_fun hsΓm (fun x _ => hItsum x), hA]
  exact hUfd.setIntegral_eq hsΛfd fun k x => hfΛ' k x

end OrbitSum

section Average

variable (F : Type u) [Field F] [NumberField F]

local instance unipotentAdelicLocallyCompactSpace (n : ℕ) :
    LocallyCompactSpace (unipotentAdelic F n) :=
  (isClosed_upperUnipotent_adelicPoints F n).locallyCompactSpace

/-- The chosen fundamental domain of `N_n(F)` in `N_n(𝔸)`. -/
abbrev unipotentFundamentalDomain (n : ℕ) : Set (unipotentAdelic F n) :=
  LeftCosetSpace.fundamentalDomain
    (AdelicSubgroupPoints.rationalSubgroup F (Scheme F n) (upperUnipotent F n))
    (AdelicSubgroupPoints.isDiscrete_rationalSubgroup F (Scheme F n) (upperUnipotent F n))

/-- The mass of the fundamental domain of `N_n(F)` in `N_n(𝔸)` inverts the mass normalizer. -/
theorem haar_unipotentFundamentalDomain (n : ℕ) :
    (Measure.haar : Measure (unipotentAdelic F n)) (unipotentFundamentalDomain F n) =
      (AdelicSubgroupPoints.quotientMassNormalizer F (Scheme F n) (upperUnipotent F n))⁻¹ := by
  rw [AdelicSubgroupPoints.quotientMassNormalizer, inv_inv,
    AdelicSubgroupPoints.rationalQuotientHaarMeasure, LeftCosetSpace.haarQuotientMeasure,
    LeftCosetSpace.discreteQuotientMeasure,
    LeftCosetSpace.quotientMeasure_apply _ _ _ MeasurableSet.univ, Set.preimage_univ,
    Set.univ_inter]

/-- The mass normalizer and the mass of the fundamental domain are inverse real numbers. -/
theorem quotientMassNormalizer_mul_haar (n : ℕ) :
    (AdelicSubgroupPoints.quotientMassNormalizer F (Scheme F n) (upperUnipotent F n)).toReal *
      ((Measure.haar : Measure (unipotentAdelic F n)) (unipotentFundamentalDomain F n)).toReal =
      1 := by
  have := compactSpace_unipotentRationalQuotient F n
  rw [haar_unipotentFundamentalDomain, ← ENNReal.toReal_mul,
    ENNReal.mul_inv_cancel (AdelicSubgroupPoints.quotientMassNormalizer_ne_zero _ _ _)
      (AdelicSubgroupPoints.quotientMassNormalizer_ne_top _ _ _), ENNReal.toReal_one]

theorem haar_unipotentFundamentalDomain_toReal_ne_zero (n : ℕ) :
    ((Measure.haar : Measure (unipotentAdelic F n)) (unipotentFundamentalDomain F n)).toReal ≠
      0 := by
  intro h0
  have := quotientMassNormalizer_mul_haar F n
  rw [h0, mul_zero] at this
  exact zero_ne_one this

/-- Averaging over `N_m(F) \ N_m(𝔸)`: for a left `N_m(F)`-invariant `f` integrable on the
fundamental domain of `N_m(F)` in `GL_m(𝔸)`, the average over the fundamental domain in
`N_m(𝔸)` is integrable there, with integral the mass times that of `f`. -/
theorem integrableOn_and_setIntegral_average {t : ℕ} {f : Points F (t + 1) → ℂ}
    (hfm : Measurable f)
    (hfΛ : ∀ k ∈ unipotentRationalImage F (t + 1), ∀ x, f (k * x) = f x)
    (hint : IntegrableOn f (LeftCosetSpace.fundamentalDomain (unipotentRationalImage F (t + 1))
        (isDiscrete_unipotentRationalImage F (t + 1))) Measure.haar) :
    IntegrableOn (fun x => ∫ n in unipotentFundamentalDomain F (t + 1),
        f ((n : Points F (t + 1)) * x) ∂Measure.haar)
      (LeftCosetSpace.fundamentalDomain (unipotentRationalImage F (t + 1))
        (isDiscrete_unipotentRationalImage F (t + 1))) Measure.haar ∧
    ∫ x in LeftCosetSpace.fundamentalDomain (unipotentRationalImage F (t + 1))
        (isDiscrete_unipotentRationalImage F (t + 1)),
      (∫ n in unipotentFundamentalDomain F (t + 1),
        f ((n : Points F (t + 1)) * x) ∂Measure.haar) ∂Measure.haar =
      ((Measure.haar : Measure (unipotentAdelic F (t + 1)))
        (unipotentFundamentalDomain F (t + 1))).toReal •
        ∫ x in LeftCosetSpace.fundamentalDomain (unipotentRationalImage F (t + 1))
          (isDiscrete_unipotentRationalImage F (t + 1)), f x ∂Measure.haar := by
  have hΛ' := isDiscrete_unipotentRationalImage F (t + 1)
  have hΛd := AdelicSubgroupPoints.isDiscrete_rationalSubgroup F (Scheme F (t + 1))
    (upperUnipotent F (t + 1))
  have := LeftCosetSpace.countable_of_isDiscrete _ hΛd
  have := compactSpace_unipotentRationalQuotient F (t + 1)
  have := AdelicSubgroupPoints.haar_isMulRightInvariant_of_compactRationalQuotient F
    (Scheme F (t + 1)) (upperUnipotent F (t + 1))
  have : (Measure.haar : Measure (unipotentAdelic F (t + 1))).IsInvInvariant :=
    isInvInvariant_of_isMulRightInvariant _
  have hsH := existsUnique_of_image
    (AdelicSubgroupPoints.rationalSubgroup F (Scheme F (t + 1)) (upperUnipotent F (t + 1)))
    (unipotentRationalImage F (t + 1)) (mem_unipotentRationalImage_iff F (t + 1))
    (LeftCosetSpace.fundamentalDomain_unique _ hΛ')
  have hsNm := LeftCosetSpace.measurableSet_fundamentalDomain _ hΛd
  have hsN := LeftCosetSpace.fundamentalDomain_unique _ hΛd
  have hfin : (Measure.haar : Measure (unipotentAdelic F (t + 1)))
      (unipotentFundamentalDomain F (t + 1)) ≠ ∞ := by
    rw [haar_unipotentFundamentalDomain]
    exact ENNReal.inv_ne_top.mpr (AdelicSubgroupPoints.quotientMassNormalizer_ne_zero _ _ _)
  have hfΛd : ∀ (l : AdelicSubgroupPoints.rationalSubgroup F (Scheme F (t + 1))
      (upperUnipotent F (t + 1))) (x : Points F (t + 1)),
      f (((l : unipotentAdelic F (t + 1)) : Points F (t + 1)) * x) = f x :=
    fun l x => hfΛ _ ((mem_unipotentRationalImage_iff F (t + 1) _).mpr ⟨l, rfl⟩) x
  obtain ⟨hprodint, hprod⟩ := integrable_and_integral_average
    (AdelicSubgroupPoints.rationalSubgroup F (Scheme F (t + 1)) (upperUnipotent F (t + 1)))
    (Measure.haar : Measure (Points F (t + 1)))
    (Measure.haar : Measure (unipotentAdelic F (t + 1)))
    (LeftCosetSpace.measurableSet_fundamentalDomain _ hΛ') hsH hsNm hsN hfin hfm hfΛd hint
  refine ⟨hprodint.integral_prod_right, ?_⟩
  rw [integral_prod_symm _ hprodint] at hprod
  exact hprod

/-- If averaging `f` over `N_m(F) \ N_m(𝔸)` gives the mass times `g`, then `f` and `g` have the
same integral over the fundamental domain of `N_m(F)` in `GL_m(𝔸)`, and `g` is integrable there. -/
theorem setIntegral_eq_of_average {t : ℕ} {f g : Points F (t + 1) → ℂ}
    (hfm : Measurable f)
    (hfΛ : ∀ k ∈ unipotentRationalImage F (t + 1), ∀ x, f (k * x) = f x)
    (hint : IntegrableOn f (LeftCosetSpace.fundamentalDomain (unipotentRationalImage F (t + 1))
        (isDiscrete_unipotentRationalImage F (t + 1))) Measure.haar)
    (hinner : ∀ x, ∫ n in unipotentFundamentalDomain F (t + 1),
        f ((n : Points F (t + 1)) * x) ∂Measure.haar =
      ((Measure.haar : Measure (unipotentAdelic F (t + 1)))
        (unipotentFundamentalDomain F (t + 1))).toReal • g x) :
    IntegrableOn g (LeftCosetSpace.fundamentalDomain (unipotentRationalImage F (t + 1))
        (isDiscrete_unipotentRationalImage F (t + 1))) Measure.haar ∧
    ∫ x in LeftCosetSpace.fundamentalDomain (unipotentRationalImage F (t + 1))
        (isDiscrete_unipotentRationalImage F (t + 1)), f x ∂Measure.haar =
      ∫ x in LeftCosetSpace.fundamentalDomain (unipotentRationalImage F (t + 1))
        (isDiscrete_unipotentRationalImage F (t + 1)), g x ∂Measure.haar := by
  have ha0 := haar_unipotentFundamentalDomain_toReal_ne_zero F (t + 1)
  obtain ⟨hint₂, hprod⟩ := integrableOn_and_setIntegral_average F hfm hfΛ hint
  simp only [hinner] at hint₂ hprod
  refine ⟨(integrable_smul_iff ha0 _).mp hint₂, ?_⟩
  rw [integral_smul] at hprod
  exact (smul_right_injective ℂ ha0 hprod).symm

end Average

section WhittakerSide

variable (F : Type u) [Field F] [NumberField F]

/-- A measurable left `N_m(𝔸)`-invariant function integrable on the fundamental domain of
`N_m(F)` in `GL_m(𝔸)` is integrable on `N_m(𝔸) \ GL_m(𝔸)` for the Whittaker quotient
measure, evaluated at quotient representatives, with the same integral. -/
theorem integrable_and_integral_whittakerQuotient {t : ℕ} {g : Points F (t + 1) → ℂ}
    (hgm : Measurable g)
    (hgN : ∀ (n : unipotentAdelic F (t + 1)) (x : Points F (t + 1)),
      g ((n : Points F (t + 1)) * x) = g x)
    (hint : IntegrableOn g (LeftCosetSpace.fundamentalDomain (unipotentRationalImage F (t + 1))
        (isDiscrete_unipotentRationalImage F (t + 1))) Measure.haar) :
    Integrable (fun q : WhittakerQuotient F (t + 1) => g q.out)
        (whittakerQuotientMeasure F (t + 1)) ∧
      ∫ q, g q.out ∂whittakerQuotientMeasure F (t + 1) =
        ∫ x in LeftCosetSpace.fundamentalDomain (unipotentRationalImage F (t + 1))
          (isDiscrete_unipotentRationalImage F (t + 1)), g x ∂Measure.haar := by
  have hgΛ : ∀ (k : unipotentRationalImage F (t + 1)) (x : Points F (t + 1)),
      g ((k : Points F (t + 1)) * x) = g x := by
    intro k x
    obtain ⟨l, hl⟩ := (mem_unipotentRationalImage_iff F (t + 1) k).mp k.property
    rw [← hl]
    exact hgN _ x
  have hgqm : Measurable (fun q : WhittakerQuotient F (t + 1) => g q.out) := by
    rw [out_eq_lift (unipotentAdelic F (t + 1)) _ hgN]
    exact measurable_from_quotient.mpr hgm
  have hcomp : (fun q : WhittakerQuotient F (t + 1) => g q.out) ∘
      toWhittakerQuotient F (t + 1) = fun q' => g q'.out := by
    funext q'
    have h1 : toWhittakerQuotient F (t + 1) q' =
        LeftCosetSpace.mk (unipotentAdelic F (t + 1)) q'.out := by
      conv_lhs => rw [← Quotient.out_eq q']
      rfl
    simp only [Function.comp_apply, h1]
    obtain ⟨n, hn⟩ := exists_out_mk_eq (unipotentAdelic F (t + 1)) q'.out
    rw [hn]
    exact hgN n _
  have hmap : AEMeasurable (toWhittakerQuotient F (t + 1))
      (LeftCosetSpace.haarQuotientMeasure (unipotentRationalImage F (t + 1))
        (isDiscrete_unipotentRationalImage F (t + 1))) :=
    (measurable_toWhittakerQuotient F (t + 1)).aemeasurable
  constructor
  · rw [whittakerQuotientMeasure, integrable_map_measure hgqm.aestronglyMeasurable hmap, hcomp]
    exact (integrable_out_iff _ hgm hgΛ _ _).mpr hint
  · rw [whittakerQuotientMeasure, integral_map hmap hgqm.aestronglyMeasurable]
    have h2 : ∀ q', ((fun q : WhittakerQuotient F (t + 1) => g q.out)
        (toWhittakerQuotient F (t + 1) q')) = g q'.out := fun q' => congrFun hcomp q'
    simp only [h2]
    exact integral_out_eq _ hgm hgΛ _ _

end WhittakerSide

end Langlands.Global.RankinSelbergGlobal.Unfolding
