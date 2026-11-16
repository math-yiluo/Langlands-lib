import Langlands.Global.RankinSelberg.EqualUnfoldingCount

/-! # Unfolding the Eisenstein series in the equal-rank integral -/

noncomputable section
universe u
open NumberField MeasureTheory Set
open scoped CategoryTheory.MonObj ENNReal Pointwise
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.EqualUnfolding

open Langlands.Global Unfolding

local instance equalEisensteinSchemeAffine (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.IsAffine (Scheme F n).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance equalEisensteinSchemeSmooth (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.Smooth (Scheme F n).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement _ _

attribute [local instance] equalSectionRowMeasurableSpace equalSectionRowBorelSpace

variable (F : Type u) [Field F] [NumberField F]

section Quotient

/-- The chosen fundamental domain of `GL_n(F)` in `GL_n(𝔸)`. -/
abbrev rationalDomain (n : ℕ) : Set (Points F n) :=
  LeftCosetSpace.fundamentalDomain (AdelicGroupPoints.rationalSubgroup F (Scheme F n))
    (AdelicGroupPoints.isDiscrete_rationalSubgroup F (Scheme F n))

/-- The slab `1 ≤ |det g| < e^n` is left invariant under `GL_n(F)`. -/
theorem rational_mul_mem_slabSet_iff (n : ℕ) {k : Points F n}
    (hk : k ∈ AdelicGroupPoints.rationalSubgroup F (Scheme F n)) (x : Points F n) :
    k * x ∈ slabSet F n ↔ x ∈ slabSet F n := by
  show (1 ≤ detNorm F n (k * x) ∧ detNorm F n (k * x) < Real.exp n) ↔
    (1 ≤ detNorm F n x ∧ detNorm F n x < Real.exp n)
  rw [detNorm_mul, detNorm_of_mem_rationalSubgroup F n hk, one_mul]

/-- The slab is saturated for the projection to `GL_n(F) \ GL_n(𝔸)`. -/
theorem preimage_image_mk_slabSet (n : ℕ) :
    LeftCosetSpace.mk (AdelicGroupPoints.rationalSubgroup F (Scheme F n)) ⁻¹'
      (LeftCosetSpace.mk (AdelicGroupPoints.rationalSubgroup F (Scheme F n)) '' slabSet F n) =
      slabSet F n := by
  rw [LeftCosetSpace.preimage_image_mk]
  ext x
  simp only [mem_iUnion]
  constructor
  · rintro ⟨k, hx⟩
    rw [mem_smul_set_iff_inv_smul_mem, Subgroup.smul_def, smul_eq_mul] at hx
    exact (rational_mul_mem_slabSet_iff F n (k⁻¹).property x).mp hx
  · intro hx
    exact ⟨1, by rw [one_smul]; exact hx⟩

/-- The measure on `Z_n(𝔸) GL_n(F) \ GL_n(𝔸)` is the quotient measure of the Haar measure
restricted to the part `S ∩ D` of the fundamental domain `D` of `GL_n(F)` in the slab `S`. -/
theorem centralQuotientMeasure_eq (n : ℕ) :
    centralQuotientMeasure F n =
      LeftCosetSpace.quotientMeasure (centralRationalSubgroup F n) Measure.haar
        (slabSet F n ∩ rationalDomain F n) := by
  have hS := measurableSet_slabSet F n
  have hSq : MeasurableSet (LeftCosetSpace.mk (AdelicGroupPoints.rationalSubgroup F (Scheme F n)) ''
      slabSet F n) :=
    LeftCosetSpace.measurableSet_image_mk _ hS
  rw [centralQuotientMeasure, rationalQuotientHaarMeasure_eq_quotientMeasure,
    LeftCosetSpace.quotientMeasure, LeftCosetSpace.quotientMeasure,
    show determinantSlab F n 1 (Real.exp n) =
      LeftCosetSpace.mk (AdelicGroupPoints.rationalSubgroup F (Scheme F n)) '' slabSet F n from rfl,
    Measure.restrict_map (LeftCosetSpace.measurable_mk _) hSq, preimage_image_mk_slabSet,
    Measure.restrict_restrict hS,
    Measure.map_map (measurable_toCentralQuotient F n) (LeftCosetSpace.measurable_mk _)]
  rfl

end Quotient

variable {F} {r : ℕ}

section Products

variable (χ : IdeleClassGroup (𝓞 F) F →ₜ* ℂˣ) (φ φ' : Points F (r + 1) → ℂ)
  (Φ : RowVector F (r + 1) → ℂ) (s : ℂ)

/-- `g ↦ φ(g) φ'(g) E(g, Φ; s, χ)` on `GL_n(𝔸)`. -/
def equalSeriesProduct (x : Points F (r + 1)) : ℂ :=
  φ x * φ' x * eisensteinSeries F χ Φ s x

/-- `g ↦ φ(g) φ'(g) F(g, Φ; s, χ)` on `GL_n(𝔸)`. -/
def equalSectionProduct (x : Points F (r + 1)) : ℂ :=
  φ x * φ' x * eisensteinSection F χ Φ s x

theorem equalIntegrand_eq :
    equalIntegrand F χ φ φ' Φ s = fun q => equalSeriesProduct χ φ φ' Φ s q.out := rfl

variable {χ φ φ'}

/-- The product `φ φ' E` is left invariant under `Z_n(𝔸) GL_n(F)` when `φ, φ'` are left
invariant under `GL_n(F)` and `φ φ'` transforms by `χ` under the center. -/
theorem equalSeriesProduct_central_mul
    (hφΓ : ∀ k ∈ AdelicGroupPoints.rationalSubgroup F (Scheme F (r + 1)), ∀ x,
      φ (k * x) = φ x)
    (hφ'Γ : ∀ k ∈ AdelicGroupPoints.rationalSubgroup F (Scheme F (r + 1)), ∀ x,
      φ' (k * x) = φ' x)
    (hφz : ∀ (z : Points F 1) (x : Points F (r + 1)),
      φ (scalarPoint F r z * x) * φ' (scalarPoint F r z * x) =
        (Automorphic.centralIdeleCharacter F χ (ideleOf F z) : ℂ) * (φ x * φ' x))
    {c : Points F (r + 1)} (hc : c ∈ centralRationalSubgroup F (r + 1)) (x : Points F (r + 1)) :
    equalSeriesProduct χ φ φ' Φ s (c * x) = equalSeriesProduct χ φ φ' Φ s x := by
  have hle : centralRationalSubgroup F (r + 1) ≤
      leftInvarianceSubgroup (equalSeriesProduct χ φ φ' Φ s) := by
    refine sup_le (fun c hc => ?_) (fun k hk => ?_)
    · obtain ⟨z, rfl⟩ := exists_scalarPoint_eq F r hc
      refine (mem_leftInvarianceSubgroup_iff _ _).mpr fun x => ?_
      have hχ : (Automorphic.centralIdeleCharacter F χ (ideleOf F z) : ℂ) ≠ 0 := Units.ne_zero _
      unfold equalSeriesProduct
      rw [hφz, eisensteinSeries_scalarPoint_mul χ Φ s z x, mul_mul_mul_comm,
        mul_inv_cancel₀ hχ, one_mul]
    · refine (mem_leftInvarianceSubgroup_iff _ _).mpr fun x => ?_
      unfold equalSeriesProduct
      rw [hφΓ k hk x, hφ'Γ k hk x, eisensteinSeries_rational_mul χ Φ s hk x]
  exact (mem_leftInvarianceSubgroup_iff _ _).mp (hle hc) x

/-- On the slab, `φ φ' E` is the sum over `P'_n(F) \ GL_n(F)` of the translates of
`φ φ' F(·, Φ; s, χ)`, and both sides vanish off the slab. -/
theorem slab_indicator_equalSeriesProduct
    (hφΓ : ∀ k ∈ AdelicGroupPoints.rationalSubgroup F (Scheme F (r + 1)), ∀ x,
      φ (k * x) = φ x)
    (hφ'Γ : ∀ k ∈ AdelicGroupPoints.rationalSubgroup F (Scheme F (r + 1)), ∀ x,
      φ' (k * x) = φ' x)
    (x : Points F (r + 1)) :
    (slabSet F (r + 1)).indicator (equalSeriesProduct χ φ φ' Φ s) x =
      ∑' q, (slabSet F (r + 1)).indicator (equalSectionProduct χ φ φ' Φ s)
        (eisensteinCosetRep F r q * x) := by
  by_cases hx : x ∈ slabSet F (r + 1)
  · have hq : ∀ q, eisensteinCosetRep F r q * x ∈ slabSet F (r + 1) := fun q =>
      (rational_mul_mem_slabSet_iff F (r + 1) (eisensteinCosetRep_mem F r q) x).mpr hx
    rw [indicator_of_mem hx, tsum_congr fun q => indicator_of_mem (hq q) _]
    unfold equalSeriesProduct eisensteinSeries
    rw [← tsum_mul_left]
    refine tsum_congr fun q => ?_
    unfold equalSectionProduct
    rw [hφΓ _ (eisensteinCosetRep_mem F r q) x, hφ'Γ _ (eisensteinCosetRep_mem F r q) x]
    rfl
  · have hq : ∀ q, eisensteinCosetRep F r q * x ∉ slabSet F (r + 1) := fun q h =>
      hx ((rational_mul_mem_slabSet_iff F (r + 1) (eisensteinCosetRep_mem F r q) x).mp h)
    rw [indicator_of_notMem hx]
    exact ((tsum_congr fun q => indicator_of_notMem (hq q) _).trans tsum_zero).symm

end Products

section Unfolding

/-- Step I of the equal-rank unfolding (Cogdell 2004, §2.3, p.210): for measurable `φ, φ'`
left invariant under `GL_n(F)` with `φ φ'` transforming by `χ` under the center, and with the
kernel `φ φ' Φ(e_n ·) |det|^s` integrable on the fundamental domain of `P_n(F)`, the integrand
of `I(s; φ, φ', Φ)` is integrable and `I(s; φ, φ', Φ)` is the integral of the kernel over
that fundamental domain. The masses of the bands `{c < |a| ≤ e c}` of the fundamental domain
of `GL_1(F)` are a hypothesis. -/
theorem eisenstein_unfolding
    (hslab : ∀ c : ℝ, 0 < c → ideleMeasure F (ideleDomain F ∩
      {z | c < detNorm F 1 z ∧ detNorm F 1 z ≤ Real.exp 1 * c}) = 1)
    (χ : IdeleClassGroup (𝓞 F) F →ₜ* ℂˣ) {φ φ' : Points F (r + 1) → ℂ}
    {Φ : RowVector F (r + 1) → ℂ} (s : ℂ)
    (hφm : Measurable φ) (hφ'm : Measurable φ') (hΦ : Measurable Φ)
    (hφΓ : ∀ k ∈ AdelicGroupPoints.rationalSubgroup F (Scheme F (r + 1)), ∀ x,
      φ (k * x) = φ x)
    (hφ'Γ : ∀ k ∈ AdelicGroupPoints.rationalSubgroup F (Scheme F (r + 1)), ∀ x,
      φ' (k * x) = φ' x)
    (hφz : ∀ (z : Points F 1) (x : Points F (r + 1)),
      φ (scalarPoint F r z * x) * φ' (scalarPoint F r z * x) =
        (Automorphic.centralIdeleCharacter F χ (ideleOf F z) : ℂ) * (φ x * φ' x))
    (hint : IntegrableOn (equalKernel F φ φ' Φ s) (mirabolicDomain F r) Measure.haar) :
    Integrable (equalIntegrand F χ φ φ' Φ s) (centralQuotientMeasure F (r + 1)) ∧
      equalIntegral F χ φ φ' Φ s =
        ∫ x in mirabolicDomain F r, equalKernel F φ φ' Φ s x ∂Measure.haar := by
  have hS : MeasurableSet (slabSet F (r + 1)) := measurableSet_slabSet F (r + 1)
  have hD : MeasurableSet (rationalDomain F (r + 1)) :=
    LeftCosetSpace.measurableSet_fundamentalDomain _ _
  have hfm : Measurable (equalSeriesProduct χ φ φ' Φ s) :=
    (hφm.mul hφ'm).mul (measurable_eisensteinSeries χ s hΦ)
  have hKm : Measurable (equalKernel F φ φ' Φ s) :=
    measurable_equalKernel F hφm hφ'm (measurable_lastRow_comp hΦ) s
  have hKP : ∀ p ∈ mirabolicRationalImage F r, ∀ x,
      equalKernel F φ φ' Φ s (p * x) = equalKernel F φ φ' Φ s x := by
    intro p hp x
    have hpΓ := mirabolicRationalImage_le F r hp
    unfold equalKernel
    rw [hφΓ p hpΓ x, hφ'Γ p hpΓ x, lastRow_mirabolic_mul F r hp x,
      detPower_rational_mul F (r + 1) hpΓ x s]
  have hinv : ∀ (c : centralRationalSubgroup F (r + 1)) (x : Points F (r + 1)),
      equalSeriesProduct χ φ φ' Φ s ((c : Points F (r + 1)) * x) =
        equalSeriesProduct χ φ φ' Φ s x :=
    fun c x => equalSeriesProduct_central_mul Φ s hφΓ hφ'Γ hφz c.property x
  -- The fiber computation over `(D' ∩ S) × 𝔸^×`.
  obtain ⟨hprod, hprodEq⟩ := integrable_and_integral_slabFiber F r hslab hKm hKP hint
  have hgeq : ∀ x, equalSectionProduct χ φ φ' Φ s x =
      ∫ z, equalKernel F φ φ' Φ s (scalarPoint F r z * x) ∂ideleMeasure F :=
    fun x => mul_eisensteinSection_eq_integral (Φ := Φ) (s := s) hφz x
  have hgint : IntegrableOn (equalSectionProduct χ φ φ' Φ s)
      (eisensteinDomain F r ∩ slabSet F (r + 1)) Measure.haar :=
    hprod.integral_prod_left.congr (Filter.Eventually.of_forall fun x => (hgeq x).symm)
  have hhint : IntegrableOn ((slabSet F (r + 1)).indicator (equalSectionProduct χ φ φ' Φ s))
      (eisensteinDomain F r) Measure.haar := by
    show Integrable _ ((Measure.haar : Measure (Points F (r + 1))).restrict (eisensteinDomain F r))
    rw [integrable_indicator_iff hS]
    show Integrable _ (((Measure.haar : Measure (Points F (r + 1))).restrict
      (eisensteinDomain F r)).restrict (slabSet F (r + 1)))
    rw [Measure.restrict_restrict hS, inter_comm]
    exact hgint
  -- Unfold the sum over `P'_n(F) \ GL_n(F)` against the fundamental domain of `GL_n(F)`.
  obtain ⟨hDint, hDeq⟩ := integrableOn_tsum_and_setIntegral_eq
    (Measure.haar : Measure (Points F (r + 1))) hD
    (LeftCosetSpace.fundamentalDomain_unique _ _) (eisensteinCosetRep F r)
    (eisensteinCosetRep_mem F r) (fun _ hk => existsUnique_eisensteinCosetRep F r hk) hhint
  have hser : (fun x => ∑' q, (slabSet F (r + 1)).indicator (equalSectionProduct χ φ φ' Φ s)
      (eisensteinCosetRep F r q * x)) =
        (slabSet F (r + 1)).indicator (equalSeriesProduct χ φ φ' Φ s) :=
    funext fun x => (slab_indicator_equalSeriesProduct Φ s hφΓ hφ'Γ x).symm
  rw [hser] at hDint hDeq
  have hfint : IntegrableOn (equalSeriesProduct χ φ φ' Φ s)
      (slabSet F (r + 1) ∩ rationalDomain F (r + 1)) Measure.haar := by
    have h1 : Integrable ((slabSet F (r + 1)).indicator (equalSeriesProduct χ φ φ' Φ s))
        ((Measure.haar : Measure (Points F (r + 1))).restrict (rationalDomain F (r + 1))) := hDint
    rw [integrable_indicator_iff hS] at h1
    have h2 : Integrable (equalSeriesProduct χ φ φ' Φ s)
        (((Measure.haar : Measure (Points F (r + 1))).restrict
          (rationalDomain F (r + 1))).restrict (slabSet F (r + 1))) := h1
    rwa [Measure.restrict_restrict hS] at h2
  refine ⟨?_, ?_⟩
  · rw [equalIntegrand_eq, centralQuotientMeasure_eq F (r + 1)]
    exact (integrable_out_iff _ hfm hinv _ _).mpr hfint
  · calc equalIntegral F χ φ φ' Φ s
        = ∫ q, equalSeriesProduct χ φ φ' Φ s q.out ∂centralQuotientMeasure F (r + 1) := rfl
      _ = ∫ x in slabSet F (r + 1) ∩ rationalDomain F (r + 1),
            equalSeriesProduct χ φ φ' Φ s x ∂Measure.haar := by
          rw [centralQuotientMeasure_eq F (r + 1)]
          exact integral_out_eq _ hfm hinv _ _
      _ = ∫ x in rationalDomain F (r + 1),
            (slabSet F (r + 1)).indicator (equalSeriesProduct χ φ φ' Φ s) x ∂Measure.haar := by
          rw [setIntegral_indicator hS, inter_comm]
      _ = ∫ x in eisensteinDomain F r,
            (slabSet F (r + 1)).indicator (equalSectionProduct χ φ φ' Φ s) x ∂Measure.haar :=
          hDeq
      _ = ∫ x in eisensteinDomain F r ∩ slabSet F (r + 1),
            equalSectionProduct χ φ φ' Φ s x ∂Measure.haar :=
          setIntegral_indicator hS
      _ = ∫ x in eisensteinDomain F r ∩ slabSet F (r + 1),
            ∫ z, equalKernel F φ φ' Φ s (scalarPoint F r z * x) ∂ideleMeasure F
              ∂Measure.haar :=
          integral_congr_ae (Filter.Eventually.of_forall hgeq)
      _ = ∫ q, equalKernel F φ φ' Φ s (scalarPoint F r q.2 * q.1)
            ∂(((Measure.haar : Measure (Points F (r + 1))).restrict
              (eisensteinDomain F r ∩ slabSet F (r + 1))).prod (ideleMeasure F)) :=
          (integral_prod _ hprod).symm
      _ = ∫ x in mirabolicDomain F r, equalKernel F φ φ' Φ s x ∂Measure.haar := hprodEq

end Unfolding

end Langlands.Global.RankinSelbergGlobal.EqualUnfolding
