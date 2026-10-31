import Langlands.Representation.GodementJacquet.TwoBlockZetaExpansion
import Langlands.Representation.Induction.CompactPairingDuality

/-!
# Reverse realization of products of block zeta integrals

Godement–Jacquet 1972, Theorem 3.4 (printed 43–45), for two blocks, by a direct
construction instead of Lemma 3.4.6: for block tests `Φ₀, Φ₁` and actual block
bi-smooth coefficients, a test `Φ` supported near the upper block-triangular
matrices and induced sections supported on `P K₀` realize a nonzero constant times
the product of the two block zeta integrals as an induced matrix zeta integral.
-/

noncomputable section

open MeasureTheory
open scoped NNReal ENNReal

namespace Langlands.GodementJacquet.TwoBlock

open GeneralLinear RankinSelberg HarmonicAnalysis

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance : TopologicalSpace F.Carrier := F.canonicalTopologicalData.topology
local instance : ValuativeRel F.Carrier := F.canonicalTopologicalData.valuativeRel
local instance : IsNonarchimedeanLocalField F.Carrier := F.canonicalTopologicalData.localField
local instance : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2
local instance : SecondCountableTopology F.Carrier :=
  F.canonicalTopologicalData.secondCountableTopology
local instance : MeasurableSpace F.Carrier := borel _
local instance : BorelSpace F.Carrier := ⟨rfl⟩
local instance (n : ℕ) : MeasurableSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := borel _
local instance (n : ℕ) : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩

attribute [local instance] glSecondCountable matrixLocallyCompact matrixSecondCountable
  glLocallyCompact

variable {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1)

/-- The open set `P K₀` of products of an element of the upper two-block parabolic and
an element of `K₀`. -/
def parabolicCompactSet (K₀ : OpenSubgroup (Langlands.GeneralLinear (t + 1) F.Carrier)) :
    Set (Langlands.GeneralLinear (t + 1) F.Carrier) :=
  {y | ∃ (q : (succBlockShape m h).parabolic F.Carrier) (l : K₀),
    y = (q : Langlands.GeneralLinear (t + 1) F.Carrier) * (l : Langlands.GeneralLinear (t + 1) F.Carrier)}

theorem isOpen_parabolicCompactSet (K₀ : OpenSubgroup (Langlands.GeneralLinear (t + 1) F.Carrier)) :
    IsOpen (parabolicCompactSet F h K₀) := by
  have he : parabolicCompactSet F h K₀ = ⋃ q : (succBlockShape m h).parabolic F.Carrier,
      (fun l => (q : Langlands.GeneralLinear (t + 1) F.Carrier) * l) ''
        (K₀ : Set (Langlands.GeneralLinear (t + 1) F.Carrier)) := by
    ext y
    simp only [parabolicCompactSet, Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_image,
      SetLike.mem_coe]
    constructor
    · rintro ⟨q, l, rfl⟩
      exact ⟨q, l, l.property, rfl⟩
    · rintro ⟨q, l, hl, rfl⟩
      exact ⟨q, ⟨l, hl⟩, rfl⟩
  rw [he]
  exact isOpen_iUnion fun q => isOpenMap_mul_left _ _ K₀.isOpen

/-- **Reverse computation for a kernel supported on `P K₀`.** Let `K₀ ≤ K` be compact open
subgroups, `ν` a finite measure on `K`, and `Γ` a continuous kernel on `K × GL_(t+1)` that
vanishes for `k ∉ P K₀` and, for `k = q l` with `q ∈ P`, `l ∈ K₀`, is the left translate
`y ↦ Γ₀ (q⁻¹ y)` of a continuous `Γ₀` supported on `P K₀` with
`Γ₀ (parabolicPoint (L, x) l) = δ_P(L)^(1/2) c₀(a) c₁(d)`. For a test `Φ` invariant on both
sides under `K₀` and an `s` at which all block tests converge against `c₀` and `c₁`, the
coefficient `g ↦ ∫ k, Γ k (k g) dν` has convergent zeta integral at `s + t/2`, equal to an
explicit constant times the Levi integral of `Φ^P`. -/
theorem reverse_zeta_of_kernel
    (K : OpenSubgroup (Langlands.GeneralLinear (t + 1) F.Carrier))
    (K₀ : OpenSubgroup (Langlands.GeneralLinear (t + 1) F.Carrier))
    (hK₀ : IsCompact (K₀ : Set (Langlands.GeneralLinear (t + 1) F.Carrier)))
    [MeasurableSpace K] [BorelSpace K] (ν : Measure K) [IsFiniteMeasure ν]
    (Γ : K → Langlands.GeneralLinear (t + 1) F.Carrier → ℂ)
    (hΓ : Continuous fun z : K × Langlands.GeneralLinear (t + 1) F.Carrier => Γ z.1 z.2)
    (Γ₀ : Langlands.GeneralLinear (t + 1) F.Carrier → ℂ) (hΓ₀c : Continuous Γ₀)
    (hsupp : ∀ k : K, (k : Langlands.GeneralLinear (t + 1) F.Carrier) ∉ parabolicCompactSet F h K₀ →
      ∀ y, Γ k y = 0)
    (htrans : ∀ (k : K) (q : (succBlockShape m h).parabolic F.Carrier) (l : K₀),
      (k : Langlands.GeneralLinear (t + 1) F.Carrier) =
        (q : Langlands.GeneralLinear (t + 1) F.Carrier) * (l : Langlands.GeneralLinear (t + 1) F.Carrier) →
      ∀ y, Γ k y = Γ₀ ((q : Langlands.GeneralLinear (t + 1) F.Carrier)⁻¹ * y))
    (hΓ₀supp : ∀ y, y ∉ parabolicCompactSet F h K₀ → Γ₀ y = 0)
    (c₀ : Langlands.GeneralLinear (m 0 + 1) F.Carrier → ℂ)
    (c₁ : Langlands.GeneralLinear (m 1 + 1) F.Carrier → ℂ)
    (hc₀ : Continuous c₀) (hc₁ : Continuous c₁)
    (hΓ₀ : ∀ (L : (succBlockShape m h).Levi F.Carrier)
      (x : Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F.Carrier) (l : K₀),
      Γ₀ (parabolicPoint h (L, x) * l) = halfModulus F h L * (c₀ (L 0) * c₁ (L 1)))
    (Φ : MatrixTestFunction t F.Carrier)
    (hΦ : ∀ (l l' : K₀) (X : Matrix (Fin (t + 1)) (Fin (t + 1)) F.Carrier),
      Φ ((l : Langlands.GeneralLinear (t + 1) F.Carrier).val * X *
        (l' : Langlands.GeneralLinear (t + 1) F.Carrier).val) = Φ X)
    (s : ℂ)
    (h₀ : ∀ α : MatrixTestFunction (m 0) F.Carrier,
      Padic.MatrixConverges F α (s + jpssShift (m 0)) c₀)
    (h₁ : ∀ α : MatrixTestFunction (m 1) F.Carrier,
      Padic.MatrixConverges F α (s + jpssShift (m 1)) c₁) :
    Padic.MatrixConverges F Φ (s + jpssShift t)
        (fun g => ∫ k, Γ k ((k : Langlands.GeneralLinear (t + 1) F.Carrier) * g) ∂ν) ∧
      Padic.matrixIntegral F Φ (s + jpssShift t)
          (fun g => ∫ k, Γ k ((k : Langlands.GeneralLinear (t + 1) F.Carrier) * g) ∂ν) =
        (((ν {k : K | (k : Langlands.GeneralLinear (t + 1) F.Carrier) ∈
              parabolicCompactSet F h K₀}).toReal *
            ((parabolicMeasure F h Measure.addHaar (parabolicPoint h ⁻¹'
              (K₀ : Set (Langlands.GeneralLinear (t + 1) F.Carrier)))).toReal)⁻¹ *
            (generalLinearHaar F.Carrier t
              (K₀ : Set (Langlands.GeneralLinear (t + 1) F.Carrier))).toReal : ℝ) : ℂ) *
          ∫ L, upperBlockIntegral h Φ Measure.addHaar ((L 0).val, (L 1).val) *
            (leviCoefficientWeight F h c₀ c₁ s L * radicalWeight F h L)
            ∂(Measure.pi fun i : Fin 2 => generalLinearHaar F.Carrier (m i)) := by
  classical
  have hK2 : SecondCountableTopology K :=
    TopologicalSpace.Subtype.secondCountableTopology
      (K : Set (Langlands.GeneralLinear (t + 1) F.Carrier))
  set μ := generalLinearHaar F.Carrier t with hμ
  set dx : Measure (Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F.Carrier) := Measure.addHaar
    with hdx
  set ρ := parabolicMeasure F h dx with hρ
  set S' := parabolicCompactSet F h K₀ with hS'def
  have hS'o : IsOpen S' := isOpen_parabolicCompactSet F h K₀
  set S : Set K := {k | (k : Langlands.GeneralLinear (t + 1) F.Carrier) ∈ S'} with hSdef
  have hSm : MeasurableSet S := (hS'o.preimage continuous_subtype_val).measurableSet
  have hK₀m : MeasurableSet (K₀ : Set (Langlands.GeneralLinear (t + 1) F.Carrier)) :=
    K₀.isOpen.measurableSet
  set H : Langlands.GeneralLinear (t + 1) F.Carrier → ℂ := fun g =>
    Φ g.val * determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData) g
      (s + jpssShift t) with hH
  set U := leviCoefficientWeight F h c₀ c₁ s with hU
  set Ψ₀ : Langlands.GeneralLinear (t + 1) F.Carrier → ℂ := fun y => H y * Γ₀ y with hΨ₀def
  set Q : (succBlockShape m h).Levi F.Carrier ×
      Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F.Carrier → ℂ := fun z =>
    Φ (parabolicPoint h z).val * U z.1 with hQdef
  have hHc : Continuous H :=
    (Φ.continuous.comp Units.continuous_val).mul (continuous_determinantWeight' F t _)
  -- invariance of `H` under `K₀`
  have hHleft : ∀ (l : K₀) (y : Langlands.GeneralLinear (t + 1) F.Carrier),
      H ((l : Langlands.GeneralLinear (t + 1) F.Carrier)⁻¹ * y) = H y := by
    intro l y
    have h1 : Φ ((l : Langlands.GeneralLinear (t + 1) F.Carrier)⁻¹ * y).val = Φ y.val := by
      have := hΦ l⁻¹ 1 y.val
      simpa using this
    have h2 := determinantWeight_mul_of_mem F K₀.toSubgroup hK₀ l.property K₀.one_mem y
      (s + jpssShift t)
    rw [mul_one] at h2
    simp only [hH, h1, h2]
  have hHright : ∀ (l : K₀) (y : Langlands.GeneralLinear (t + 1) F.Carrier),
      H (y * (l : Langlands.GeneralLinear (t + 1) F.Carrier)) = H y := by
    intro l y
    have h1 : Φ (y * (l : Langlands.GeneralLinear (t + 1) F.Carrier)).val = Φ y.val := by
      have := hΦ 1 l y.val
      simpa using this
    have h2 := determinantWeight_mul_of_mem F K₀.toSubgroup hK₀ K₀.one_mem l.property y
      (s + jpssShift t)
    rw [inv_one, one_mul] at h2
    simp only [hH, h1, h2]
  -- the parabolic reduction for `Q`
  have hUc : Continuous U := continuous_leviCoefficientWeight F h c₀ c₁ s hc₀ hc₁
  have hPs := integral_testFunction_parabolicPoint F h dx Φ U hUc.aestronglyMeasurable
    (integrable_leviCoefficientWeight F h c₀ c₁ s h₀ h₁)
  have hQeq : ∀ (z : (succBlockShape m h).Levi F.Carrier ×
      Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F.Carrier) (l : K₀),
      Ψ₀ (parabolicPoint h z * (l : Langlands.GeneralLinear (t + 1) F.Carrier)) = Q z := by
    rintro ⟨L, x⟩ l
    simp only [hΨ₀def, hQdef, hU, leviCoefficientWeight]
    rw [hHright, hΓ₀]
    simp only [hH, determinantWeight, det_parabolicPoint]
    ring
  -- integrability and integral of `Ψ₀` through the factorization over `K₀`
  have hSfac : ∀ y ∈ S', ∃ z, ∃ k₀ ∈ K₀.toSubgroup, y = parabolicPoint h z * k₀ := by
    rintro y ⟨q, l, rfl⟩
    exact ⟨parabolicCoord h q, l, l.property, by rw [parabolicPoint_parabolicCoord]⟩
  have hSK : ∀ z, ∀ k ∈ K₀.toSubgroup, parabolicPoint h z * k ∈ S' := fun z k hk =>
    ⟨⟨parabolicPoint h z, parabolicPoint_mem h z⟩, ⟨k, hk⟩, rfl⟩
  have hpos := parabolicMeasure_preimage_ne_zero F h dx K₀
  have hfin := parabolicMeasure_preimage_ne_top F h dx K₀.toSubgroup hK₀
  have hΨ₀c : Continuous Ψ₀ := hHc.mul hΓ₀c
  have hfinK₀ : IsFiniteMeasure (μ.restrict (K₀ : Set (Langlands.GeneralLinear (t + 1) F.Carrier))) :=
    isFiniteMeasure_restrict.mpr hK₀.measure_lt_top.ne
  have hcompint : Integrable (fun p : Langlands.GeneralLinear (t + 1) F.Carrier ×
      ((succBlockShape m h).Levi F.Carrier × Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F.Carrier) =>
      Ψ₀ (parabolicPoint h p.2 * p.1))
      ((μ.restrict (K₀ : Set (Langlands.GeneralLinear (t + 1) F.Carrier))).prod ρ) := by
    have h1 : Integrable (fun p : Langlands.GeneralLinear (t + 1) F.Carrier ×
        ((succBlockShape m h).Levi F.Carrier ×
          Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F.Carrier) => (1 : ℂ) * Q p.2)
        ((μ.restrict (K₀ : Set (Langlands.GeneralLinear (t + 1) F.Carrier))).prod ρ) :=
      (integrable_const (1 : ℂ)).mul_prod hPs.1
    refine h1.congr ?_
    have hae : ∀ᵐ p ∂((μ.restrict (K₀ : Set (Langlands.GeneralLinear (t + 1) F.Carrier))).prod ρ),
        p.1 ∈ (K₀ : Set (Langlands.GeneralLinear (t + 1) F.Carrier)) :=
      Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem hK₀m)
    filter_upwards [hae] with p hp
    rw [one_mul, hQeq p.2 ⟨p.1, hp⟩]
  have hS'int := (CompactFactorization.integrable_comp_mul_iff_of_subset μ K₀.toSubgroup hK₀m ρ
    (parabolicPoint h) (measurable_parabolicPoint F h) (parabolicPoint_translation F h dx) S'
    hS'o.measurableSet hSfac hSK hpos hfin hΨ₀c.aestronglyMeasurable).mp hcompint
  have hsuppΨ : Function.support Ψ₀ ⊆ S' := by
    intro y hy
    by_contra hn
    exact hy (by simp only [hΨ₀def, hΓ₀supp y hn, mul_zero])
  have hΨ₀int : Integrable Ψ₀ μ := (integrableOn_iff_integrable_of_support_subset hsuppΨ).mp hS'int
  have hval0 := CompactFactorization.integral_restrict_integral_mul_of_subset μ K₀.toSubgroup
    hK₀m ρ (parabolicPoint h) (measurable_parabolicPoint F h) (parabolicPoint_translation F h dx)
    S' hS'o.measurableSet hSfac hSK hpos hfin hS'int
  have hLHS : ∫ k in (K₀ : Set (Langlands.GeneralLinear (t + 1) F.Carrier)),
      ∫ z, Ψ₀ (parabolicPoint h z * k) ∂ρ ∂μ =
        μ.real (K₀ : Set (Langlands.GeneralLinear (t + 1) F.Carrier)) • ∫ z, Q z ∂ρ := by
    rw [setIntegral_congr_fun hK₀m (fun k hk => integral_congr_ae
      (Filter.Eventually.of_forall fun z => hQeq z ⟨k, hk⟩)), setIntegral_const]
  have hRHS : ∫ y in S', Ψ₀ y ∂μ = ∫ y, Ψ₀ y ∂μ :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy => by
      simp only [hΨ₀def, hΓ₀supp y hy, mul_zero]
  have hρne : (ρ (parabolicPoint h ⁻¹'
      (K₀ : Set (Langlands.GeneralLinear (t + 1) F.Carrier)))).toReal ≠ 0 :=
    ENNReal.toReal_ne_zero.mpr ⟨hpos, hfin⟩
  have hΨval : ∫ y, Ψ₀ y ∂μ = ((ρ (parabolicPoint h ⁻¹'
      (K₀ : Set (Langlands.GeneralLinear (t + 1) F.Carrier)))).toReal)⁻¹ •
      μ.real (K₀ : Set (Langlands.GeneralLinear (t + 1) F.Carrier)) • ∫ z, Q z ∂ρ := by
    have hval0' : ∫ k in (K₀ : Set (Langlands.GeneralLinear (t + 1) F.Carrier)),
        ∫ z, Ψ₀ (parabolicPoint h z * k) ∂ρ ∂μ =
          (ρ (parabolicPoint h ⁻¹' (K₀ : Set (Langlands.GeneralLinear (t + 1) F.Carrier)))).toReal •
            ∫ y in S', Ψ₀ y ∂μ := hval0
    rw [← hLHS, hval0', hRHS, smul_smul, inv_mul_cancel₀ hρne, one_smul]
  -- the coefficient integral through the compact translates
  have hm : AEStronglyMeasurable (fun z : K × Langlands.GeneralLinear (t + 1) F.Carrier =>
      H ((z.1 : Langlands.GeneralLinear (t + 1) F.Carrier)⁻¹ * z.2) * Γ z.1 z.2) (ν.prod μ) :=
    ((hHc.comp ((continuous_subtype_val.comp continuous_fst).inv.mul continuous_snd)).mul
      hΓ).aestronglyMeasurable
  have htrans' : ∀ k ∈ S, ∃ g₀ : Langlands.GeneralLinear (t + 1) F.Carrier,
      ∀ y, H ((k : Langlands.GeneralLinear (t + 1) F.Carrier)⁻¹ * y) * Γ k y = Ψ₀ (g₀ * y) := by
    rintro k ⟨q, l, hkql⟩
    refine ⟨(q : Langlands.GeneralLinear (t + 1) F.Carrier)⁻¹, fun y => ?_⟩
    have e : (k : Langlands.GeneralLinear (t + 1) F.Carrier)⁻¹ * y =
        (l : Langlands.GeneralLinear (t + 1) F.Carrier)⁻¹ *
          ((q : Langlands.GeneralLinear (t + 1) F.Carrier)⁻¹ * y) := by
      rw [hkql, mul_inv_rev, mul_assoc]
    rw [htrans k q l hkql y, e, hHleft]
  have hzero : ∀ k ∉ S, ∀ y,
      H ((k : Langlands.GeneralLinear (t + 1) F.Carrier)⁻¹ * y) * Γ k y = 0 :=
    fun k hk y => by rw [hsupp k hk y, mul_zero]
  obtain ⟨hint, hval⟩ := CompactFactorization.integrable_integral_coefficient_of_translate μ ν
    Subtype.val continuous_subtype_val.measurable H Γ hm S hSm Ψ₀ hΨ₀int htrans' hzero
  have hfun : GodementJacquet.matrixIntegrand (normalizedAbsoluteValue F.canonicalTopologicalData)
      Φ (s + jpssShift t)
      (fun g => ∫ k, Γ k ((k : Langlands.GeneralLinear (t + 1) F.Carrier) * g) ∂ν) =
      fun g => H g * ∫ k, Γ k ((k : Langlands.GeneralLinear (t + 1) F.Carrier) * g) ∂ν := by
    funext g
    simp only [GodementJacquet.matrixIntegrand, hH]
    ring
  refine ⟨?_, ?_⟩
  · change Integrable (GodementJacquet.matrixIntegrand _ Φ (s + jpssShift t) _) μ
    rw [hfun]
    exact hint
  · change ∫ g, GodementJacquet.matrixIntegrand _ Φ (s + jpssShift t) _ g ∂μ = _
    have hQ' : ∫ z, Q z ∂ρ = ∫ L, upperBlockIntegral h Φ Measure.addHaar ((L 0).val, (L 1).val) *
        (leviCoefficientWeight F h c₀ c₁ s L * radicalWeight F h L)
        ∂(Measure.pi fun i : Fin 2 => generalLinearHaar F.Carrier (m i)) := hPs.2
    rw [hfun, hval, hΨval, hQ', smul_smul, smul_smul, Complex.real_smul]
    rfl

section Tests

/-- The compact open box of integral rectangular matrices. -/
def integralBox (r s : ℕ) : Set (Matrix (Fin r) (Fin s) F.Carrier) :=
  Set.univ.pi fun _ => Set.univ.pi fun _ => (F.canonicalTopologicalData.Integers : Set F.Carrier)

theorem isCompact_integralBox (r s : ℕ) : IsCompact (integralBox F r s) :=
  isCompact_univ_pi fun _ => isCompact_univ_pi fun _ =>
    F.canonicalTopologicalData.isCompact_integers

theorem isOpen_integralBox (r s : ℕ) : IsOpen (integralBox F r s) :=
  isOpen_set_pi Set.finite_univ fun _ _ => isOpen_set_pi Set.finite_univ fun _ _ =>
    F.canonicalTopologicalData.isOpen_integers

theorem zero_mem_integralBox (r s : ℕ) : (0 : Matrix (Fin r) (Fin s) F.Carrier) ∈ integralBox F r s :=
  fun _ _ _ _ => (F.canonicalTopologicalData.Integers).zero_mem

/-- The indicator of the integral box, a Schwartz–Bruhat function with value `1` at `0`. -/
def integralBoxTest (r s : ℕ) : SchwartzBruhat (Matrix (Fin r) (Fin s) F.Carrier) :=
  ⟨(integralBox F r s).indicator fun _ => 1,
    ((LocallyConstant.const _ (1 : ℂ)).indicator
      ⟨(isCompact_integralBox F r s).isClosed, isOpen_integralBox F r s⟩).isLocallyConstant,
    HasCompactSupport.intro (isCompact_integralBox F r s)
      (fun _ hx => Set.indicator_of_notMem hx _)⟩

theorem integralBoxTest_apply (r s : ℕ) (X : Matrix (Fin r) (Fin s) F.Carrier) :
    integralBoxTest F r s X = (integralBox F r s).indicator (fun _ => (1 : ℂ)) X := rfl

theorem integralBoxTest_zero (r s : ℕ) : integralBoxTest F r s 0 = 1 := by
  rw [integralBoxTest_apply, Set.indicator_of_mem (zero_mem_integralBox F r s)]

/-- The four blocks `((A, D), B), C` of a matrix in the block convention. -/
def blockSplit (X : Matrix (Fin (t + 1)) (Fin (t + 1)) F.Carrier) :
    ((Matrix (Fin (m 0 + 1)) (Fin (m 0 + 1)) F.Carrier × Matrix (Fin (m 1 + 1)) (Fin (m 1 + 1)) F.Carrier) ×
      Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F.Carrier) × Matrix (Fin (m 1 + 1)) (Fin (m 0 + 1)) F.Carrier :=
  let Y := Matrix.reindex (blockEquiv h).symm (blockEquiv h).symm X
  (((Y.toBlocks₁₁, Y.toBlocks₂₂), Y.toBlocks₁₂), Y.toBlocks₂₁)

/-- The matrix with prescribed blocks `((A, D), B), C`. -/
def blockJoin (w : ((Matrix (Fin (m 0 + 1)) (Fin (m 0 + 1)) F.Carrier ×
      Matrix (Fin (m 1 + 1)) (Fin (m 1 + 1)) F.Carrier) ×
      Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F.Carrier) × Matrix (Fin (m 1 + 1)) (Fin (m 0 + 1)) F.Carrier) :
    Matrix (Fin (t + 1)) (Fin (t + 1)) F.Carrier :=
  Matrix.reindex (blockEquiv h) (blockEquiv h) (Matrix.fromBlocks w.1.1.1 w.1.2 w.2 w.1.1.2)

theorem blockJoin_blockSplit (X : Matrix (Fin (t + 1)) (Fin (t + 1)) F.Carrier) :
    blockJoin F h (blockSplit F h X) = X := by
  simp only [blockJoin, blockSplit, Matrix.fromBlocks_toBlocks]
  ext i j
  simp

theorem blockSplit_upper (A : Matrix (Fin (m 0 + 1)) (Fin (m 0 + 1)) F.Carrier)
    (B : Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F.Carrier)
    (D : Matrix (Fin (m 1 + 1)) (Fin (m 1 + 1)) F.Carrier) :
    blockSplit F h (Matrix.reindex (blockEquiv h) (blockEquiv h) (Matrix.fromBlocks A B 0 D)) =
      (((A, D), B), 0) := by
  simp [blockSplit]

theorem continuous_blockSplit : Continuous (blockSplit F h) := by
  refine (((?_ : Continuous _).prodMk (?_ : Continuous _)).prodMk (?_ : Continuous _)).prodMk
    (?_ : Continuous _)
  · exact continuous_pi fun i => continuous_pi fun j =>
      continuous_id.matrix_elem ((blockEquiv h) (Sum.inl i)) ((blockEquiv h) (Sum.inl j))
  · exact continuous_pi fun i => continuous_pi fun j =>
      continuous_id.matrix_elem ((blockEquiv h) (Sum.inr i)) ((blockEquiv h) (Sum.inr j))
  · exact continuous_pi fun i => continuous_pi fun j =>
      continuous_id.matrix_elem ((blockEquiv h) (Sum.inl i)) ((blockEquiv h) (Sum.inr j))
  · exact continuous_pi fun i => continuous_pi fun j =>
      continuous_id.matrix_elem ((blockEquiv h) (Sum.inr i)) ((blockEquiv h) (Sum.inl j))

theorem continuous_blockJoin : Continuous (blockJoin F h) := by
  unfold blockJoin
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply]
  rcases (blockEquiv h).symm i with a | a <;> rcases (blockEquiv h).symm j with b | b
  · exact (continuous_apply_apply a b).comp
      (continuous_fst.comp (continuous_fst.comp continuous_fst))
  · exact (continuous_apply_apply a b).comp (continuous_snd.comp continuous_fst)
  · exact (continuous_apply_apply a b).comp continuous_snd
  · exact (continuous_apply_apply a b).comp
      (continuous_snd.comp (continuous_fst.comp continuous_fst))

/-- The test `X ↦ Φ₀(A) Φ₁(D) 1_box(B) 1_box(C)` for the blocks `[[A, B], [C, D]]` of `X`. -/
def reverseTest (Φ₀ : MatrixTestFunction (m 0) F.Carrier) (Φ₁ : MatrixTestFunction (m 1) F.Carrier) :
    MatrixTestFunction t F.Carrier :=
  SchwartzBruhat.compLeftInverse
    (SchwartzBruhat.tensor (SchwartzBruhat.tensor (SchwartzBruhat.tensor Φ₀ Φ₁)
      (integralBoxTest F (m 0 + 1) (m 1 + 1))) (integralBoxTest F (m 1 + 1) (m 0 + 1)))
    (blockSplit F h) (blockJoin F h) (continuous_blockSplit F h) (continuous_blockJoin F h)
    (blockJoin_blockSplit F h)

theorem reverseTest_upper (Φ₀ : MatrixTestFunction (m 0) F.Carrier)
    (Φ₁ : MatrixTestFunction (m 1) F.Carrier) (A : Matrix (Fin (m 0 + 1)) (Fin (m 0 + 1)) F.Carrier)
    (B : Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F.Carrier)
    (D : Matrix (Fin (m 1 + 1)) (Fin (m 1 + 1)) F.Carrier) :
    reverseTest F h Φ₀ Φ₁ (Matrix.reindex (blockEquiv h) (blockEquiv h) (Matrix.fromBlocks A B 0 D)) =
      Φ₀ A * Φ₁ D * integralBoxTest F (m 0 + 1) (m 1 + 1) B := by
  change SchwartzBruhat.tensor (SchwartzBruhat.tensor (SchwartzBruhat.tensor Φ₀ Φ₁)
      (integralBoxTest F (m 0 + 1) (m 1 + 1))) (integralBoxTest F (m 1 + 1) (m 0 + 1))
      (blockSplit F h (Matrix.reindex (blockEquiv h) (blockEquiv h) (Matrix.fromBlocks A B 0 D))) = _
  rw [blockSplit_upper]
  simp only [SchwartzBruhat.tensor_apply, integralBoxTest_zero, mul_one]

/-- The upper-block integral of the reverse test is the product of the block tests. -/
theorem upperBlockIntegral_reverseTest (Φ₀ : MatrixTestFunction (m 0) F.Carrier)
    (Φ₁ : MatrixTestFunction (m 1) F.Carrier)
    (dx : Measure (Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F.Carrier)) [IsFiniteMeasureOnCompacts dx]
    (A : Matrix (Fin (m 0 + 1)) (Fin (m 0 + 1)) F.Carrier)
    (D : Matrix (Fin (m 1 + 1)) (Fin (m 1 + 1)) F.Carrier) :
    upperBlockIntegral h (reverseTest F h Φ₀ Φ₁) dx (A, D) =
      ((dx (integralBox F (m 0 + 1) (m 1 + 1))).toReal : ℂ) * (Φ₀ A * Φ₁ D) := by
  rw [upperBlockIntegral_apply]
  simp only [reverseTest_upper, integralBoxTest_apply]
  rw [integral_const_mul, integral_indicator_const _ (isOpen_integralBox F _ _).measurableSet,
    Complex.real_smul, mul_one, measureReal_def]
  ring

end Tests

section Subgroups

/-- A full-matrix test is invariant on both sides under some compact open subgroup
contained in any prescribed open subgroup. -/
theorem exists_compactOpen_biInvariant (Φ : MatrixTestFunction t F.Carrier)
    (U : OpenSubgroup (Langlands.GeneralLinear (t + 1) F.Carrier)) :
    ∃ K₀ : OpenSubgroup (Langlands.GeneralLinear (t + 1) F.Carrier),
      IsCompact (K₀ : Set (Langlands.GeneralLinear (t + 1) F.Carrier)) ∧ K₀ ≤ U ∧
      ∀ (l l' : K₀) (X : Matrix (Fin (t + 1)) (Fin (t + 1)) F.Carrier),
        Φ ((l : Langlands.GeneralLinear (t + 1) F.Carrier).val * X *
          (l' : Langlands.GeneralLinear (t + 1) F.Carrier).val) = Φ X := by
  have hW := eventually_matrixTranslate_eq Φ
  obtain ⟨u, hu, v, hv, huv⟩ := mem_nhds_prod_iff.mp hW
  have hN : u ∩ v ∩ (U : Set (Langlands.GeneralLinear (t + 1) F.Carrier)) ∈
      nhds (1 : Langlands.GeneralLinear (t + 1) F.Carrier) :=
    Filter.inter_mem (Filter.inter_mem hu hv) U.mem_nhds_one
  have : NonarchimedeanGroup (Langlands.GeneralLinear (t + 1) F.Carrier) :=
    F.canonicalTopologicalData.generalLinearNonarchimedean (t + 1)
  obtain ⟨L, hLc, hLN⟩ := compactOpenSubgroupBasis _ _ hN
  refine ⟨L, hLc, fun x hx => (hLN hx).2, fun l l' X => ?_⟩
  have hmem : ((l : Langlands.GeneralLinear (t + 1) F.Carrier),
      (l' : Langlands.GeneralLinear (t + 1) F.Carrier)) ∈ u ×ˢ v :=
    ⟨(hLN l.property).1.1, (hLN l'.property).1.2⟩
  exact huv hmem X

/-- The modulus of the upper two-block parabolic is trivial on elements of a compact
subgroup. -/
theorem leviModulus_eq_one_of_mem (K : Subgroup (Langlands.GeneralLinear (t + 1) F.Carrier))
    (hK : IsCompact (K : Set (Langlands.GeneralLinear (t + 1) F.Carrier)))
    (q : (succBlockShape m h).parabolic F.Carrier)
    (hq : (q : Langlands.GeneralLinear (t + 1) F.Carrier) ∈ K) :
    F.canonicalTopologicalData.leviModulus (succBlockShape m h)
      ((succBlockShape m h).leviProjection F.Carrier q) = 1 := by
  have hχ : Continuous ((F.canonicalTopologicalData.leviModulus (succBlockShape m h)).comp
      ((succBlockShape m h).leviProjection F.Carrier)) :=
    (F.canonicalTopologicalData.continuous_leviModulus (succBlockShape m h)).comp
      ((succBlockShape m h).leviProjectionContinuous F.Carrier).continuous
  have hJ : IsCompact ((K.comap ((succBlockShape m h).parabolic F.Carrier).subtype :
      Subgroup ((succBlockShape m h).parabolic F.Carrier)) :
        Set ((succBlockShape m h).parabolic F.Carrier)) :=
    ((succBlockShape m h).isClosed_parabolic F.Carrier).isClosedEmbedding_subtypeVal.isCompact_preimage
      hK
  exact RankinSelberg.LastRowReduction.eq_one_of_isCompact _ hχ _ hJ hq

end Subgroups

section Realization

theorem smoothDualPairing_smoothContragredient {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] {W : Type*} [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ G W)
    (g : G) (lam : SmoothDual ρ) (x : W) :
    smoothDualPairing ρ (smoothContragredient ρ g lam) x = smoothDualPairing ρ lam (ρ g⁻¹ x) :=
  rfl

/-- A dependent family on `Fin 2` from its two values. -/
def twoFamily {X : Fin 2 → Type*} (a : X 0) (b : X 1) : ∀ i, X i :=
  fun i => Fin.cases a (fun j => Fin.cases (motive := fun j : Fin 1 => X j.succ) b
    (fun k => k.elim0) j) i

@[simp] theorem twoFamily_zero {X : Fin 2 → Type*} (a : X 0) (b : X 1) :
    twoFamily a b 0 = a := rfl

@[simp] theorem twoFamily_one {X : Fin 2 → Type*} (a : X 0) (b : X 1) :
    twoFamily a b 1 = b := rfl

variable {V : Fin 2 → Type uV} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
  (σ : ∀ i, Representation ℂ (Langlands.GeneralLinear (m i + 1) F.Carrier) (V i))

set_option maxHeartbeats 1600000 in
/-- **Reverse realization.** For smooth admissible blocks, a block test and an actual
bi-smooth block coefficient in each block, there are a full-matrix test, an actual
bi-smooth coefficient of the induced representation and a nonzero constant `κ` such
that, whenever the block integrals converge at `s + m₀/2` and `s + m₁/2`, the induced
zeta integral converges at `s + t/2` and equals `κ` times the product of the two
block zeta integrals. -/
theorem exists_twoBlock_reverse_realization (hσs : ∀ i, IsSmooth (σ i))
    (hσa : ∀ i, IsAdmissible (σ i))
    (Φ₀ : MatrixTestFunction (m 0) F.Carrier) (ℓ₀ : SmoothDual (σ 0)) (v₀ : smoothVectors (σ 0))
    (Φ₁ : MatrixTestFunction (m 1) F.Carrier) (ℓ₁ : SmoothDual (σ 1)) (v₁ : smoothVectors (σ 1)) :
    ∃ (Φ : MatrixTestFunction t F.Carrier)
      (ℓ : SmoothDual (F.canonicalNormalizedProductInduced (succBlockShape m h) σ))
      (v : smoothVectors (F.canonicalNormalizedProductInduced (succBlockShape m h) σ)) (κ : ℂ),
      κ ≠ 0 ∧ ∀ s : ℂ,
        (∀ α : MatrixTestFunction (m 0) F.Carrier,
          Padic.MatrixConverges F α (s + jpssShift (m 0)) (biSmoothCoefficient (σ 0) ℓ₀ v₀)) →
        (∀ α : MatrixTestFunction (m 1) F.Carrier,
          Padic.MatrixConverges F α (s + jpssShift (m 1)) (biSmoothCoefficient (σ 1) ℓ₁ v₁)) →
        Padic.MatrixConverges F Φ (s + jpssShift t)
            (biSmoothCoefficient (F.canonicalNormalizedProductInduced (succBlockShape m h) σ)
              ℓ v) ∧
          Padic.matrixIntegral F Φ (s + jpssShift t)
              (biSmoothCoefficient (F.canonicalNormalizedProductInduced (succBlockShape m h) σ)
                ℓ v) =
            κ * (Padic.matrixIntegral F Φ₀ (s + jpssShift (m 0))
                (biSmoothCoefficient (σ 0) ℓ₀ v₀) *
              Padic.matrixIntegral F Φ₁ (s + jpssShift (m 1))
                (biSmoothCoefficient (σ 1) ℓ₁ v₁)) := by
  classical
  obtain ⟨K, hK, hPK, hμ⟩ := exists_compactProductCoefficientFormula (V := V)
    F.canonicalTopologicalData (succBlockShape m h) (Nat.succ_pos t)
  let : MeasurableSpace K := borel K
  have : BorelSpace K := ⟨rfl⟩
  obtain ⟨μK, hHaar, hprob, hformula⟩ := hμ
  obtain ⟨E, hE⟩ := hformula σ hσa
  have : NonarchimedeanGroup (Langlands.GeneralLinear (t + 1) F.Carrier) :=
    F.canonicalTopologicalData.generalLinearNonarchimedean (t + 1)
  -- the full-matrix test and a compact open subgroup fixing it on both sides
  obtain ⟨K₁, hK₁, hK₁K, hΦinv⟩ := exists_compactOpen_biInvariant F (reverseTest F h Φ₀ Φ₁) K
  -- the pure tensor vector and functional
  let w : PiTensorProduct ℂ V := PiTensorProduct.tprod ℂ (twoFamily (X := V) v₀.val v₁.val)
  let lam : SmoothDual ((succBlockShape m h).blockTensor σ) :=
    FiniteTensor.smoothDualTensorMap σ
      (PiTensorProduct.tprod ℂ (twoFamily (X := fun i => SmoothDual (σ i)) ℓ₀ ℓ₁))
  have hm : Continuous ((succBlockShape m h).leviProjection F.Carrier) :=
    ((succBlockShape m h).leviProjectionContinuous F.Carrier).continuous
  have hker := F.canonicalTopologicalData.isOpen_ker_parabolicHalfModulus (succBlockShape m h)
  obtain ⟨Hw, hHw⟩ := FiniteTensor.isSmooth_external σ hσs w
  obtain ⟨Hw', hHw'⟩ := Induction.exists_twist_comp_fixed ((succBlockShape m h).parabolic F.Carrier)
    ((succBlockShape m h).leviProjection F.Carrier) hm
    (F.canonicalTopologicalData.parabolicHalfModulus (succBlockShape m h)) hker
    ((succBlockShape m h).blockTensor σ) w Hw hHw
  obtain ⟨Hl, hHl⟩ := isSmooth_smoothContragredient ((succBlockShape m h).blockTensor σ) lam
  obtain ⟨Hl', hHl'⟩ := Induction.exists_twist_comp_fixed ((succBlockShape m h).parabolic F.Carrier)
    ((succBlockShape m h).leviProjection F.Carrier) hm
    (F.canonicalTopologicalData.parabolicHalfModulus (succBlockShape m h)) hker
    (smoothContragredient ((succBlockShape m h).blockTensor σ)) lam Hl hHl
  obtain ⟨K₂, hK₂, hK₂K₁, hlfix⟩ := Induction.exists_compact_conj_fixed
    ((succBlockShape m h).parabolic F.Carrier) _ lam Hl' hHl' 1 K₁
  obtain ⟨K₀, hK₀, hK₀K₂, hwfix⟩ := Induction.exists_compact_conj_fixed
    ((succBlockShape m h).parabolic F.Carrier) _ w Hw' hHw' 1 K₂
  have hlfix₀ : lam ∈ fixedVectors (twist (F.canonicalTopologicalData.parabolicHalfModulus
      (succBlockShape m h)) ((smoothContragredient ((succBlockShape m h).blockTensor σ)).comp
        ((succBlockShape m h).leviProjection F.Carrier)))
      (Induction.conjOpenSubgroup ((succBlockShape m h).parabolic F.Carrier) K₀ 1).toSubgroup := by
    rw [fixedVectors, Representation.mem_invariants]
    intro p
    have hp : p.val ∈ Induction.conjOpenSubgroup ((succBlockShape m h).parabolic F.Carrier) K₂ 1 := by
      rw [Induction.mem_conjOpenSubgroup]
      exact hK₀K₂ (Induction.mem_conjOpenSubgroup.mp p.property)
    exact (Representation.mem_invariants _ _).mp hlfix ⟨p.val, hp⟩
  -- the two compact double coset sections
  let fsec := Induction.compactDoubleCosetSection ((succBlockShape m h).parabolic F.Carrier)
    (twist (F.canonicalTopologicalData.parabolicHalfModulus (succBlockShape m h))
      (((succBlockShape m h).blockTensor σ).comp ((succBlockShape m h).leviProjection F.Carrier)))
    K₀ hK₀ 1 w hwfix
  let hsec := Induction.compactDoubleCosetSection ((succBlockShape m h).parabolic F.Carrier)
    (twist (F.canonicalTopologicalData.parabolicHalfModulus (succBlockShape m h))
      ((smoothContragredient ((succBlockShape m h).blockTensor σ)).comp
        ((succBlockShape m h).leviProjection F.Carrier)))
    K₀ hK₀ 1 lam hlfix₀
  let ℓ : SmoothDual (F.canonicalNormalizedProductInduced (succBlockShape m h) σ) := E.symm hsec.val
  have hEℓ : E ℓ = hsec.val := E.toLinearEquiv.apply_symm_apply hsec.val
  let v : smoothVectors (F.canonicalNormalizedProductInduced (succBlockShape m h) σ) :=
    ⟨fsec.val, F.canonicalTopologicalData.isSmooth_normalizedProductInduced (succBlockShape m h) σ
      fsec.val⟩
  -- the kernels
  let Γ : K → Langlands.GeneralLinear (t + 1) F.Carrier → ℂ := fun k y =>
    smoothDualPairing ((succBlockShape m h).blockTensor σ)
      (Induction.eval _ _ hsec.val (k : Langlands.GeneralLinear (t + 1) F.Carrier))
      (Induction.eval _ _ fsec.val y)
  let Γ₀ : Langlands.GeneralLinear (t + 1) F.Carrier → ℂ := fun y =>
    smoothDualPairing ((succBlockShape m h).blockTensor σ) lam (Induction.eval _ _ fsec.val y)
  have hΓ : Continuous fun z : K × Langlands.GeneralLinear (t + 1) F.Carrier => Γ z.1 z.2 := by
    have hl := (Induction.eval_isLocallyConstant _ _ hsec.val).comp_continuous
      (continuous_subtype_val.comp (continuous_fst (X := K)
        (Y := Langlands.GeneralLinear (t + 1) F.Carrier)))
    have hv := (Induction.eval_isLocallyConstant _ _ fsec.val).comp_continuous
      (continuous_snd (X := K) (Y := Langlands.GeneralLinear (t + 1) F.Carrier))
    exact (hl.comp₂ hv fun a b =>
      smoothDualPairing ((succBlockShape m h).blockTensor σ) a b).continuous
  have hΓ₀c : Continuous Γ₀ :=
    ((Induction.eval_isLocallyConstant _ _ fsec.val).comp fun x =>
      smoothDualPairing ((succBlockShape m h).blockTensor σ) lam x).continuous
  have hsupp : ∀ k : K, (k : Langlands.GeneralLinear (t + 1) F.Carrier) ∉
      parabolicCompactSet F h K₀ → ∀ y, Γ k y = 0 := by
    intro k hk y
    have h0 : Induction.eval _ _ hsec.val (k : Langlands.GeneralLinear (t + 1) F.Carrier) = 0 := by
      by_contra hne
      obtain ⟨q, l, hql⟩ := Induction.compactDoubleCosetSection_mem_of_ne_zero _ _ K₀ hK₀ 1 lam
        hlfix₀ _ hne
      exact hk ⟨q, l, by rw [hql, mul_one]⟩
    simp only [Γ, h0, map_zero, LinearMap.zero_apply]
  have hΓ₀supp : ∀ y, y ∉ parabolicCompactSet F h K₀ → Γ₀ y = 0 := by
    intro y hy
    have h0 : Induction.eval _ _ fsec.val y = 0 := by
      by_contra hne
      obtain ⟨q, l, hql⟩ := Induction.compactDoubleCosetSection_mem_of_ne_zero _ _ K₀ hK₀ 1 w
        hwfix _ hne
      exact hy ⟨q, l, by rw [hql, mul_one]⟩
    simp only [Γ₀, h0, map_zero]
  -- translation in the compact variable
  have hK₀K : K₀ ≤ K := fun x hx => hK₁K (hK₂K₁ (hK₀K₂ hx))
  have htrans : ∀ (k : K) (q : (succBlockShape m h).parabolic F.Carrier) (l : K₀),
      (k : Langlands.GeneralLinear (t + 1) F.Carrier) =
        (q : Langlands.GeneralLinear (t + 1) F.Carrier) *
          (l : Langlands.GeneralLinear (t + 1) F.Carrier) →
      ∀ y, Γ k y = Γ₀ ((q : Langlands.GeneralLinear (t + 1) F.Carrier)⁻¹ * y) := by
    intro k q l hkql y
    have hqK : (q : Langlands.GeneralLinear (t + 1) F.Carrier) ∈ K.toSubgroup := by
      have hq : (q : Langlands.GeneralLinear (t + 1) F.Carrier) =
          (k : Langlands.GeneralLinear (t + 1) F.Carrier) *
            (l : Langlands.GeneralLinear (t + 1) F.Carrier)⁻¹ := by
        rw [hkql, mul_inv_cancel_right]
      rw [hq]
      exact K.toSubgroup.mul_mem k.property (K.toSubgroup.inv_mem (hK₀K l.property))
    have hδ : F.canonicalTopologicalData.leviModulus (succBlockShape m h)
        ((succBlockShape m h).leviProjection F.Carrier q) = 1 :=
      leviModulus_eq_one_of_mem F h K.toSubgroup hK q hqK
    have hδ' : F.canonicalTopologicalData.leviModulus (succBlockShape m h)
        ((succBlockShape m h).leviProjection F.Carrier q⁻¹) = 1 := by
      rw [map_inv, map_inv, hδ, inv_one]
    have hhalf : F.canonicalTopologicalData.parabolicHalfModulus (succBlockShape m h) q = 1 :=
      (F.canonicalTopologicalData.leviHalfModulus_eq_one _ _).mpr hδ
    have hh : Induction.eval _ _ hsec.val (k : Langlands.GeneralLinear (t + 1) F.Carrier) =
        smoothContragredient ((succBlockShape m h).blockTensor σ)
          ((succBlockShape m h).leviProjection F.Carrier q) lam := by
      have happ := Induction.compactDoubleCosetSection_apply _ _ K₀ hK₀ 1 lam hlfix₀ q l
      rw [mul_one, ← hkql] at happ
      rw [happ]
      change (((F.canonicalTopologicalData.parabolicHalfModulus (succBlockShape m h) q : ℂ) •
        ((smoothContragredient ((succBlockShape m h).blockTensor σ)).comp
          ((succBlockShape m h).leviProjection F.Carrier)) q) lam) = _
      rw [hhalf, Units.val_one, one_smul]
      rfl
    have hcov := F.canonicalTopologicalData.normalizedProductInduced_covariant
      (succBlockShape m h) σ fsec.val q⁻¹ y
    have hcov' : Induction.eval _ _ fsec.val ((q : Langlands.GeneralLinear (t + 1) F.Carrier)⁻¹ * y) =
        (succBlockShape m h).blockTensor σ ((succBlockShape m h).leviProjection F.Carrier q)⁻¹
          (Induction.eval _ _ fsec.val y) := by
      refine (congrArg (Induction.eval _ _ fsec.val) (congrArg (· * y) (Subgroup.coe_inv _ q).symm)).trans
        (hcov.trans ?_)
      rw [hδ', Units.val_one, NNReal.sqrt_one, NNReal.coe_one, Complex.ofReal_one, one_smul,
        map_inv]
    show smoothDualPairing ((succBlockShape m h).blockTensor σ)
        (Induction.eval _ _ hsec.val (k : Langlands.GeneralLinear (t + 1) F.Carrier))
        (Induction.eval _ _ fsec.val y) =
      smoothDualPairing ((succBlockShape m h).blockTensor σ) lam
        (Induction.eval _ _ fsec.val ((q : Langlands.GeneralLinear (t + 1) F.Carrier)⁻¹ * y))
    rw [hh, smoothDualPairing_smoothContragredient, hcov']
  -- the values of `Γ₀` on `P K₀`
  have hΓ₀ : ∀ (L : (succBlockShape m h).Levi F.Carrier)
      (x : Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F.Carrier) (l : K₀),
      Γ₀ (parabolicPoint h (L, x) * l) =
        halfModulus F h L * (biSmoothCoefficient (σ 0) ℓ₀ v₀ (L 0) *
          biSmoothCoefficient (σ 1) ℓ₁ v₁ (L 1)) := by
    intro L x l
    have hcov := F.canonicalTopologicalData.normalizedProductInduced_covariant
      (succBlockShape m h) σ fsec.val ⟨parabolicPoint h (L, x), parabolicPoint_mem h _⟩ l
    have hLP : (succBlockShape m h).leviProjection F.Carrier
        ⟨parabolicPoint h (L, x), parabolicPoint_mem h _⟩ = L :=
      congrArg Prod.fst (parabolicCoord_parabolicPoint h (L, x))
    have hfl : Induction.eval _ _ fsec.val (l : Langlands.GeneralLinear (t + 1) F.Carrier) = w := by
      have happ := Induction.compactDoubleCosetSection_apply_mul _ _ K₀ hK₀ 1 w hwfix l
      rwa [one_mul] at happ
    have hcoef := FiniteTensor.matrixCoefficient_smoothDualTensorMap_tprod σ
      (twoFamily (X := fun i => SmoothDual (σ i)) ℓ₀ ℓ₁) (twoFamily (X := V) v₀.val v₁.val) L
    rw [Fin.prod_univ_two] at hcoef
    show smoothDualPairing ((succBlockShape m h).blockTensor σ) lam
        (Induction.eval _ _ fsec.val (parabolicPoint h (L, x) * l)) = _
    rw [hcov, hLP, hfl, map_smul, smul_eq_mul]
    exact congrArg _ hcoef
  have hΦ : ∀ (l l' : K₀) (X : Matrix (Fin (t + 1)) (Fin (t + 1)) F.Carrier),
      reverseTest F h Φ₀ Φ₁ ((l : Langlands.GeneralLinear (t + 1) F.Carrier).val * X *
        (l' : Langlands.GeneralLinear (t + 1) F.Carrier).val) = reverseTest F h Φ₀ Φ₁ X :=
    fun l l' X => hΦinv ⟨l, hK₂K₁ (hK₀K₂ l.property)⟩ ⟨l', hK₂K₁ (hK₀K₂ l'.property)⟩ X
  have hc₀ : Continuous (biSmoothCoefficient (σ 0) ℓ₀ v₀) :=
    (matrixCoefficient_isLocallyConstant (σ 0) _ _ v₀.property).continuous
  have hc₁ : Continuous (biSmoothCoefficient (σ 1) ℓ₁ v₁) :=
    (matrixCoefficient_isLocallyConstant (σ 1) _ _ v₁.property).continuous
  -- the coefficient of the induced representation
  have hcoefπ : biSmoothCoefficient (F.canonicalNormalizedProductInduced (succBlockShape m h) σ)
      ℓ v = fun g => ∫ k, Γ k ((k : Langlands.GeneralLinear (t + 1) F.Carrier) * g) ∂μK := by
    funext g
    have hform := (hE ℓ fsec.val g).2
    rw [hEℓ] at hform
    exact hform
  -- the constant
  have hHaar' := hHaar
  have hSpos : (μK {k : K | (k : Langlands.GeneralLinear (t + 1) F.Carrier) ∈
      parabolicCompactSet F h K₀}).toReal ≠ 0 := by
    have hSo : IsOpen {k : K | (k : Langlands.GeneralLinear (t + 1) F.Carrier) ∈
        parabolicCompactSet F h K₀} :=
      (isOpen_parabolicCompactSet F h K₀).preimage continuous_subtype_val
    have h1S : (1 : K) ∈ {k : K | (k : Langlands.GeneralLinear (t + 1) F.Carrier) ∈
        parabolicCompactSet F h K₀} := ⟨1, 1, by simp⟩
    exact ENNReal.toReal_ne_zero.mpr ⟨hSo.measure_ne_zero μK ⟨1, h1S⟩, measure_ne_top μK _⟩
  have hρpos : (parabolicMeasure F h Measure.addHaar (parabolicPoint h ⁻¹'
      (K₀ : Set (Langlands.GeneralLinear (t + 1) F.Carrier)))).toReal ≠ 0 :=
    ENNReal.toReal_ne_zero.mpr ⟨parabolicMeasure_preimage_ne_zero F h _ K₀,
      parabolicMeasure_preimage_ne_top F h _ K₀.toSubgroup hK₀⟩
  have hμpos : (generalLinearHaar F.Carrier t
      (K₀ : Set (Langlands.GeneralLinear (t + 1) F.Carrier))).toReal ≠ 0 :=
    ENNReal.toReal_ne_zero.mpr ⟨K₀.isOpen.measure_ne_zero _ ⟨1, K₀.one_mem⟩,
      hK₀.measure_lt_top.ne⟩
  have hbox : ((Measure.addHaar : Measure (Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F.Carrier))
      (integralBox F (m 0 + 1) (m 1 + 1))).toReal ≠ 0 :=
    ENNReal.toReal_ne_zero.mpr ⟨(isOpen_integralBox F _ _).measure_ne_zero _
      ⟨0, zero_mem_integralBox F _ _⟩, (isCompact_integralBox F _ _).measure_lt_top.ne⟩
  refine ⟨reverseTest F h Φ₀ Φ₁, ℓ, v,
    (((μK {k : K | (k : Langlands.GeneralLinear (t + 1) F.Carrier) ∈
        parabolicCompactSet F h K₀}).toReal *
      ((parabolicMeasure F h Measure.addHaar (parabolicPoint h ⁻¹'
        (K₀ : Set (Langlands.GeneralLinear (t + 1) F.Carrier)))).toReal)⁻¹ *
      (generalLinearHaar F.Carrier t
        (K₀ : Set (Langlands.GeneralLinear (t + 1) F.Carrier))).toReal : ℝ) : ℂ) *
      (((Measure.addHaar : Measure (Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F.Carrier))
        (integralBox F (m 0 + 1) (m 1 + 1))).toReal : ℂ), ?_, ?_⟩
  · refine mul_ne_zero (Complex.ofReal_ne_zero.mpr ?_) (Complex.ofReal_ne_zero.mpr hbox)
    exact mul_ne_zero (mul_ne_zero hSpos (inv_ne_zero hρpos)) hμpos
  · intro s h₀ h₁
    obtain ⟨hconv, hval⟩ := reverse_zeta_of_kernel F h K K₀ hK₀ μK Γ hΓ Γ₀ hΓ₀c hsupp htrans
      hΓ₀supp _ _ hc₀ hc₁ hΓ₀ (reverseTest F h Φ₀ Φ₁) hΦ s h₀ h₁
    rw [hcoefπ]
    refine ⟨hconv, ?_⟩
    rw [hval]
    have hfun : (fun L : (succBlockShape m h).Levi F.Carrier =>
        upperBlockIntegral h (reverseTest F h Φ₀ Φ₁) Measure.addHaar ((L 0).val, (L 1).val) *
          (leviCoefficientWeight F h (biSmoothCoefficient (σ 0) ℓ₀ v₀)
            (biSmoothCoefficient (σ 1) ℓ₁ v₁) s L * radicalWeight F h L)) =
        fun L => (((Measure.addHaar : Measure (Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F.Carrier))
          (integralBox F (m 0 + 1) (m 1 + 1))).toReal : ℂ) *
          (Φ₀ (L 0).val * Φ₁ (L 1).val *
            (leviCoefficientWeight F h (biSmoothCoefficient (σ 0) ℓ₀ v₀)
              (biSmoothCoefficient (σ 1) ℓ₁ v₁) s L * radicalWeight F h L)) := by
      funext L
      rw [upperBlockIntegral_reverseTest]
      ring
    have hZ := integral_leviCoefficientWeight F h (biSmoothCoefficient (σ 0) ℓ₀ v₀)
      (biSmoothCoefficient (σ 1) ℓ₁ v₁) s (R := 1) (fun _ => Φ₀) (fun _ => Φ₁) h₀ h₁
      (fun L => Φ₀ (L 0).val * Φ₁ (L 1).val) (fun L => by simp)
    rw [hfun, integral_const_mul, hZ, Fin.sum_univ_one]
    ring

/-- **Reverse generator input.** If both blocks satisfy the matrix analytic
assertions, then the product of actual rational values of individual block zeta
integrals lies in the Laurent span of the induced representation's values. This is
the third component of `TwoBlockMatrixGeneratorInputs`. -/
theorem twoBlock_reverse_generatorInput (hσs : ∀ i, IsSmooth (σ i))
    (hσa : ∀ i, IsAdmissible (σ i)) (P : Fin 2 → Polynomial ℂ)
    (hblock : ∀ i, Padic.MatrixAnalyticAssertions F (σ i) (P i)) :
    ∀ (Φ₀ : MatrixTestFunction (m 0) F.Carrier) (ℓ₀ : SmoothDual (σ 0))
      (v₀ : smoothVectors (σ 0)) (Φ₁ : MatrixTestFunction (m 1) F.Carrier)
      (ℓ₁ : SmoothDual (σ 1)) (v₁ : smoothVectors (σ 1)) (R S : RationalFunctions),
      HasShiftedRationalValue F.canonicalTopologicalData.residueCardinality
        (normalizedAbsoluteValue F.canonicalTopologicalData) (generalLinearHaar F.Carrier (m 0))
        Φ₀ (biSmoothCoefficient (σ 0) ℓ₀ v₀) R →
      HasShiftedRationalValue F.canonicalTopologicalData.residueCardinality
        (normalizedAbsoluteValue F.canonicalTopologicalData) (generalLinearHaar F.Carrier (m 1))
        Φ₁ (biSmoothCoefficient (σ 1) ℓ₁ v₁) S →
      R * S ∈ zetaSpan (GodementJacquet.matrixRationalValues
        F.canonicalTopologicalData.residueCardinality
        (normalizedAbsoluteValue F.canonicalTopologicalData) (generalLinearHaar F.Carrier t)
        (F.canonicalNormalizedProductInduced (succBlockShape m h) σ)) := by
  intro Φ₀ ℓ₀ v₀ Φ₁ ℓ₁ v₁ R S hR hS
  obtain ⟨a₀, ha₀⟩ := (hblock 0).1
  obtain ⟨a₁, ha₁⟩ := (hblock 1).1
  obtain ⟨Φ, ℓ, v, κ, hκ, hD⟩ := exists_twoBlock_reverse_realization F h σ hσs hσa Φ₀ ℓ₀ v₀ Φ₁ ℓ₁ v₁
  have hmem₀ : biSmoothCoefficient (σ 0) ℓ₀ v₀ ∈ biSmoothMatrixCoefficients (σ 0) :=
    Submodule.subset_span ⟨ℓ₀, v₀, rfl⟩
  have hmem₁ : biSmoothCoefficient (σ 1) ℓ₁ v₁ ∈ biSmoothMatrixCoefficients (σ 1) :=
    Submodule.subset_span ⟨ℓ₁, v₁, rfl⟩
  have hconv (s : ℂ) (hs : max a₀ a₁ < s.re) :=
    hD s (fun α => ha₀ α ⟨_, hmem₀⟩ s ((le_max_left a₀ a₁).trans_lt hs))
      (fun α => ha₁ α ⟨_, hmem₁⟩ s ((le_max_right a₀ a₁).trans_lt hs))
  have hHS : HasShiftedRationalValue F.canonicalTopologicalData.residueCardinality
      (normalizedAbsoluteValue F.canonicalTopologicalData) (generalLinearHaar F.Carrier t) Φ
      (biSmoothCoefficient (F.canonicalNormalizedProductInduced (succBlockShape m h) σ) ℓ v)
      (RatFunc.C κ * (R * S)) :=
    ⟨⟨max a₀ a₁, fun s hs => (hconv s hs).1⟩,
      RationalContinuationLinear.continuation_of_eq_on_right
        (hasRationalContinuation_const_mul κ (HasRationalContinuation.mul hR.2 hS.2))
        ⟨max a₀ a₁, fun s hs => (hconv s hs).2⟩⟩
  have hπmem : RatFunc.C κ * (R * S) ∈ zetaSpan (GodementJacquet.matrixRationalValues
      F.canonicalTopologicalData.residueCardinality
      (normalizedAbsoluteValue F.canonicalTopologicalData) (generalLinearHaar F.Carrier t)
      (F.canonicalNormalizedProductInduced (succBlockShape m h) σ)) :=
    Submodule.subset_span ⟨Φ, ⟨_, Submodule.subset_span ⟨ℓ, v, rfl⟩⟩, hHS⟩
  have hsm := Submodule.smul_mem _ (LaurentPolynomial.C κ⁻¹) hπmem
  rw [Algebra.smul_def, algebraMap_laurent, laurentToRatFunc_C, ← mul_assoc, ← map_mul,
    inv_mul_cancel₀ hκ, map_one, one_mul] at hsm
  exact hsm

/-- **Two-block generator inputs.** All three components of
`TwoBlockMatrixGeneratorInputs` for the canonical normalized induced representation of
two smooth admissible blocks satisfying the matrix analytic assertions. -/
theorem twoBlock_matrixGeneratorInputs (hσs : ∀ i, IsSmooth (σ i))
    (hσa : ∀ i, IsAdmissible (σ i)) (P : Fin 2 → Polynomial ℂ)
    (hblock : ∀ i, Padic.MatrixAnalyticAssertions F (σ i) (P i)) :
    TwoBlockMatrixGeneratorInputs F.canonicalTopologicalData.residueCardinality
      (normalizedAbsoluteValue F.canonicalTopologicalData) (generalLinearHaar F.Carrier t)
      (F.canonicalNormalizedProductInduced (succBlockShape m h) σ) m
      (fun i => generalLinearHaar F.Carrier (m i)) σ :=
  ⟨(twoBlock_forward_generatorInputs F h σ hσs hσa P hblock).1,
    (twoBlock_forward_generatorInputs F h σ hσs hσa P hblock).2,
    twoBlock_reverse_generatorInput F h σ hσs hσa P hblock⟩

end Realization

end Langlands.GodementJacquet.TwoBlock
