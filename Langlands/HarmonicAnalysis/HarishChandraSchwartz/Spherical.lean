import Mathlib.Analysis.Real.Sqrt
import Mathlib.MeasureTheory.Group.ModularCharacter
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.LocallyConstant.Basic

/-! # The spherical function `Ξ` from an Iwasawa-type factorization

Waldspurger 2003, II.1: `Ξ(g) = ∫_K δ₀(m₀(kg))^{1/2} dk`, where `G = P₀ K`, `δ₀` is the
modulus character of the minimal parabolic subgroup `P₀`, and `K` has Haar measure of
total mass one. This module constructs `Ξ` from arbitrary data of the same shape: a
subgroup `P`, a compact subgroup `K` with `G = P K`, and a positive character `δ` of `P`
trivial on `P ∩ K`.
-/

noncomputable section

open MeasureTheory Measure TopologicalSpace
open scoped NNReal ENNReal

namespace Langlands.HarishChandraSchwartz

universe u

section CompactHaar

variable (H : Type u) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [CompactSpace H]
  [MeasurableSpace H] [BorelSpace H]

/-- The Haar measure of total mass one on a compact group. -/
def normalizedHaar : Measure H :=
  haarMeasure ⊤

instance : IsHaarMeasure (normalizedHaar H) :=
  isHaarMeasure_haarMeasure _

instance : IsProbabilityMeasure (normalizedHaar H) := by
  refine ⟨?_⟩
  have h := haarMeasure_self (K₀ := (⊤ : TopologicalSpace.PositiveCompacts H))
  rwa [TopologicalSpace.PositiveCompacts.coe_top] at h

/-- On a compact group the normalized Haar measure is also right invariant. -/
instance : (normalizedHaar H).IsMulRightInvariant := by
  refine ⟨fun g => ?_⟩
  have h := map_right_mul_eq_modularCharacterFun_smul (normalizedHaar H) g
  have hΔ : modularCharacterFun g = 1 := by
    have h1 := congrArg (fun μ : Measure H => μ Set.univ) h
    simp only [Measure.smul_apply, measure_univ, ENNReal.smul_def, smul_eq_mul, mul_one] at h1
    exact_mod_cast h1.symm
  rw [h, hΔ, one_smul]

end CompactHaar

section Iwasawa

variable {G : Type u} [Group G]

/-- The factorization `G = P K` (the Iwasawa decomposition `G = P₀ K` of Waldspurger I.1). -/
def IsIwasawaPair (P K : Subgroup G) : Prop :=
  ∀ g : G, ∃ p ∈ P, ∃ k ∈ K, g = p * k

variable {P K : Subgroup G} (hPK : IsIwasawaPair P K) (δ : P →* ℝ≥0ˣ)

/-- The `P`-component of `g` chosen from the factorization `g = p k`. -/
def iwasawaFactor (g : G) : P :=
  ⟨(hPK g).choose, (hPK g).choose_spec.1⟩

theorem exists_iwasawaFactor (g : G) : ∃ k ∈ K, g = (iwasawaFactor hPK g : G) * k :=
  (hPK g).choose_spec.2

/-- The function `g = p k ↦ δ(p)^{1/2}`; for `P = P₀` and `δ = δ₀` this is the function
`g ↦ δ₀(m₀(g))^{1/2}` of Waldspurger II.1. -/
def iwasawaWeight (g : G) : ℝ :=
  NNReal.sqrt (δ (iwasawaFactor hPK g) : ℝ≥0)

variable {hPK δ}

/-- If `δ` is trivial on `P ∩ K`, the weight is independent of the factorization. -/
theorem iwasawaWeight_mul (hδ : ∀ p : P, (p : G) ∈ K → δ p = 1) {p : G} (hp : p ∈ P)
    {k : G} (hk : k ∈ K) : iwasawaWeight hPK δ (p * k) = NNReal.sqrt (δ ⟨p, hp⟩ : ℝ≥0) := by
  obtain ⟨k', hk', hfac⟩ := exists_iwasawaFactor hPK (p * k)
  set q := iwasawaFactor hPK (p * k)
  have hmem : ((q⁻¹ * ⟨p, hp⟩ : P) : G) ∈ K := by
    have h1 : ((q⁻¹ * ⟨p, hp⟩ : P) : G) = k' * k⁻¹ := by
      push_cast
      rw [eq_mul_inv_iff_mul_eq, mul_assoc, hfac, inv_mul_cancel_left]
    rw [h1]
    exact K.mul_mem hk' (K.inv_mem hk)
  have hδq : δ q = δ ⟨p, hp⟩ := by
    have h2 := hδ _ hmem
    rw [map_mul, map_inv, inv_mul_eq_one] at h2
    exact h2
  unfold iwasawaWeight
  rw [hδq]

theorem iwasawaWeight_nonneg (g : G) : 0 ≤ iwasawaWeight hPK δ g :=
  NNReal.coe_nonneg _

theorem iwasawaWeight_pos (g : G) : 0 < iwasawaWeight hPK δ g := by
  unfold iwasawaWeight
  exact_mod_cast NNReal.sqrt_pos.mpr (pos_iff_ne_zero.mpr (Units.ne_zero _))

variable (hδ : ∀ p : P, (p : G) ∈ K → δ p = 1)
include hδ

/-- The weight is right `K`-invariant. -/
theorem iwasawaWeight_mul_right (g : G) {k : G} (hk : k ∈ K) :
    iwasawaWeight hPK δ (g * k) = iwasawaWeight hPK δ g := by
  obtain ⟨k', hk', hfac⟩ := exists_iwasawaFactor hPK g
  generalize iwasawaFactor hPK g = q at hfac
  subst hfac
  rw [mul_assoc, iwasawaWeight_mul (hPK := hPK) hδ q.2 (K.mul_mem hk' hk),
    iwasawaWeight_mul (hPK := hPK) hδ q.2 hk']

/-- The weight is left `P`-equivariant: `φ(p g) = δ(p)^{1/2} φ(g)`. -/
theorem iwasawaWeight_mul_left (p : P) (g : G) :
    iwasawaWeight hPK δ ((p : G) * g) = NNReal.sqrt (δ p : ℝ≥0) * iwasawaWeight hPK δ g := by
  obtain ⟨k', hk', hfac⟩ := exists_iwasawaFactor hPK g
  generalize iwasawaFactor hPK g = q at hfac
  subst hfac
  rw [← mul_assoc, show (p : G) * q = ((p * q : P) : G) from rfl,
    iwasawaWeight_mul (hPK := hPK) hδ (p * q).2 hk', iwasawaWeight_mul (hPK := hPK) hδ q.2 hk']
  simp only [Subtype.coe_eta, map_mul, Units.val_mul, NNReal.sqrt_mul, NNReal.coe_mul]

/-- The weight equals `1` on `K`. -/
theorem iwasawaWeight_of_mem {k : G} (hk : k ∈ K) : iwasawaWeight hPK δ k = 1 := by
  have h := iwasawaWeight_mul (hPK := hPK) hδ P.one_mem hk
  rw [one_mul] at h
  rw [h]
  have h1 : (⟨1, P.one_mem⟩ : P) = 1 := rfl
  rw [h1, map_one, Units.val_one, NNReal.sqrt_one, NNReal.coe_one]

variable [TopologicalSpace G] [IsTopologicalGroup G]

/-- For open `K`, the weight is locally constant. -/
theorem isLocallyConstant_iwasawaWeight (hK : IsOpen (K : Set G)) :
    IsLocallyConstant (iwasawaWeight hPK δ) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have hopen : IsOpen {y : G | x⁻¹ * y ∈ (K : Set G)} :=
    hK.preimage (continuous_const.mul continuous_id)
  have hx : x ∈ {y : G | x⁻¹ * y ∈ (K : Set G)} := by
    simp only [Set.mem_ofPred_eq, inv_mul_cancel]
    exact K.one_mem
  filter_upwards [hopen.mem_nhds hx] with y hy
  have h := iwasawaWeight_mul_right (hPK := hPK) hδ x hy
  rwa [mul_inv_cancel_left] at h

theorem continuous_iwasawaWeight (hK : IsOpen (K : Set G)) :
    Continuous (iwasawaWeight hPK δ) :=
  (isLocallyConstant_iwasawaWeight hδ hK).continuous

end Iwasawa

section Spherical

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G]
variable {P K : Subgroup G} [CompactSpace K]

/-- Waldspurger's spherical function (II.1): `Ξ(g) = ∫_K φ(k g) dk`, with
`φ(p k) = δ(p)^{1/2}` and the Haar measure of `K` of total mass one. -/
def xi (hPK : IsIwasawaPair P K) (δ : P →* ℝ≥0ˣ) (g : G) : ℝ :=
  ∫ k : K, iwasawaWeight hPK δ ((k : G) * g) ∂(normalizedHaar K)

variable {hPK : IsIwasawaPair P K} {δ : P →* ℝ≥0ˣ}
  (hδ : ∀ p : P, (p : G) ∈ K → δ p = 1) (hK : IsOpen (K : Set G))
include hδ hK

omit [MeasurableSpace G] [BorelSpace G] [CompactSpace K] in
theorem continuous_iwasawaWeight_mul (g : G) :
    Continuous fun k : K => iwasawaWeight hPK δ ((k : G) * g) :=
  (continuous_iwasawaWeight hδ hK).comp (continuous_subtype_val.mul continuous_const)

theorem integrable_iwasawaWeight_mul (g : G) :
    Integrable (fun k : K => iwasawaWeight hPK δ ((k : G) * g)) (normalizedHaar K) :=
  (continuous_iwasawaWeight_mul hδ hK g).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

omit hK in
/-- `Ξ(1) = 1`. -/
theorem xi_one : xi hPK δ 1 = 1 := by
  unfold xi
  have h : ∀ k : K, iwasawaWeight hPK δ (k : G) = 1 := fun k => iwasawaWeight_of_mem hδ k.2
  simp only [mul_one, h]
  simp

/-- `Ξ` is positive. -/
theorem xi_pos (g : G) : 0 < xi hPK δ g := by
  unfold xi
  rw [integral_pos_iff_support_of_nonneg (fun k => iwasawaWeight_nonneg _)
    (integrable_iwasawaWeight_mul hδ hK g)]
  have hsupp : Function.support (fun k : K => iwasawaWeight hPK δ ((k : G) * g)) = Set.univ :=
    Set.eq_univ_of_forall fun k => (iwasawaWeight_pos _).ne'
  rw [hsupp, measure_univ]
  exact one_pos

omit hK in
/-- `Ξ` is right `K`-invariant. -/
theorem xi_mul_right (g : G) {k : G} (hk : k ∈ K) : xi hPK δ (g * k) = xi hPK δ g := by
  unfold xi
  congr 1
  funext k'
  rw [← mul_assoc, iwasawaWeight_mul_right hδ _ hk]

omit hδ hK in
/-- `Ξ` is left `K`-invariant (Waldspurger, Lemma II.1.1, first assertion). -/
theorem xi_mul_left {k : G} (hk : k ∈ K) (g : G) : xi hPK δ (k * g) = xi hPK δ g := by
  unfold xi
  have h := integral_mul_right_eq_self (μ := normalizedHaar K)
    (fun k' : K => iwasawaWeight hPK δ ((k' : G) * g)) ⟨k, hk⟩
  simp only [Subgroup.coe_mul, mul_assoc] at h
  exact h

omit hK in
/-- `Ξ` is bi-`K`-invariant. -/
theorem xi_mul_mul {k₁ k₂ : G} (hk₁ : k₁ ∈ K) (hk₂ : k₂ ∈ K) (g : G) :
    xi hPK δ (k₁ * g * k₂) = xi hPK δ g := by
  rw [xi_mul_right hδ _ hk₂, xi_mul_left hk₁]

/-- For open `K`, `Ξ` is locally constant, hence continuous. -/
theorem isLocallyConstant_xi : IsLocallyConstant (xi hPK δ) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have hopen : IsOpen {y : G | x⁻¹ * y ∈ (K : Set G)} :=
    hK.preimage (continuous_const.mul continuous_id)
  have hx : x ∈ {y : G | x⁻¹ * y ∈ (K : Set G)} := by
    simp only [Set.mem_ofPred_eq, inv_mul_cancel]
    exact K.one_mem
  filter_upwards [hopen.mem_nhds hx] with y hy
  have h := xi_mul_right (hPK := hPK) hδ x hy
  rwa [mul_inv_cancel_left] at h

theorem continuous_xi : Continuous (xi hPK δ) :=
  (isLocallyConstant_xi hδ hK).continuous

/-- Waldspurger, Lemma II.1.3: `∫_K Ξ(g₁ k g₂) dk = Ξ(g₁) Ξ(g₂)`. Second countability
makes the Borel σ-algebra of `K × K` the product σ-algebra, for Fubini's theorem. -/
theorem integral_xi_mul_mul [SecondCountableTopology G] (g₁ g₂ : G) :
    ∫ k : K, xi hPK δ (g₁ * k * g₂) ∂(normalizedHaar K) = xi hPK δ g₁ * xi hPK δ g₂ := by
  have : SecondCountableTopology K :=
    TopologicalSpace.Subtype.secondCountableTopology (K : Set G)
  set μ := normalizedHaar K
  set w := iwasawaWeight hPK δ
  have hw := continuous_iwasawaWeight hδ hK (hPK := hPK) (δ := δ)
  -- the double integrand
  set F : K → K → ℝ := fun k k' => w ((k' : G) * (g₁ * k * g₂)) with hF
  have hFc : Continuous (Function.uncurry F) :=
    hw.comp ((continuous_subtype_val.comp continuous_snd).mul
      (((continuous_const.mul (continuous_subtype_val.comp continuous_fst)).mul continuous_const)))
  have hFi : Integrable (Function.uncurry F) (μ.prod μ) :=
    hFc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hswap := integral_integral_swap hFi
  -- the inner integral after swapping
  have hinner : ∀ k' : K, ∫ k : K, F k k' ∂μ = w ((k' : G) * g₁) * xi hPK δ g₂ := by
    intro k'
    obtain ⟨k'', hk'', hfac⟩ := exists_iwasawaFactor hPK ((k' : G) * g₁)
    generalize iwasawaFactor hPK ((k' : G) * g₁) = q at hfac
    have hpt : ∀ k : K, F k k' = NNReal.sqrt (δ q : ℝ≥0) * w ((k'' : G) * ((k : G) * g₂)) := by
      intro k
      simp only [hF]
      have h1 : (k' : G) * (g₁ * k * g₂) = (q : G) * ((k'' : G) * ((k : G) * g₂)) := by
        calc (k' : G) * (g₁ * k * g₂) = ((k' : G) * g₁) * ((k : G) * g₂) := by group
          _ = (q : G) * ((k'' : G) * ((k : G) * g₂)) := by
            rw [hfac]
            simp only [mul_assoc]
      rw [h1]
      exact iwasawaWeight_mul_left hδ q _
    have hinv := integral_mul_left_eq_self (μ := μ)
      (fun k : K => w ((k : G) * g₂)) ⟨k'', hk''⟩
    simp only [Subgroup.coe_mul, mul_assoc] at hinv
    rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_const_mul, hinv]
    have hq : w ((k' : G) * g₁) = NNReal.sqrt (δ q : ℝ≥0) := by
      rw [hfac]
      exact iwasawaWeight_mul hδ q.2 hk''
    rw [hq]
    rfl
  calc ∫ k : K, xi hPK δ (g₁ * k * g₂) ∂μ = ∫ k : K, ∫ k' : K, F k k' ∂μ ∂μ := rfl
    _ = ∫ k' : K, ∫ k : K, F k k' ∂μ ∂μ := hswap
    _ = ∫ k' : K, w ((k' : G) * g₁) * xi hPK δ g₂ ∂μ :=
        integral_congr_ae (Filter.Eventually.of_forall hinner)
    _ = xi hPK δ g₁ * xi hPK δ g₂ := by
        rw [integral_mul_const]
        rfl

end Spherical

end Langlands.HarishChandraSchwartz
