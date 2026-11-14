import Langlands.GroupScheme.Examples.SU3RootUnitaryIntegralModel
import Langlands.GroupScheme.Examples.SU3RootParametersHenselianValuation
import Langlands.Geometry.Building.UnramifiedQuasiSplitReduction

/-! # The models `X_{r,s}` over the maximal unramified extension

Every separable quadratic extension of a Henselian field with a surjective integer-valued
valuation and algebraically closed residue field is ramified: the invariant extension of the
valuation takes the value `1/2`. Hence the hypotheses of the integral models `X_{r,s}` hold
for the actual maximal unramified field `inertiaFixedField F` of a nonarchimedean local field
`F`, its integer ring `fixedFieldIntegers F`, and any separable quadratic extension `L`.
-/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry

attribute [local instance] CategoryTheory.Hom.group

namespace Langlands.GroupScheme.SU3Root

/-! ### Ramification from residue roots -/

section Ramification

variable {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
  [Algebra.IsQuadraticExtension K L] [Algebra.IsSeparable K L]

local notation "σ" => conjugation K L

variable (K) in
/-- Monic quadratics with integral coefficients have approximate roots in `K`: this is the
form in which an algebraically closed residue field enters. -/
def HasResidueQuadraticRoots (ω : AddValuation L (WithTop ℝ)) : Prop :=
  ∀ t n : K, 0 ≤ ω (algebraMap K L t) → 0 ≤ ω (algebraMap K L n) →
    ∃ b : K, 0 < ω (algebraMap K L (b ^ 2 - t * b + n))

/-- **Ramification.** If `ω` is conjugation invariant, takes integer values on `K^×`, takes the
value `1` on `K`, and monic integral quadratics have approximate roots in `K`, then some
element of `L` has value `1/2`. -/
theorem exists_half_of_hasResidueQuadraticRoots {ω : AddValuation L (WithTop ℝ)}
    (hinv : ∀ z : L, ω (σ z) = ω z)
    (hbase : ∀ a : K, a ≠ 0 → ∃ n : ℤ, ω (algebraMap K L a) = ((n : ℝ) : WithTop ℝ))
    {ϖ : K} (hϖ : ω (algebraMap K L ϖ) = ((1 : ℝ) : WithTop ℝ))
    (hroots : HasResidueQuadraticRoots K ω) :
    ∃ π : L, ω π = ((1 / 2 : ℝ) : WithTop ℝ) := by
  have hϖL : algebraMap K L ϖ ≠ 0 := by
    intro h
    rw [h, ω.map_zero] at hϖ
    exact WithTop.top_ne_coe hϖ
  have hϖ0 : ϖ ≠ 0 := by
    rintro rfl
    exact hϖL (map_zero _)
  -- Values of nonzero elements are half-integers.
  have half : ∀ x : L, x ≠ 0 → ∃ n : ℤ, ω x = (((n : ℝ) / 2 : ℝ) : WithTop ℝ) := by
    intro x hx
    obtain ⟨c, hc⟩ := exists_algebraMap_eq_of_conjugation_eq K L (x := x * σ x)
      (by rw [map_mul, conjugation_involutive K L x, mul_comm])
    have hσx : σ x ≠ 0 := by
      intro h
      exact hx ((map_eq_zero_iff _ (conjugation K L).injective).mp h)
    have hc0 : c ≠ 0 := by
      rintro rfl
      rw [map_zero] at hc
      exact mul_ne_zero hx hσx hc.symm
    obtain ⟨n, hn⟩ := hbase c hc0
    obtain ⟨t, ht⟩ := exists_omega_eq_coe ω hx
    refine ⟨n, ?_⟩
    have h2 : ω (x * σ x) = ((t + t : ℝ) : WithTop ℝ) := by
      rw [ω.map_mul, hinv, ht, WithTop.coe_add]
    rw [← hc, hn, WithTop.coe_eq_coe] at h2
    rw [ht, WithTop.coe_eq_coe]
    linarith
  -- Scaling by powers of `ϖ`.
  have scale : ∀ (x : L) (k : ℤ) (t : ℝ), ω x = (t : WithTop ℝ) →
      ω (algebraMap K L (ϖ ^ k) * x) = (((k : ℝ) + t : ℝ) : WithTop ℝ) := by
    intro x k t ht
    rw [map_zpow₀, ω.map_mul, omega_zpow ω hϖL 1 hϖ k, ht, ← WithTop.coe_add, mul_one]
  -- An element moved by the conjugation, and the distances from it to `K`.
  obtain ⟨θ, hθ⟩ := exists_conjugation_ne K L
  have hne : ∀ c : K, θ - algebraMap K L c ≠ 0 := by
    intro c h
    apply hθ
    rw [sub_eq_zero] at h
    rw [h, AlgEquiv.commutes]
  have hbound : ∀ c : K, ω (θ - algebraMap K L c) ≤ ω (θ - σ θ) := by
    intro c
    have h := AddValuation.map_sub ω (θ - algebraMap K L c) (σ (θ - algebraMap K L c))
    rw [hinv, min_self, map_sub σ θ (algebraMap K L c), AlgEquiv.commutes,
      sub_sub_sub_cancel_right] at h
    exact h
  have hθσ : θ - σ θ ≠ 0 := sub_ne_zero.mpr (Ne.symm hθ)
  obtain ⟨B, hB⟩ := exists_omega_eq_coe ω hθσ
  -- The distance `ω(θ - c)` attains its maximum.
  obtain ⟨m₀, ⟨c₀, hc₀⟩, hmax⟩ := Int.exists_greatest_of_bdd
    (P := fun m : ℤ => ∃ c : K, ω (θ - algebraMap K L c) = (((m : ℝ) / 2 : ℝ) : WithTop ℝ))
    ⟨⌊2 * B⌋, by
      rintro m ⟨c, hc⟩
      have h := hbound c
      rw [hc, hB, WithTop.coe_le_coe] at h
      exact Int.le_floor.mpr (by linarith)⟩
    (by
      obtain ⟨m, hm⟩ := half _ (hne 0)
      exact ⟨m, 0, hm⟩)
  obtain ⟨k, hk | hk⟩ := Int.even_or_odd' m₀
  · -- Even maximum: contradiction with the residue roots.
    exfalso
    set y := algebraMap K L (ϖ ^ (-k)) * (θ - algebraMap K L c₀) with hy_def
    have hy : ω y = ((0 : ℝ) : WithTop ℝ) := by
      rw [hy_def, scale _ _ _ hc₀, WithTop.coe_eq_coe, hk]
      push_cast
      ring
    have hk1 : algebraMap K L (ϖ ^ (-k)) * algebraMap K L (ϖ ^ k) = 1 := by
      rw [← map_mul, ← zpow_add₀ hϖ0, neg_add_cancel, zpow_zero, map_one]
    have hfar : ∀ c : K, ω (y - algebraMap K L c) ≤ 0 := by
      intro c
      have heq : y - algebraMap K L c = algebraMap K L (ϖ ^ (-k)) *
          (θ - algebraMap K L (c₀ + ϖ ^ k * c)) := by
        rw [hy_def, map_add, map_mul]
        linear_combination (algebraMap K L c) * hk1
      obtain ⟨m, hm⟩ := half _ (hne (c₀ + ϖ ^ k * c))
      have hm₀ : m ≤ m₀ := hmax m ⟨_, hm⟩
      rw [heq, scale _ _ _ hm, ← WithTop.coe_zero, WithTop.coe_le_coe]
      have : (m : ℝ) ≤ m₀ := by exact_mod_cast hm₀
      rw [hk] at this
      push_cast at this ⊢
      linarith
    obtain ⟨t, ht⟩ := exists_algebraMap_eq_of_conjugation_eq K L (x := y + σ y)
      (by rw [map_add, conjugation_involutive K L y, add_comm])
    obtain ⟨n, hn⟩ := exists_algebraMap_eq_of_conjugation_eq K L (x := y * σ y)
      (by rw [map_mul, conjugation_involutive K L y, mul_comm])
    have htv : 0 ≤ ω (algebraMap K L t) := by
      rw [ht]
      refine le_trans ?_ (ω.map_add _ _)
      rw [hinv, hy, min_self, WithTop.coe_zero]
    have hnv : 0 ≤ ω (algebraMap K L n) := by
      rw [hn, ω.map_mul, hinv, hy, ← WithTop.coe_add, add_zero, WithTop.coe_zero]
    obtain ⟨b, hb⟩ := hroots t n htv hnv
    have hfac : algebraMap K L (b ^ 2 - t * b + n) =
        (algebraMap K L b - y) * σ (algebraMap K L b - y) := by
      rw [map_add, map_sub, map_mul, map_pow, ht, hn, map_sub, AlgEquiv.commutes]
      ring
    have hby : ω (algebraMap K L b - y) ≤ 0 := by
      rw [← ω.map_neg, neg_sub]
      exact hfar b
    rw [hfac, ω.map_mul, hinv] at hb
    have : ω (algebraMap K L b - y) + ω (algebraMap K L b - y) ≤ 0 := by
      calc ω (algebraMap K L b - y) + ω (algebraMap K L b - y) ≤ 0 + 0 := add_le_add hby hby
        _ = 0 := zero_add 0
    exact absurd hb (not_lt.mpr this)
  · -- Odd maximum: a rescaling has value `1/2`.
    refine ⟨algebraMap K L (ϖ ^ (-k)) * (θ - algebraMap K L c₀), ?_⟩
    rw [scale _ _ _ hc₀, WithTop.coe_eq_coe, hk]
    push_cast
    ring

/-- The hypotheses of `IsRamifiedQuadraticValuation` from residue roots. -/
theorem IsRamifiedQuadraticValuation.of_hasResidueQuadraticRoots {ω : AddValuation L (WithTop ℝ)}
    (hinv : ∀ z : L, ω (σ z) = ω z)
    (hbase : ∀ a : K, a ≠ 0 → ∃ n : ℤ, ω (algebraMap K L a) = ((n : ℝ) : WithTop ℝ))
    {ϖ : K} (hϖ : ω (algebraMap K L ϖ) = ((1 : ℝ) : WithTop ℝ))
    (hroots : HasResidueQuadraticRoots K ω) :
    IsRamifiedQuadraticValuation K L ω :=
  ⟨hinv, hbase, exists_half_of_hasResidueQuadraticRoots hinv hbase hϖ hroots⟩

end Ramification

/-! ### Henselian fields with algebraically closed residue field -/

section Henselian

variable (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
  [Algebra.IsQuadraticExtension K L] [Algebra.IsSeparable K L]
  (v : Valuation K (WithZero (Multiplicative ℤ)))
  (hH : HenselianLocalRing v.valuationSubring)

/-- Integrality for the invariant extension is integrality for `v`. -/
theorem henselianQuadraticValuation_nonneg_iff (a : K) :
    0 ≤ henselianQuadraticValuation K L v hH (algebraMap K L a) ↔ v a ≤ 1 := by
  rcases eq_or_ne a 0 with rfl | ha
  · rw [map_zero, AddValuation.map_zero, map_zero]
    exact iff_of_true le_top zero_le
  · have hv0 : v a ≠ 0 := v.ne_zero_iff.mpr ha
    rw [henselianQuadraticValuation_base K L v hH ha, ← WithTop.coe_zero, WithTop.coe_le_coe,
      Int.cast_nonneg_iff, neg_nonneg, WithZero.log_le_iff_le_exp hv0, WithZero.exp_zero]

/-- Positive value for the invariant extension is `v a < 1`. -/
theorem henselianQuadraticValuation_pos_iff (a : K) :
    0 < henselianQuadraticValuation K L v hH (algebraMap K L a) ↔ v a < 1 := by
  rcases eq_or_ne a 0 with rfl | ha
  · rw [map_zero, AddValuation.map_zero, map_zero]
    exact iff_of_true (WithTop.coe_lt_top (0 : ℝ)) zero_lt_one
  · have hv0 : v a ≠ 0 := v.ne_zero_iff.mpr ha
    rw [henselianQuadraticValuation_base K L v hH ha, ← WithTop.coe_zero, WithTop.coe_lt_coe,
      Int.cast_pos, neg_pos, WithZero.log_lt_iff_lt_exp hv0, WithZero.exp_zero]

/-- An algebraically closed residue field gives residue roots. -/
theorem henselianQuadraticValuation_hasResidueQuadraticRoots
    [IsAlgClosed (IsLocalRing.ResidueField v.valuationSubring)] :
    HasResidueQuadraticRoots K (henselianQuadraticValuation K L v hH) := by
  intro t n ht hn
  rw [henselianQuadraticValuation_nonneg_iff] at ht hn
  let t' : v.valuationSubring := ⟨t, ht⟩
  let n' : v.valuationSubring := ⟨n, hn⟩
  let p : Polynomial (IsLocalRing.ResidueField v.valuationSubring) :=
    Polynomial.C 1 * Polynomial.X ^ 2 +
      Polynomial.C (-IsLocalRing.residue v.valuationSubring t') * Polynomial.X +
        Polynomial.C (IsLocalRing.residue v.valuationSubring n')
  have hp : p.degree ≠ 0 := by
    rw [Polynomial.degree_quadratic one_ne_zero]
    decide
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_root p hp
  obtain ⟨b', rfl⟩ := IsLocalRing.residue_surjective z
  refine ⟨(b' : K), ?_⟩
  have hmem : b' ^ 2 - t' * b' + n' ∈ IsLocalRing.maximalIdeal v.valuationSubring := by
    rw [← IsLocalRing.residue_eq_zero_iff, map_add, map_sub, map_mul, map_pow]
    simp only [p, Polynomial.IsRoot, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X] at hz
    linear_combination hz
  rw [ValuationSubring.valuation_lt_one_iff] at hmem
  rw [henselianQuadraticValuation_pos_iff]
  exact (Valuation.isEquiv_valuation_valuationSubring v).lt_one_iff_lt_one.mpr hmem

/-- **Ramification over a Henselian field with algebraically closed residue field.** -/
theorem henselianQuadraticValuation_isRamified (hv : Function.Surjective v)
    [IsAlgClosed (IsLocalRing.ResidueField v.valuationSubring)] :
    IsRamifiedQuadraticValuation K L (henselianQuadraticValuation K L v hH) := by
  obtain ⟨ϖ, -, hϖ⟩ := exists_henselianQuadraticValuation_base_eq K L v hH hv 1
  rw [Int.cast_one] at hϖ
  exact IsRamifiedQuadraticValuation.of_hasResidueQuadraticRoots
    (henselianQuadraticValuation_conjugation K L v hH)
    (fun a ha => ⟨_, henselianQuadraticValuation_base K L v hH ha⟩) hϖ
    (henselianQuadraticValuation_hasResidueQuadraticRoots K L v hH)

/-- The valuation subring of `v` is the ring of integers of the invariant extension. -/
theorem isValuationIntegers_valuationSubring :
    IsValuationIntegers v.valuationSubring K (henselianQuadraticValuation K L v hH) := by
  intro a
  rw [henselianQuadraticValuation_nonneg_iff, ← Valuation.mem_valuationSubring_iff]
  constructor
  · rintro ⟨b, rfl⟩
    exact b.2
  · intro h
    exact ⟨⟨a, h⟩, rfl⟩

end Henselian

/-! ### The maximal unramified extension of a local field -/

section MaximalUnramified

open Langlands.LocalGalois.Separable Langlands.Geometry.Building

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  (L : Type u) [Field L] [Algebra (inertiaFixedField F) L]
  [Algebra.IsQuadraticExtension (inertiaFixedField F) L]
  [Algebra.IsSeparable (inertiaFixedField F) L]

/-- The invariant extension to `L` of the integer-normalized valuation of the maximal
unramified field. -/
def maximalUnramifiedValuation : AddValuation L (WithTop ℝ) :=
  henselianQuadraticValuation (inertiaFixedField F) L (MaximalUnramified.valuation F)
    (MaximalUnramified.valuationSubring_isHenselian F)

/-- Every separable quadratic extension of the maximal unramified field is ramified, and the
hypotheses of the lattice models hold. -/
theorem maximalUnramifiedValuation_isRamified :
    IsRamifiedQuadraticValuation (inertiaFixedField F) L (maximalUnramifiedValuation F L) :=
  haveI := MaximalUnramified.residueField_isAlgClosed F
  henselianQuadraticValuation_isRamified (inertiaFixedField F) L (MaximalUnramified.valuation F)
    (MaximalUnramified.valuationSubring_isHenselian F) (MaximalUnramified.valuation_surjective F)

/-- `fixedFieldIntegers F` is the ring of integers for `maximalUnramifiedValuation`. -/
theorem maximalUnramifiedValuation_isValuationIntegers :
    IsValuationIntegers (fixedFieldIntegers F) (inertiaFixedField F)
      (maximalUnramifiedValuation F L) := by
  intro a
  have h := isValuationIntegers_valuationSubring (inertiaFixedField F) L
    (MaximalUnramified.valuation F) (MaximalUnramified.valuationSubring_isHenselian F) a
  refine Iff.trans ?_ h
  constructor
  · rintro ⟨b, rfl⟩
    exact ⟨⟨b, (MaximalUnramified.mem_valuationSubring_iff F b).mpr b.2⟩, rfl⟩
  · rintro ⟨b, rfl⟩
    exact ⟨⟨b, (MaximalUnramified.mem_valuationSubring_iff F b).mp b.2⟩, rfl⟩

/-- **The model `X_{r,s}` over `fixedFieldIntegers F`**, for arbitrary real depths. -/
def maximalUnramifiedModel (r s : ℝ) :
    IntegralModel (fixedFieldIntegers F) (inertiaFixedField F)
      (unitaryParameterGroup (inertiaFixedField F) L) :=
  (maximalUnramifiedValuation_isRamified F L).latticeModel
    (maximalUnramifiedValuation_isValuationIntegers F L) r s

theorem maximalUnramifiedModel_isSmooth (r s : ℝ) : (maximalUnramifiedModel F L r s).IsSmooth :=
  (maximalUnramifiedValuation_isRamified F L).latticeModel_isSmooth _ r s

theorem maximalUnramifiedModel_hasGeometricallyConnectedFibres (r s : ℝ) :
    (maximalUnramifiedModel F L r s).HasGeometricallyConnectedFibres :=
  (maximalUnramifiedValuation_isRamified F L).latticeModel_hasGeometricallyConnectedFibres _ r s

/-- The integral points of `X_{r,s}` are `X(K)_r · Z(K)_s`. -/
theorem maximalUnramifiedModel_integralPoints_map (r s : ℝ) :
    (maximalUnramifiedModel F L r s).integralPoints.map
        (unitaryRationalPointsEquiv (inertiaFixedField F) L).toMonoidHom =
      (maximalUnramifiedValuation_isRamified F L).filtrationProduct r s :=
  (maximalUnramifiedValuation_isRamified F L).integralPoints_latticeModel_map _ r s

/-- The transition homomorphisms `X_{r₂,s₂} → X_{r₁,s₁}`. -/
def maximalUnramifiedTransition {r₁ s₁ r₂ s₂ : ℝ} (hr : r₁ ≤ r₂) (hs : s₁ ≤ s₂) :
    (maximalUnramifiedModel F L r₂ s₂).Hom (maximalUnramifiedModel F L r₁ s₁) (𝟙 _) :=
  (maximalUnramifiedValuation_isRamified F L).latticeTransition _ hr hs

end MaximalUnramified

end Langlands.GroupScheme.SU3Root
