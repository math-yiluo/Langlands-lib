import Langlands.Representation.Conductor.SphericalSeparation
import Langlands.Group.GL.PrincipalLevelDominance

/-!
# Exponential bounds for the masses of the Iwasawa cells

For a right-invariant Borel measure `μ` on `N_(n+1) \ GL_(n+1)(F)`, the mass of the
Iwasawa cell `N \ N ϖ^λ GL_(n+1)(O)` is at most `μ(cell 0) c^(∑ |λ_i|)` for a constant
`c`. The proof covers `ϖ^δ K` by finitely many translates `K ϖ^δ y` for each elementary
exponent `δ = ± e_i` (compactness of `K` and openness of `K ∩ ϖ^(-δ) K ϖ^δ`), and uses
right invariance of `μ`.
-/

noncomputable section

namespace Langlands.Conductor

open MeasureTheory Langlands.GeneralLinear Langlands.RankinSelberg
open Langlands.QuotientIntegration Langlands.GeneralLinear.Iwasawa

universe uF uG

/-! ### Finite covers of a translated compact open subgroup -/

section Cover

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- For a compact open subgroup `K` and any `g`, finitely many `y` satisfy
`g K ⊆ ⋃_y K g y`. -/
theorem exists_finset_translate_cover (K : Subgroup G) (hKo : IsOpen (K : Set G))
    (hKc : IsCompact (K : Set G)) (g : G) :
    ∃ Y : Finset G, ∀ k ∈ K, ∃ y ∈ Y, ∃ k' ∈ K, g * k = k' * g * y := by
  classical
  let U : Set G := {z | z ∈ K ∧ g * z * g⁻¹ ∈ K}
  have hUo : IsOpen U := hKo.inter (hKo.preimage
    ((continuous_const.mul continuous_id).mul continuous_const))
  let W : G → Set G := fun x => (fun z => z * x⁻¹) ⁻¹' U
  have hWo : ∀ x, IsOpen (W x) := fun x =>
    hUo.preimage (continuous_id.mul continuous_const)
  have hcov : (K : Set G) ⊆ ⋃ x, W x := by
    intro k _
    refine Set.mem_iUnion.mpr ⟨k, ?_⟩
    change k * k⁻¹ ∈ K ∧ g * (k * k⁻¹) * g⁻¹ ∈ K
    simp only [mul_inv_cancel, mul_one]
    exact ⟨K.one_mem, K.one_mem⟩
  obtain ⟨Y, hY⟩ := hKc.elim_finite_subcover W hWo hcov
  refine ⟨Y, fun k hk => ?_⟩
  obtain ⟨y, hy, hky⟩ := Set.mem_iUnion₂.mp (hY hk)
  obtain ⟨_, hgk⟩ := hky
  refine ⟨y, hy, g * (k * y⁻¹) * g⁻¹, hgk, ?_⟩
  group

end Cover

/-! ### Masses of cells -/

section Cells

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable [IsNonarchimedeanLocalField F] {n : ℕ} {ϖ : Fˣ}
variable (hϖ : IsUniformizingElement (ValuativeRel.valuation F) ϖ)
variable [MeasurableSpace (LeftUnipotentQuotient n F)] [BorelSpace (LeftUnipotentQuotient n F)]
variable {μ : Measure (LeftUnipotentQuotient n F)}

omit [MeasurableSpace (LeftUnipotentQuotient n F)] [BorelSpace (LeftUnipotentQuotient n F)] in
theorem isOpen_integralSubgroup' :
    IsOpen (integralSubgroup (ValuativeRel.valuation F).integer n :
      Set (Langlands.GeneralLinear (n + 1) F)) :=
  isOpen_integralSubgroup _ n (Valuation.isOpen_integer (v := ValuativeRel.valuation F))

omit [MeasurableSpace (LeftUnipotentQuotient n F)] [BorelSpace (LeftUnipotentQuotient n F)] in
theorem isCompact_integralSubgroup' :
    IsCompact (integralSubgroup (ValuativeRel.valuation F).integer n :
      Set (Langlands.GeneralLinear (n + 1) F)) := by
  have h := isCompact_integralRange F (n + 1)
  rwa [Iwasawa.integralRange_succ] at h

omit [BorelSpace (LeftUnipotentQuotient n F)] in
/-- Right translation preserves the mass of a measurable set. -/
theorem measure_rightTranslate_image
    (hright : ∀ g, MeasurePreserving
      (rightTranslate (upperUnipotent (n + 1) F) g) μ μ)
    (g : Langlands.GeneralLinear (n + 1) F) {S : Set (LeftUnipotentQuotient n F)}
    (hS : MeasurableSet S) :
    μ (rightTranslate (upperUnipotent (n + 1) F) g '' S) = μ S := by
  have he : rightTranslate (upperUnipotent (n + 1) F) g '' S =
      rightTranslate (upperUnipotent (n + 1) F) g⁻¹ ⁻¹' S := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      change rightTranslate _ g⁻¹ (rightTranslate _ g y) ∈ S
      rw [rightTranslate_mul, mul_inv_cancel, rightTranslate_one]
      exact hy
    · intro hx
      refine ⟨_, hx, ?_⟩
      rw [rightTranslate_mul, inv_mul_cancel, rightTranslate_one]
  rw [he]
  exact (hright g⁻¹).measure_preimage hS.nullMeasurableSet

include hϖ in
/-- One elementary step: `μ(cell(λ + δ)) ≤ |Y| μ(cell λ)`. -/
theorem exists_sphericalCell_measure_step
    (hright : ∀ g, MeasurePreserving
      (rightTranslate (upperUnipotent (n + 1) F) g) μ μ)
    (δ : Fin (n + 1) → ℤ) :
    ∃ c : ℕ, ∀ lam : Fin (n + 1) → ℤ,
      μ (sphericalCell hϖ (lam + δ)) ≤ c * μ (sphericalCell hϖ lam) := by
  classical
  obtain ⟨Y, hY⟩ := exists_finset_translate_cover
    (integralSubgroup (ValuativeRel.valuation F).integer n) isOpen_integralSubgroup'
    isCompact_integralSubgroup' (torus ϖ δ)
  refine ⟨Y.card, fun lam => ?_⟩
  have hsub : sphericalCell hϖ (lam + δ) ⊆
      ⋃ y ∈ Y, rightTranslate (upperUnipotent (n + 1) F) (torus ϖ δ * y) ''
        sphericalCell hϖ lam := by
    rw [sphericalCell_eq_image hϖ (lam + δ)]
    rintro _ ⟨k, hk, rfl⟩
    obtain ⟨y, hy, k', hk', heq⟩ := hY k hk
    refine Set.mem_iUnion₂.mpr ⟨y, hy, ?_⟩
    rw [sphericalCell_eq_image hϖ lam]
    refine ⟨Quotient.mk _ (torus ϖ lam * k'), ⟨k', hk', rfl⟩, ?_⟩
    rw [rightTranslate_mk]
    change _ = Quotient.mk _ (torus ϖ (lam + δ) * k)
    rw [torus_add, show torus ϖ lam * torus ϖ δ * k = torus ϖ lam * (torus ϖ δ * k) from
      mul_assoc _ _ _, heq]
    congr 1
    group
  calc
    μ (sphericalCell hϖ (lam + δ)) ≤
        μ (⋃ y ∈ Y, rightTranslate (upperUnipotent (n + 1) F) (torus ϖ δ * y) ''
          sphericalCell hϖ lam) := measure_mono hsub
    _ ≤ ∑ y ∈ Y, μ (rightTranslate (upperUnipotent (n + 1) F) (torus ϖ δ * y) ''
          sphericalCell hϖ lam) := measure_biUnion_finset_le _ _
    _ = ∑ _y ∈ Y, μ (sphericalCell hϖ lam) := by
      apply Finset.sum_congr rfl
      intro y _
      exact measure_rightTranslate_image hright _ (isOpen_sphericalCell hϖ lam).measurableSet
    _ = Y.card * μ (sphericalCell hϖ lam) := by
      rw [Finset.sum_const, nsmul_eq_mul]

include hϖ in
/-- **Cell mass bound.** There is `c ≥ 1` with
`μ(cell λ) ≤ μ(cell 0) c^(∑ |λ_i|)` for every exponent `λ`. -/
theorem exists_sphericalCell_measure_le
    (hright : ∀ g, MeasurePreserving
      (rightTranslate (upperUnipotent (n + 1) F) g) μ μ) :
    ∃ c : ℕ, 1 ≤ c ∧ ∀ lam : Fin (n + 1) → ℤ,
      μ (sphericalCell hϖ lam) ≤
        μ (sphericalCell hϖ 0) * (c : ENNReal) ^ (∑ i, (lam i).natAbs) := by
  classical
  have hstep : ∀ (i : Fin (n + 1)) (ε : Bool), ∃ c : ℕ, ∀ lam : Fin (n + 1) → ℤ,
      μ (sphericalCell hϖ (lam + Pi.single i (if ε then 1 else -1))) ≤
        c * μ (sphericalCell hϖ lam) :=
    fun i ε => exists_sphericalCell_measure_step hϖ hright _
  choose c hc using hstep
  let C : ℕ := 1 + ∑ i, (c i true + c i false)
  have hcC : ∀ i ε, c i ε ≤ C := by
    intro i ε
    have h1 : c i ε ≤ c i true + c i false := by
      cases ε <;> omega
    have h2 : c i true + c i false ≤ ∑ j, (c j true + c j false) :=
      Finset.single_le_sum (f := fun j => c j true + c j false) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ i)
    omega
  refine ⟨C, by omega, ?_⟩
  -- induction on the size `∑ |λ_i|`
  suffices H : ∀ N : ℕ, ∀ lam : Fin (n + 1) → ℤ, ∑ i, (lam i).natAbs = N →
      μ (sphericalCell hϖ lam) ≤ μ (sphericalCell hϖ 0) * (C : ENNReal) ^ N from
    fun lam => H _ lam rfl
  intro N
  induction N with
  | zero =>
    intro lam hlam
    have hz : lam = 0 := by
      funext i
      have := (Finset.sum_eq_zero_iff.mp hlam) i (Finset.mem_univ i)
      simpa using this
    subst hz
    simp
  | succ N ih =>
    intro lam hlam
    have hne : ∃ i, lam i ≠ 0 := by
      by_contra hall
      push Not at hall
      simp [hall] at hlam
    obtain ⟨i, hi⟩ := hne
    let ε : Bool := decide (0 < lam i)
    let d : ℤ := if ε then 1 else -1
    let lam' : Fin (n + 1) → ℤ := lam - Pi.single i d
    have hlam' : lam' + Pi.single i d = lam := by simp [lam']
    have hsize : ∑ j, (lam' j).natAbs = N := by
      have hj : ∀ j, (lam' j).natAbs + (if j = i then 1 else 0) = (lam j).natAbs := by
        intro j
        by_cases hji : j = i
        · subst hji
          simp only [lam', Pi.sub_apply, Pi.single_eq_same, ite_true, d, ε]
          by_cases hp : 0 < lam j
          · simp only [hp, decide_true, ite_true]
            omega
          · simp only [hp, decide_false]
            simp only [Bool.false_eq_true, ite_false]
            omega
        · simp [lam', hji]
      have hsum := Finset.sum_congr rfl (fun j (_ : j ∈ Finset.univ) => hj j)
      rw [Finset.sum_add_distrib, Finset.sum_ite_eq', ite_eq_left (Finset.mem_univ i)] at hsum
      omega
    calc
      μ (sphericalCell hϖ lam) = μ (sphericalCell hϖ (lam' + Pi.single i d)) := by rw [hlam']
      _ ≤ c i ε * μ (sphericalCell hϖ lam') := hc i ε lam'
      _ ≤ C * (μ (sphericalCell hϖ 0) * (C : ENNReal) ^ N) := by
        gcongr
        · exact_mod_cast hcC i ε
        · exact ih lam' hsize
      _ = μ (sphericalCell hϖ 0) * (C : ENNReal) ^ (N + 1) := by
        rw [pow_succ]
        ring

end Cells

end Langlands.Conductor
