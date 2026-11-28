import Langlands.Algebra.HarishChandra.LeviComponentFacts
import Langlands.Algebra.HarishChandra.CenterBorelInjectivityProof

/-! # Independence of the parabolic for the normalized Levi component

This file proves `ParabolicIndependenceStatement`. For a central element `z` of `U(𝔤)` and the
Levi components `y₁, y₂` of `z` for the two parabolics, choose `Y ∈ 𝔥` real-regular for the
Levi `𝔪` and a small `ε > 0`. Then `Xᵢ + εY` is real-regular for `𝔤`, and its positive roots
are those of `𝔳ᵢ` together with the positive roots of `𝔪` at `Y`. Transitivity of the Verma
congruences through `U(𝔪)`, the independence of the Borel subalgebra
(`WeightBasis.sub_mem_vermaIdeal_rho`) and the computation of `ρ` give that the shifted
components `τ₁ y₁` and `τ₂ y₂` have the same scalar modulo every mirror Verma right ideal of
`𝔪` for `Y`. Their difference is central in `U(𝔪)` and lies in the right ideal of the positive
root vectors of `𝔪`, so it vanishes by `centerBorelInjectivity`. -/

noncomputable section

universe v w

set_option autoImplicit false

namespace Langlands.Algebra.HarishChandra

open LieModule Langlands.Algebra.UniversalEnveloping

attribute [local instance 100] LieRing.ofAssociativeRing

/-- A small real perturbation of an integer keeps its sign, and of zero takes the sign of the
perturbation. -/
theorem int_add_mul_pos_iff {k : ℤ} {r ε : ℝ} (hε : 0 < ε) (hr : ε * |r| < 1) :
    (0 < (k : ℝ) + ε * r ↔ 0 < k ∨ (k = 0 ∧ 0 < r)) ∧ ((k : ℝ) + ε * r ≠ 0 ↔ k ≠ 0 ∨ r ≠ 0) := by
  have h1 : |ε * r| < 1 := by rwa [abs_mul, abs_of_pos hε]
  have h2 := abs_lt.mp h1
  rcases lt_trichotomy k 0 with hk | hk | hk
  · have hk' : (k : ℝ) ≤ -1 := by exact_mod_cast Int.le_sub_one_of_lt hk
    refine ⟨⟨fun h => by linarith, fun h => ?_⟩, ⟨fun _ => Or.inl hk.ne, fun _ => by linarith⟩⟩
    rcases h with h | ⟨h, _⟩ <;> omega
  · subst hk
    simp only [Int.cast_zero, zero_add, lt_irrefl, false_or, true_and, ne_eq, not_true_eq_false]
    constructor
    · exact ⟨fun h => pos_of_mul_pos_right h hε.le, fun h => mul_pos hε h⟩
    · exact ⟨fun h hr0 => h (by rw [hr0, mul_zero]), fun h => mul_ne_zero hε.ne' h⟩
  · have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
    refine ⟨⟨fun _ => Or.inl hk, fun _ => by linarith⟩, ⟨fun _ => Or.inl hk.ne', fun _ => by linarith⟩⟩

section Assembly

variable {L : Type v} [LieRing L] [LieAlgebra ℂ L] {H : LieSubalgebra ℂ L} (B : WeightBasis H)

/-- An element of `𝔥` at which the roots of the Levi subalgebra have nonzero real part. -/
theorem WeightBasis.exists_regular_levi (X₁ : H) :
    ∃ Y : H, ∀ a, ⇑(B.w a) ≠ 0 → B.w a X₁ = 0 → (B.w a Y).re ≠ 0 := by
  classical
  obtain ⟨Y, hY⟩ := exists_forall_ne_zero_of_real_linear
    (Finset.univ.filter fun a => ⇑(B.w a) ≠ 0 ∧ B.w a X₁ = 0) (fun a Z => (B.w a Z).re)
    (fun a x y => by simp only [map_add, Complex.add_re])
    (fun a r x => by simp only [map_smul, smul_eq_mul, Complex.re_ofReal_mul])
    (fun a ha => by
      have h0 := (Finset.mem_filter.mp ha).2.1
      obtain ⟨Z, hZ⟩ : ∃ Z, B.w a Z ≠ 0 := by
        by_contra hall
        push Not at hall
        exact h0 (funext hall)
      by_cases hre : (B.w a Z).re = 0
      · refine ⟨Complex.I • Z, ?_⟩
        rw [map_smul, smul_eq_mul, Complex.mul_re, Complex.I_re, Complex.I_im, hre]
        have him : (B.w a Z).im ≠ 0 := fun him => hZ (Complex.ext hre him)
        simpa using him
      · exact ⟨Z, hre⟩)
  exact ⟨Y, fun a h0 h1 => hY a (Finset.mem_filter.mpr ⟨Finset.mem_univ a, h0, h1⟩)⟩

theorem WeightBasis.exists_small (Y : H) : ∃ ε : ℝ, 0 < ε ∧ ∀ a, ε * |(B.w a Y).re| < 1 := by
  refine ⟨1 / (1 + ∑ a, |(B.w a Y).re|), by positivity, fun a => ?_⟩
  have hle : |(B.w a Y).re| ≤ ∑ a, |(B.w a Y).re| :=
    Finset.single_le_sum (f := fun a => |(B.w a Y).re|) (fun a _ => abs_nonneg _)
      (Finset.mem_univ a)
  have hpos : 0 < 1 + ∑ a, |(B.w a Y).re| := by positivity
  rw [div_mul_eq_mul_div, one_mul, div_lt_one hpos]
  linarith

variable {B}

/-- Signs of the roots at `X + εY`. -/
theorem WeightBasis.re_shift (X Y : H) {ε : ℝ} (hε : 0 < ε) (hεY : ∀ a, ε * |(B.w a Y).re| < 1)
    (hint : ∀ a, ∃ k : ℤ, B.w a X = k) (a : Fin B.n) :
    (0 < (B.w a (X + (ε : ℂ) • Y)).re ↔ 0 < (B.w a X).re ∨ (B.w a X = 0 ∧ 0 < (B.w a Y).re)) ∧
      ((B.w a (X + (ε : ℂ) • Y)).re ≠ 0 ↔ B.w a X ≠ 0 ∨ (B.w a Y).re ≠ 0) := by
  obtain ⟨k, hk⟩ := hint a
  rw [B.re_add_smul, hk, Complex.intCast_re]
  have := int_add_mul_pos_iff (k := k) hε (hεY a)
  simp only [Int.cast_pos, Int.cast_eq_zero, ne_eq] at this ⊢
  exact this

variable {M : Type w} [LieRing M] [LieAlgebra ℂ M]

local notation "UL" => UniversalEnvelopingAlgebra ℂ L
local notation "UM" => UniversalEnvelopingAlgebra ℂ M

/-- The correction term `κ₀`: half the sum of the roots of the Levi subalgebra that are positive
at `Y`. -/
def WeightBasis.leviHalfSum (B : WeightBasis H) (X Y : H) : H →ₗ[ℂ] ℂ :=
  (2 : ℂ)⁻¹ • ∑ a ∈ Finset.univ.filter (fun a => B.w a X = 0 ∧ 0 < (B.w a Y).re), B.w a

/-- **One parabolic.** If `y` is the Levi component of the central element `z` for `X` and
`y ≡ s` modulo `R_Y(μ + λ)` in `U(𝔪)`, then `z ≡ s` modulo `R_{X+εY}(μ - κ₀ + ρ_{X+εY})` in
`U(𝔤)`. -/
theorem sub_mem_vermaIdeal_of_levi (hC : IsSplitCartan H) (ι : M →ₗ⁅ℂ⁆ L)
    (hinj : Function.Injective ι) (X : H) (hint : ∀ a, ∃ k : ℤ, B.w a X = k)
    (hrange : LinearMap.range ι.toLinearMap = LinearMap.ker (LieAlgebra.ad ℂ L (X : L)))
    (Y : H) {ε : ℝ} (hε : 0 < ε)
    (hεY : ∀ a, ε * |(B.w a Y).re| < 1) (lam : M →ₗ[ℂ] ℂ)
    (htr : ∀ (Y' : M) (hY' : Set.MapsTo (LieAlgebra.ad ℂ L (ι Y'))
        (positiveEigenSubmodule (X : L)) (positiveEigenSubmodule (X : L))),
      2 * lam Y' = LinearMap.trace ℂ _ ((LieAlgebra.ad ℂ L (ι Y')).restrict hY'))
    {z : UL} {y : UM}
    (hy : z - UniversalEnvelopingAlgebra.lift ℂ ((UniversalEnvelopingAlgebra.ι ℂ).comp ι) y ∈
      generatorRightIdeal (positiveEigenSubmodule (X : L)))
    (μ : H.comap ι →ₗ[ℂ] ℂ) {s : ℂ}
    (hs : y - algebraMap ℂ UM s ∈ vermaIdeal (H.comap ι)
      ((comapCartanEquiv X hinj hC.isLieAbelian hrange).symm Y)
      (μ + lam.comp (H.comap ι).incl.toLinearMap)) :
    z - algebraMap ℂ UL s ∈ vermaIdeal H (X + (ε : ℂ) • Y)
      (μ.comp (comapCartanEquiv X hinj hC.isLieAbelian hrange).symm.toLinearMap -
        B.leviHalfSum X Y + B.rho (X + (ε : ℂ) • Y)) := by
  classical
  have hab := hC.isLieAbelian
  set φ := comapCartanEquiv X hinj hab hrange with hφdef
  set j := UniversalEnvelopingAlgebra.lift ℂ ((UniversalEnvelopingAlgebra.ι ℂ).comp ι) with hj
  set X' := X + (ε : ℂ) • Y with hX'
  have hw : ∀ a (h : H), ⁅(h : L), B.b a⁆ = B.w a h • B.b a := fun a h =>
    (mem_weightSpace _ _).mp (B.mem a) h
  have hsign := fun a => B.re_shift X Y hε hεY hint a
  have hv := positiveEigenSubmodule_eq_span B.b (fun a => ⇑(B.w a)) hw X hint
  set P := Finset.univ.filter fun a => 0 < (B.w a X).re
  have hvP : positiveEigenSubmodule (X : L) = Submodule.span ℂ (B.b '' ↑P) := by
    rw [hv]
    congr 2
    ext a
    simp [P]
  -- the shift `λ` on `𝔥`
  have hlamρ : lam.comp ((H.comap ι).incl.toLinearMap.comp φ.symm.toLinearMap) =
      (2 : ℂ)⁻¹ • ∑ a ∈ P, B.w a := by
    ext h
    have hφh : ι (φ.symm h : M) = (h : L) := by
      rw [← comapCartanEquiv_apply X hinj hab hrange, LinearEquiv.apply_symm_apply]
    have hmaps : Set.MapsTo (LieAlgebra.ad ℂ L (ι (φ.symm h : M)))
        (positiveEigenSubmodule (X : L)) (positiveEigenSubmodule (X : L)) := by
      intro x hx
      rw [LieAlgebra.ad_apply]
      refine lie_mem_positiveEigenSubmodule ?_ hx
      have : ι (φ.symm h : M) ∈ LinearMap.ker (LieAlgebra.ad ℂ L (X : L)) := hrange ▸ ⟨_, rfl⟩
      simpa using this
    have h2 := htr (φ.symm h : M) hmaps
    rw [trace_restrict_span_eigen B.b (fun a => B.w a h) _ (fun a => by
      rw [LieAlgebra.ad_apply, hφh, hw]) P hvP hmaps] at h2
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LieHom.coe_toLinearMap,
      LieSubalgebra.coe_incl, LinearMap.smul_apply, LinearMap.sum_apply, smul_eq_mul]
    linear_combination (2 : ℂ)⁻¹ * h2
  -- the shift `ρ` at `X + εY`
  have hρ : B.rho X' = (2 : ℂ)⁻¹ • ∑ a ∈ P, B.w a + B.leviHalfSum X Y := by
    have hsplit : Finset.univ.filter (fun a => 0 < (B.w a X').re) =
        P ∪ Finset.univ.filter (fun a => B.w a X = 0 ∧ 0 < (B.w a Y).re) := by
      ext a
      simp only [P, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
      exact (hsign a).1
    have hdisj : Disjoint P (Finset.univ.filter fun a => B.w a X = 0 ∧ 0 < (B.w a Y).re) := by
      rw [Finset.disjoint_filter]
      intro a _ hpos h0
      rw [h0.1, Complex.zero_re] at hpos
      exact lt_irrefl 0 hpos
    rw [WeightBasis.rho, hsplit, Finset.sum_union hdisj, smul_add, WeightBasis.leviHalfSum]
  have hν : μ.comp φ.symm.toLinearMap - B.leviHalfSum X Y + B.rho X' =
      (μ + lam.comp (H.comap ι).incl.toLinearMap).comp φ.symm.toLinearMap := by
    rw [hρ, LinearMap.add_comp, LinearMap.comp_assoc, hlamρ]
    abel
  rw [hν]
  set ν := (μ + lam.comp (H.comap ι).incl.toLinearMap).comp φ.symm.toLinearMap
  have hR : ∀ r ∈ vermaIdeal H X' ν, ∀ a : UL, r * a ∈ vermaIdeal H X' ν :=
    fun r hr a => vermaIdeal_mul_mem X' ν hr a
  -- the radical lies in the positive roots at `X + εY`
  have hvpos : positiveEigenSubmodule (X : L) ≤ positiveRootSubmodule H X' := by
    rw [hvP, Submodule.span_le]
    rintro _ ⟨a, ha, rfl⟩
    have ha' : 0 < (B.w a X).re := (Finset.mem_filter.mp ha).2
    exact mem_positiveRootSubmodule ((hsign a).1.mpr (Or.inl ha')) (B.mem a)
  -- the positive roots of the Levi at `Y` are positive at `X + εY`
  have hlevipos : ∀ x ∈ positiveRootSubmodule (H.comap ι) (φ.symm Y),
      ι x ∈ positiveRootSubmodule H X' := by
    intro x hx
    induction hx using Submodule.iSup_induction' with
    | mem χ x hx =>
      induction hx using Submodule.iSup_induction' with
      | mem hχ x hx =>
        by_cases hx0 : x = 0
        · rw [hx0, map_zero]
          exact Submodule.zero_mem _
        have hb : weightSpace M χ ≠ ⊥ := weightSpace_ne_bot_of_mem hx hx0
        have hιx := (mem_weightSpace_iff_symm X hinj hab hrange χ x).mp hx
        obtain ⟨a, ha⟩ := B.exists_index (weightSpace_symm_ne_bot X hinj hab hrange hb)
        have hz := weight_symm_apply_eq_zero X hinj hab hrange hb
        rw [← ha] at hιx hz
        refine mem_positiveRootSubmodule ((hsign a).1.mpr (Or.inr ⟨hz, ?_⟩)) hιx
        have : B.w a Y = χ (φ.symm Y) := by
          rw [show B.w a Y = (⇑(B.w a)) Y from rfl, ha]
          rfl
        rwa [this]
      | zero => rw [map_zero]; exact Submodule.zero_mem _
      | add x x' _ _ h₁ h₂ => rw [map_add]; exact Submodule.add_mem _ h₁ h₂
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add x x' _ _ h₁ h₂ => rw [map_add]; exact Submodule.add_mem _ h₁ h₂
  have hjmem : j (y - algebraMap ℂ UM s) ∈ vermaIdeal H X' ν := by
    refine map_mem_of_mem_vermaIdeal (φ.symm Y) _ j _ hR (fun x hx => ?_) (fun h => ?_) hs
    · rw [hj, UniversalEnvelopingAlgebra.lift_ι_apply, LieHom.comp_apply, ← mul_one
        (UniversalEnvelopingAlgebra.ι ℂ (ι x))]
      exact positive_mul_mem_vermaIdeal X' ν (hlevipos x hx) 1
    · have hφh : ι (h : M) = ((φ h : H) : L) := (comapCartanEquiv_apply X hinj hab hrange h).symm
      have hνh : (μ + lam.comp (H.comap ι).incl.toLinearMap) h = ν (φ h) := by
        simp only [ν, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
      rw [map_sub, hj, UniversalEnvelopingAlgebra.lift_ι_apply, LieHom.comp_apply, AlgHom.commutes,
        hφh, hνh, ← mul_one (UniversalEnvelopingAlgebra.ι ℂ ((φ h : H) : L) -
          algebraMap ℂ UL (ν (φ h)))]
      exact cartan_mul_mem_vermaIdeal X' ν (φ h) 1
  have heq : z - algebraMap ℂ UL s = (z - j y) + j (y - algebraMap ℂ UM s) := by
    rw [map_sub, AlgHom.commutes]
    abel
  rw [heq]
  exact Submodule.add_mem _ (generatorRightIdeal_le_vermaIdeal X' ν hvpos hy) hjmem

end Assembly

/-- **Independence of the parabolic** (Knapp–Vogan, Proposition 4.129 (c), mirrored). -/
theorem parabolicIndependence : ParabolicIndependenceStatement.{v, w} := by
  intro L _ _ _ H hC M _ _ ι X₁ X₂ hint hinj hrange lam₁ lam₂ hlam₁ hlam₂ htr₁ htr₂ z y₁ y₂ hy₁
    hy₂
  classical
  obtain ⟨B⟩ := hC.nonempty_weightBasis
  have hab := hC.isLieAbelian
  have _ : FiniteDimensional ℂ M := FiniteDimensional.of_injective ι.toLinearMap hinj
  have hw : ∀ a (h : H), ⁅(h : L), B.b a⁆ = B.w a h • B.b a := fun a h =>
    (mem_weightSpace _ _).mp (B.mem a) h
  have hintB : ∀ a, (∃ k : ℤ, B.w a X₁ = k) ∧ (∃ k : ℤ, B.w a X₂ = k) ∧
      (B.w a X₁ = 0 ↔ B.w a X₂ = 0) := fun a => hint _ (B.weightSpace_ne_bot a)
  have hker : LinearMap.ker (LieAlgebra.ad ℂ L (X₂ : L)) =
      LinearMap.ker (LieAlgebra.ad ℂ L (X₁ : L)) := by
    ext x
    simp only [LinearMap.mem_ker, LieAlgebra.ad_apply]
    rw [lie_eq_zero_iff B.b (fun a => ⇑(B.w a)) hw X₂ x,
      lie_eq_zero_iff B.b (fun a => ⇑(B.w a)) hw X₁ x]
    exact forall₂_congr fun a _ => (hintB a).2.2.symm
  have hrange₂ : LinearMap.range ι.toLinearMap = LinearMap.ker (LieAlgebra.ad ℂ L (X₂ : L)) :=
    hrange.trans hker.symm
  have hy₁c := mem_center_of_sub_mem_generatorRightIdeal hC ι hinj X₁ (fun χ h => (hint χ h).1)
    hrange z.2 hy₁
  have hy₂c := mem_center_of_sub_mem_generatorRightIdeal hC ι hinj X₂
    (fun χ h => (hint χ h).2.1) hrange₂ z.2 hy₂
  set K := H.comap ι
  have hCK : IsSplitCartan K := hC.comap X₁ hinj hrange
  set φ := comapCartanEquiv X₁ hinj hab hrange with hφ
  have hφ₂ : comapCartanEquiv X₂ hinj hab hrange₂ = φ := rfl
  obtain ⟨Y, hY⟩ := B.exists_regular_levi X₁
  have hY₂ : ∀ a, ⇑(B.w a) ≠ 0 → B.w a X₂ = 0 → (B.w a Y).re ≠ 0 := fun a h0 h1 =>
    hY a h0 ((hintB a).2.2.mpr h1)
  obtain ⟨ε, hε, hεY⟩ := B.exists_small Y
  -- regularity
  have hYK : IsRealRegular K (φ.symm Y) := by
    intro χ hχ0 hχb
    obtain ⟨a, ha⟩ := B.exists_index (weightSpace_symm_ne_bot X₁ hinj hab hrange hχb)
    have hz := weight_symm_apply_eq_zero X₁ hinj hab hrange hχb
    have hne := weight_symm_ne_zero X₁ hinj hab hrange hχ0
    rw [← ha] at hz hne
    have : χ (φ.symm Y) = B.w a Y := by
      rw [show B.w a Y = (⇑(B.w a)) Y from rfl, ha]
      rfl
    rw [this]
    exact hY a hne hz
  have hreg : ∀ (X : H) (hX : ∀ a, ∃ k : ℤ, B.w a X = k)
      (hYX : ∀ a, ⇑(B.w a) ≠ 0 → B.w a X = 0 → (B.w a Y).re ≠ 0),
      IsRealRegular H (X + (ε : ℂ) • Y) := by
    intro X hX hYX
    rw [B.isRealRegular_iff]
    intro a ha
    refine (B.re_shift X Y hε hεY hX a).2.mpr ?_
    by_cases h0 : B.w a X = 0
    · exact Or.inr (hYX a ha h0)
    · exact Or.inl h0
  have hX₁' := hreg X₁ (fun a => (hintB a).1) hY
  have hX₂' := hreg X₂ (fun a => (hintB a).2.1) hY₂
  have hκ : B.leviHalfSum X₂ Y = B.leviHalfSum X₁ Y := by
    simp only [WeightBasis.leviHalfSum]
    congr 2
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [(hintB a).2.2]
  have hcomm : ∀ {y : UniversalEnvelopingAlgebra ℂ M}, y ∈ Subalgebra.center ℂ _ →
      ∀ h : K, commutatorMap (h : M) y = 0 := fun hy h =>
    commutatorMap_eq_zero_of_mem_center hy _
  -- the shifted components agree modulo every Verma right ideal of the Levi
  have hall : ∀ μ : K →ₗ[ℂ] ℂ, scalarShift lam₁ hlam₁ y₁ - scalarShift lam₂ hlam₂ y₂ ∈
      vermaIdeal K (φ.symm Y) μ := by
    intro μ
    obtain ⟨s₁, hs₁⟩ := exists_sub_mem_vermaIdeal hCK hYK y₁ (hcomm hy₁c)
      (μ + lam₁.comp K.incl.toLinearMap)
    obtain ⟨s₂, hs₂⟩ := exists_sub_mem_vermaIdeal hCK hYK y₂ (hcomm hy₂c)
      (μ + lam₂.comp K.incl.toLinearMap)
    have hz₁ := sub_mem_vermaIdeal_of_levi (B := B) hC ι hinj X₁ (fun a => (hintB a).1) hrange Y
      hε hεY lam₁ htr₁ hy₁ μ hs₁
    have hz₂ := sub_mem_vermaIdeal_of_levi (B := B) hC ι hinj X₂ (fun a => (hintB a).2.1)
      hrange₂ Y hε hεY lam₂ htr₂ hy₂ μ (by rw [hφ₂]; exact hs₂)
    rw [hφ₂, hκ] at hz₂
    have hz₁' := B.sub_mem_vermaIdeal_rho hC hX₁' hX₂'
      (μ.comp φ.symm.toLinearMap - B.leviHalfSum X₁ Y) z.2 hz₁
    have hs : s₁ = s₂ := eq_of_sub_mem_vermaIdeal hC hX₂' _ _ hz₁' hz₂
    have ht₁ := scalarShift_mem_vermaIdeal lam₁ hlam₁ (φ.symm Y) μ hs₁
    have ht₂ := scalarShift_mem_vermaIdeal lam₂ hlam₂ (φ.symm Y) μ hs₂
    rw [map_sub, AlgHom.commutes] at ht₁ ht₂
    rw [hs] at ht₁
    have := Submodule.sub_mem _ ht₁ ht₂
    rwa [sub_sub_sub_cancel_right] at this
  have hdc : scalarShift lam₁ hlam₁ y₁ - scalarShift lam₂ hlam₂ y₂ ∈ Subalgebra.center ℂ _ :=
    Subalgebra.sub_mem _ (scalarShift_mem_center lam₁ hlam₁ hy₁c)
      (scalarShift_mem_center lam₂ hlam₂ hy₂c)
  have hdmem := mem_generatorRightIdeal_of_forall_mem_vermaIdeal hCK hYK _
    (fun h => commutatorMap_eq_zero_of_mem_center hdc _) hall
  exact sub_eq_zero.mp (centerBorelInjectivity.{w} M K hCK (φ.symm Y) hYK _ hdc hdmem)

end Langlands.Algebra.HarishChandra
