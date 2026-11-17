import Langlands.Representation.Archimedean.RealBlockFlatJacquet

/-!
# Two interlaced linked induction blocks: composites and mode expansions

Real Jacquet functionals composed with intertwiners into principal series of characters (flat
and binomial multipliers, the dichotomy at a block), and expansions of functions on matrices
along the block rotations. These are the first tools for the proof of
`RealInterlacedInducedInducedLinkedJacquetFunctionalStatement` in `RealInterlacedMirror`.
-/

noncomputable section

open scoped TensorProduct Matrix Manifold ContDiff Matrix.Norms.Operator

set_option autoImplicit false

namespace Langlands.Archimedean

attribute [local instance 100] LieRing.ofAssociativeRing

set_option backward.isDefEq.respectTransparency false

namespace RealInterlacedJacquet

open Langlands.LocalFactor.Archimedean
open RealJacquetFrobenius RealBlockJacquet RealBlockMultiplier RealBlockRotation
  RealBlockFourierFinite RealBlockDerivative RealCharacterCrossing RealBlockFlatJacquet InductionStages

variable {n : ℕ}

/-! ## Composites with intertwiners -/

section Composite

variable {ds ds' : List RealBlock}

theorem blockFourierCoefficient_rep (p : ℕ) (j : ℤ) (κ : Matrix.unitaryGroup (Fin n) ℝ)
    (w : KF n ds') :
    blockFourierCoefficient n p j (realStandardRep n ds' κ w) 1 =
      blockFourierCoefficient n p j w (Unitary.toUnits κ) := by
  rw [realStandardRep_apply_coe, blockFourierCoefficient_rightTranslation, one_mul]

theorem toUnits_mk {g : Langlands.GeneralLinear n ℝ} (hg : g ∈ unitaryCompact ℝ n) :
    (Unitary.toUnits (⟨(g : Matrix (Fin n) (Fin n) ℝ), hg⟩ : Matrix.unitaryGroup (Fin n) ℝ) :
      Langlands.GeneralLinear n ℝ) = g :=
  Units.ext rfl

/-- **Windows from a vanishing composite.** If `ℓ_μ ∘ B = 0` for an `O(n)`-intertwiner `B`, then
`Φ_j(B v)` vanishes on `O(n)` wherever `μ_j ≠ 0`. -/
theorem blockFourierCoefficient_eq_zero_of_comp {r : ℕ} (hr : r + 1 < n) {μ : ℤ → ℂ}
    {e : Fin n → Fin 2}
    (hsign : ∀ (i : Fin n) (w : KF n ds'),
      blockJacquet n ds' r μ (realStandardRep n ds' (signReflection n i) w) =
        (-1) ^ (e i).val * blockJacquet n ds' r μ w)
    (B : KF n ds →ₗ[ℂ] KF n ds')
    (hrep : ∀ κ v, B (realStandardRep n ds κ v) = realStandardRep n ds' κ (B v))
    (h0 : blockJacquet n ds' r μ ∘ₗ B = 0) {j : ℤ} (hμ : μ j ≠ 0) (v : KF n ds)
    {κ : Langlands.GeneralLinear n ℝ} (hκ : κ ∈ unitaryCompact ℝ n) :
    blockFourierCoefficient n r j (B v) κ = 0 := by
  by_contra hne
  refine blockJacquet_comp_ne_zero hr hsign B hrep hμ
    (realStandardRep n ds ⟨(κ : Matrix (Fin n) (Fin n) ℝ), hκ⟩ v) ?_ h0
  rw [hrep, blockFourierCoefficient_rep, toUnits_mk]
  exact hne

/-- **A linked adjacent pair after an intertwiner**, from the nonvanishing of the composite. -/
theorem exists_of_comp_ne {τ : Fin n → ℂ} {e : Fin n → Fin 2} (B : KF n ds →ₗ[ℂ] KF n (PL τ e))
    (hrep : ∀ κ v, B (realStandardRep n ds κ v) = realStandardRep n (PL τ e) κ (B v))
    (hlie : ∀ Y v, B (realStandardLie n ds Y v) = realStandardLie n (PL τ e) Y (B v))
    {r : ℕ} (hr : r + 1 < n) {k : ℕ} (hk : 0 < k) (hτ : τ (ia hr) - τ (ib hr) = k)
    (hodd : Odd (k + (e (ia hr)).val + (e (ib hr)).val))
    (hne : blockJacquet n (PL τ e) r (binomialMultiplier k ((par hr e : ℕ) : ℤ)) ∘ₗ B ≠ 0) :
    RealLinkedJacquetFunctionalExists n ds := by
  set ε : ℤ := ((par hr e : ℕ) : ℤ) with hεdef
  have hε : ε = 0 ∨ ε = 1 := par_cases hr e
  have hpar : Even ((k : ℤ) - 1 - ε) := by
    rw [hεdef, Int.even_iff]
    unfold par
    obtain ⟨m, hm⟩ := hodd
    omega
  set μ := binomialMultiplier k ε with hμdef
  have hrec : IsRecurrent (τ (ia hr) - τ (ib hr) + 1) (par hr e) μ := by
    rw [hτ]
    exact isRecurrent_binomialMultiplier hk hε hpar
  have hsym : IsSymmetric (par hr e) ((-1) ^ par hr e) μ :=
    isSymmetric_binomialMultiplier k hε
  have hJ := isJacquet_cross hr τ e hrec hsym
  have ha : crossExp hr τ (ia hr) - crossExp hr τ (ib hr) = 1 - (k : ℂ) := by
    rw [crossExp_sub]
    linear_combination -hτ
  have hwin : ∀ (j : ℤ) (f : KF n (PL τ e)), μ j * blockFourierCoefficient n r j f 1 ≠ 0 →
      |j| < k ∧ Even ((k : ℤ) - 1 - j) := by
    intro j f h
    have hj : Even (j - ε) := by
      by_contra hj
      exact h (by rw [blockFourierCoefficient_eq_zero_of_not_even hr (PL_parity hr τ e) f hj 1,
        mul_zero])
    refine ⟨(binomialMultiplier_ne_zero_iff hk hε hpar hj).mp (left_ne_zero_of_mul h), ?_⟩
    rw [Int.even_iff] at hj hpar ⊢
    omega
  have hpow := blockJacquet_pow_eq_zero hr hJ hk ha hwin
  refine ⟨blockJacquet n (PL τ e) r μ ∘ₗ B, crossExp hr τ, e ∘ sw hr, r, k, hr, hne,
    ⟨fun X hX w => ?_, fun j w => ⟨?_, ?_⟩⟩, ha, fun w => ?_⟩
  · simp only [LinearMap.comp_apply, hlie]
    exact hJ.1 X hX (B w)
  · simp only [LinearMap.comp_apply, hlie]
    exact (hJ.2 j (B w)).1
  · simp only [LinearMap.comp_apply, hrep]
    exact (hJ.2 j (B w)).2
  · rw [LinearMap.comp_apply, map_pow_lie B hlie]
    exact hpow (B w)

/-- `finsum_rightDerivative_flat` for one function. -/
theorem finsum_rightDerivative_flat_of {p : ℕ} (hp : p + 1 < n) {τ : Fin n → ℂ} {μ : ℤ → ℂ}
    (hτ : ∀ (i : Fin n) (x : ℝ),
      realPositionCharacter ds i (Units.mk0 (Real.exp x) (Real.exp_pos x).ne') =
        Complex.exp (τ i * x))
    {δ : ℂ} (hδ : (τ (ia hp) + ((n : ℂ) - 1) / 2 - (((ia hp : Fin n) : ℕ) : ℂ)) -
      (τ (ib hp) + ((n : ℂ) - 1) / 2 - (((ib hp : Fin n) : ℕ) : ℂ)) = δ)
    (f : KF n ds)
    (hflat : ∀ j : ℤ, blockFourierCoefficient n p j f 1 ≠ 0 →
      μ (j + 2) * (δ + j) = μ j * (δ + j) ∧ μ (j - 2) * (δ - j) = μ j * (δ - j))
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsUpperTriangular) :
    ∑ᶠ j : ℤ, μ j * blockFourierCoefficient n p j (rightDerivative (matrixModel ℝ n) A f) 1 =
      (∑ i, (τ i + ((n : ℂ) - 1) / 2 - ((i : ℕ) : ℂ)) * (A i i : ℂ)) *
        ∑ᶠ j : ℤ, μ j * blockFourierCoefficient n p j f 1 := by
  have hα := isExpEquivariant_of_mem_principalSeries hτ f.2.1.1
  have hsm := contMDiff_of_mem_realStandardModule f.2.1
  obtain ⟨D, hD⟩ := exists_bound_coe p f
  simp_rw [blockFourierCoefficient_rightDerivative hp hsm hα hA (X := A) 1 (by simp)]
  subst hδ
  exact finsum_flat D (fun j hj => hD j hj 1 (one_mem _)) hflat _ _ _ _

/-- **A flat multiplier after an intertwiner.** If `μ` is flat at the block `p` on the modes of
the functions `B v`, then `ℓ_μ ∘ B` is a real Jacquet functional with the exponents of `ds'`. -/
theorem isRealJacquetFunctional_comp_flat {p : ℕ} (hp : p + 1 < n) {τ : Fin n → ℂ}
    (hτ : ∀ (i : Fin n) (x : ℝ),
      realPositionCharacter ds' i (Units.mk0 (Real.exp x) (Real.exp_pos x).ne') =
        Complex.exp (τ i * x))
    {ε : ℤ}
    (hpar : (-1 : ℂ) ^ ε =
      realPositionCharacter ds' p (-1) * realPositionCharacter ds' (p + 1) (-1))
    {δ : ℂ} (hδ : (τ (ia hp) + ((n : ℂ) - 1) / 2 - (((ia hp : Fin n) : ℕ) : ℂ)) -
      (τ (ib hp) + ((n : ℂ) - 1) / 2 - (((ib hp : Fin n) : ℕ) : ℂ)) = δ)
    {μ : ℤ → ℂ} (B : KF n ds →ₗ[ℂ] KF n ds')
    (hrep : ∀ κ v, B (realStandardRep n ds κ v) = realStandardRep n ds' κ (B v))
    (hlie : ∀ Y v, B (realStandardLie n ds Y v) = realStandardLie n ds' Y (B v))
    (hflat : ∀ (v : KF n ds) (j : ℤ), blockFourierCoefficient n p j (B v) 1 ≠ 0 →
      μ (j + 2) * (δ + j) = μ j * (δ + j) ∧ μ (j - 2) * (δ - j) = μ j * (δ - j))
    {σ : ℂ} (hsym : IsSymmetric ε σ μ) {e : Fin n → Fin 2}
    (he_off : ∀ i : Fin n, i ≠ ia hp → i ≠ ib hp →
      (-1 : ℂ) ^ (e i).val = realPositionCharacter ds' i (-1))
    (he_p : (-1 : ℂ) ^ (e (ia hp)).val = realPositionCharacter ds' p (-1) * σ)
    (he_q : (-1 : ℂ) ^ (e (ib hp)).val = realPositionCharacter ds' (p + 1) (-1) * σ) :
    IsRealJacquetFunctional n (realStandardRep n ds) (realStandardLie n ds)
      (blockJacquet n ds' p μ ∘ₗ B) (fun i => τ i + ((n : ℂ) - 1) / 2 - ((i : ℕ) : ℂ)) e := by
  refine ⟨fun X hX v => ?_, fun i v => ⟨?_, ?_⟩⟩
  · have hU : X.IsUpperTriangular := fun i k hik => hX i k (le_of_lt hik)
    have hdiag : ∀ i, X i i = 0 := fun i => hX i i le_rfl
    rw [LinearMap.comp_apply, hlie, blockJacquet_apply, realStandardLie_one_tmul_apply_coe,
      finsum_rightDerivative_flat_of hp hτ hδ (B v) (hflat v) hU]
    simp [hdiag]
  · have hU : (Matrix.single i i (1 : ℝ)).IsUpperTriangular := fun k l hkl => by
      refine Matrix.single_apply_of_ne _ _ _ _ _ ?_
      rintro ⟨rfl, rfl⟩
      exact lt_irrefl _ hkl
    rw [LinearMap.comp_apply, LinearMap.comp_apply, hlie, blockJacquet_apply, blockJacquet_apply,
      realStandardLie_one_tmul_apply_coe,
      finsum_rightDerivative_flat_of hp hτ hδ (B v) (hflat v) hU]
    have hsum : ∑ k, (τ k + ((n : ℂ) - 1) / 2 - ((k : ℕ) : ℂ)) *
        ((Matrix.single i i (1 : ℝ) k k : ℝ) : ℂ) = τ i + ((n : ℂ) - 1) / 2 - ((i : ℕ) : ℂ) := by
      rw [Finset.sum_eq_single i]
      · simp
      · intro k _ hk
        rw [Matrix.single_apply_of_ne _ _ _ _ _ (fun h => hk h.1.symm)]
        simp
      · simp
    rw [hsum]
    ring
  · rw [LinearMap.comp_apply, LinearMap.comp_apply, hrep]
    exact blockJacquet_hsign hp hpar hsym he_off he_p he_q i (B v)

/-- On `O(n)` the Frobenius function of `ℓ_μ ∘ B` is `g ↦ (2π)⁻¹ Σᶠ_i μ_i Φ_i(B v)(g)`. -/
theorem frobFun_comp_apply_of_mem {p : ℕ} {μ : ℤ → ℂ} {a : Fin n → ℂ} {e : Fin n → Fin 2}
    (B : KF n ds →ₗ[ℂ] KF n ds')
    (hrep : ∀ κ v, B (realStandardRep n ds κ v) = realStandardRep n ds' κ (B v))
    (hsign : ∀ (i : Fin n) (v : KF n ds),
      (blockJacquet n ds' p μ ∘ₗ B) (realStandardRep n ds (signReflection n i) v) =
        (-1) ^ (e i).val * (blockJacquet n ds' p μ ∘ₗ B) v)
    (v : KF n ds) {g : Langlands.GeneralLinear n ℝ} (hg : g ∈ unitaryCompact ℝ n) :
    RealJacquetFrobenius.frobFun (realStandardRep n ds) (blockJacquet n ds' p μ ∘ₗ B) a e v g =
      (2 * (Real.pi : ℂ))⁻¹ * ∑ᶠ i : ℤ, μ i * blockFourierCoefficient n p i (B v) g := by
  rw [RealJacquetFrobenius.frobFun_eq hsign (b := 1) (k := (g : Matrix (Fin n) (Fin n) ℝ))
    Matrix.blockTriangular_one hg (one_mul _).symm v, RealJacquetFrobenius.diagChar_one, one_mul,
    LinearMap.comp_apply, hrep, blockJacquet_apply]
  simp_rw [blockFourierCoefficient_rep, toUnits_mk]

/-- The sign multiplier is flat for `δ = w + 1` on coefficients `c` vanishing in the window
`|j| < w` and off the parity class `j ≡ w + 1`. -/
theorem flat_sign_of {ε : ℤ} {w : ℕ} (hεw : Even (ε - w - 1)) {c : ℤ → ℂ}
    (hwin : ∀ j : ℤ, |j| < w → c j = 0) (hpar : ∀ j : ℤ, ¬ Even (j - ε) → c j = 0)
    {δ : ℂ} (hδ : δ = (w : ℂ) + 1) (j : ℤ) (hj : c j ≠ 0) :
    (fun j : ℤ => ((Int.sign j : ℤ) : ℂ)) (j + 2) * (δ + j) =
        (fun j : ℤ => ((Int.sign j : ℤ) : ℂ)) j * (δ + j) ∧
      (fun j : ℤ => ((Int.sign j : ℤ) : ℂ)) (j - 2) * (δ - j) =
        (fun j : ℤ => ((Int.sign j : ℤ) : ℂ)) j * (δ - j) := by
  have h1 : (w : ℤ) ≤ |j| := not_lt.mp fun h => hj (hwin j h)
  have h2 : Even (j - ε) := by
    by_contra h
    exact hj (hpar j h)
  rw [le_abs] at h1
  rw [Int.even_iff] at h2 hεw
  have hplus : ∀ m : ℤ, (w : ℤ) + 1 + m = 0 → δ + m = 0 := fun m hm => by
    rw [hδ]
    exact_mod_cast hm
  have hminus : ∀ m : ℤ, (w : ℤ) + 1 - m = 0 → δ - m = 0 := fun m hm => by
    rw [hδ]
    exact_mod_cast hm
  simp only
  rcases lt_trichotomy j 0 with hneg | hzero | hpos
  · have hs : j.sign = -1 := Int.sign_eq_neg_one_of_neg hneg
    refine ⟨?_, ?_⟩
    · by_cases h3 : j + 2 < 0
      · rw [hs, Int.sign_eq_neg_one_of_neg h3]
      · rw [hplus j (by omega), mul_zero, mul_zero]
    · rw [hs, Int.sign_eq_neg_one_of_neg (by omega)]
  · subst hzero
    omega
  · have hs : j.sign = 1 := Int.sign_eq_one_of_pos hpos
    refine ⟨?_, ?_⟩
    · rw [hs, Int.sign_eq_one_of_pos (by omega)]
    · by_cases h3 : 0 < j - 2
      · rw [hs, Int.sign_eq_one_of_pos h3]
      · rw [hminus j (by omega), mul_zero, mul_zero]

/-- **The dichotomy.** Let `B` be an intertwiner into the principal series of `PL τ e` with a
linked adjacent pair `τ_b - τ_{b+1} = k₁` at a block `b`. Either the binomial functional at `b`
composed with `B` is nonzero, or the window `|j| < k₁` of every `B v` vanishes at `b` on `O(n)`;
then the sign multiplier at `b` is flat on the functions `B v`, and the binomial functional at a
second linked adjacent pair `r` of the flipped signs `e'` gives the conclusion, provided some
`θ ↦ Σᶠ_j sgn(j) Φ^{(b)}_j(B v)(r_r(θ))` has a nonzero coefficient in the parity class. -/
theorem exists_of_dichotomy {τ : Fin n → ℂ} {e : Fin n → Fin 2}
    (B : KF n ds →ₗ[ℂ] KF n (PL τ e))
    (hrep : ∀ κ v, B (realStandardRep n ds κ v) = realStandardRep n (PL τ e) κ (B v))
    (hlie : ∀ Y v, B (realStandardLie n ds Y v) = realStandardLie n (PL τ e) Y (B v))
    {b : ℕ} (hb : b + 1 < n) {k₁ : ℕ} (hk₁ : 0 < k₁) (hτ₁ : τ (ia hb) - τ (ib hb) = k₁)
    (hodd₁ : Odd (k₁ + (e (ia hb)).val + (e (ib hb)).val))
    {e' : Fin n → Fin 2}
    (he_off : ∀ i : Fin n, i ≠ ia hb → i ≠ ib hb → e' i = e i)
    (he_p : (-1 : ℂ) ^ (e' (ia hb)).val = -(-1) ^ (e (ia hb)).val)
    (he_q : (-1 : ℂ) ^ (e' (ib hb)).val = -(-1) ^ (e (ib hb)).val)
    {r : ℕ} (hr : r + 1 < n) {k₂ : ℕ} (hk₂ : 0 < k₂) (hτ₂ : τ (ia hr) - τ (ib hr) = k₂)
    (hodd₂ : Odd (k₂ + (e' (ia hr)).val + (e' (ib hr)).val))
    (hmain : (∀ (v : KF n ds) (j : ℤ), |j| < k₁ → ∀ κ ∈ unitaryCompact ℝ n,
        blockFourierCoefficient n b j (B v) κ = 0) →
      ∃ v : KF n ds, coeff ((par hr e' : ℕ) : ℤ) (fun θ => ∑ᶠ j : ℤ, ((Int.sign j : ℤ) : ℂ) *
        blockFourierCoefficient n b j (B v) (blockRotation n r θ)) ≠ 0) :
    RealLinkedJacquetFunctionalExists n ds := by
  by_cases hΛ : blockJacquet n (PL τ e) b (binomialMultiplier k₁ ((par hb e : ℕ) : ℤ)) ∘ₗ B = 0
  swap
  · exact exists_of_comp_ne B hrep hlie hb hk₁ hτ₁ hodd₁ hΛ
  set ε : ℤ := ((par hb e : ℕ) : ℤ) with hεdef
  have hε : ε = 0 ∨ ε = 1 := par_cases hb e
  have hpar1 : Even ((k₁ : ℤ) - 1 - ε) := by
    rw [hεdef, Int.even_iff]
    unfold par
    obtain ⟨m, hm⟩ := hodd₁
    omega
  have hrec : IsRecurrent (τ (ia hb) - τ (ib hb) + 1) (par hb e) (binomialMultiplier k₁ ε) := by
    rw [hτ₁]
    exact isRecurrent_binomialMultiplier hk₁ hε hpar1
  have hsym : IsSymmetric (par hb e) ((-1) ^ par hb e) (binomialMultiplier k₁ ε) :=
    isSymmetric_binomialMultiplier k₁ hε
  have hJ := isJacquet_cross hb τ e hrec hsym
  have hsignΛ : ∀ (i : Fin n) (w : KF n (PL τ e)),
      blockJacquet n (PL τ e) b (binomialMultiplier k₁ ε)
          (realStandardRep n (PL τ e) (signReflection n i) w) =
        (-1) ^ ((e ∘ sw hb) i).val * blockJacquet n (PL τ e) b (binomialMultiplier k₁ ε) w :=
    fun i w => (hJ.2 i w).2
  have hwin : ∀ (v : KF n ds) (j : ℤ), |j| < k₁ → ∀ κ ∈ unitaryCompact ℝ n,
      blockFourierCoefficient n b j (B v) κ = 0 := by
    intro v j hj κ hκ
    by_cases hje : Even (j - ε)
    · exact blockFourierCoefficient_eq_zero_of_comp hb hsignΛ B hrep hΛ
        ((binomialMultiplier_ne_zero_iff hk₁ hε hpar1 hje).mpr hj) v hκ
    · exact blockFourierCoefficient_eq_zero_of_not_even hb (PL_parity hb τ e) (B v) hje κ
  obtain ⟨v, hv⟩ := hmain hwin
  -- the sign multiplier at `b`
  have hδ : (τ (ia hb) + ((n : ℂ) - 1) / 2 - (((ia hb : Fin n) : ℕ) : ℂ)) -
      (τ (ib hb) + ((n : ℂ) - 1) / 2 - (((ib hb : Fin n) : ℕ) : ℂ)) = (k₁ : ℂ) + 1 := by
    have h := hτ₁
    simp only [ia, ib] at h ⊢
    push_cast
    linear_combination h
  have hεw : Even (ε - k₁ - 1) := by
    rw [hεdef, Int.even_iff]
    unfold par
    obtain ⟨m, hm⟩ := hodd₁
    omega
  have hflat : ∀ (w : KF n ds) (j : ℤ), blockFourierCoefficient n b j (B w) 1 ≠ 0 →
      (fun j : ℤ => ((Int.sign j : ℤ) : ℂ)) (j + 2) * (((k₁ : ℂ) + 1) + j) =
          (fun j : ℤ => ((Int.sign j : ℤ) : ℂ)) j * (((k₁ : ℂ) + 1) + j) ∧
        (fun j : ℤ => ((Int.sign j : ℤ) : ℂ)) (j - 2) * (((k₁ : ℂ) + 1) - j) =
          (fun j : ℤ => ((Int.sign j : ℤ) : ℂ)) j * (((k₁ : ℂ) + 1) - j) :=
    fun w j hj => flat_sign_of hεw (c := fun j => blockFourierCoefficient n b j (B w) 1)
      (fun j hj => hwin w j hj 1 (one_mem _))
      (fun j hj => blockFourierCoefficient_eq_zero_of_not_even hb (PL_parity hb τ e) (B w) hj 1)
      rfl j hj
  have hψ := isRealJacquetFunctional_comp_flat hb (PL_position_exp τ e) (PL_parity hb τ e) hδ
    B hrep hlie hflat (isSymmetric_sign _) (e := e')
    (fun i h1 h2 => by rw [he_off i h1 h2, PL_position_neg_one])
    (by
      rw [he_p, show realPositionCharacter (PL τ e) b (-1) = (-1) ^ (e (ia hb)).val from
        PL_position_neg_one τ e (ia hb)]
      ring)
    (by
      rw [he_q, show realPositionCharacter (PL τ e) (b + 1) (-1) = (-1) ^ (e (ib hb)).val from
        PL_position_neg_one τ e (ib hb)]
      ring)
  have hsign : ∀ (i : Fin n) (w : KF n ds),
      (blockJacquet n (PL τ e) b (fun j : ℤ => ((Int.sign j : ℤ) : ℂ)) ∘ₗ B)
          (realStandardRep n ds (signReflection n i) w) =
        (-1) ^ (e' i).val *
          (blockJacquet n (PL τ e) b (fun j : ℤ => ((Int.sign j : ℤ) : ℂ)) ∘ₗ B) w :=
    fun i w => (hψ.2 i w).2
  refine exists_of_comp (frobMap hψ) (frobMap_rep hψ) (frobMap_lie hψ) hr hk₂ ?_ hodd₂ v ?_
  · simp only [RealJacquetFrobenius.expo]
    linear_combination hτ₂
  · rw [blockFourierCoefficient_eq_coeff]
    have h : (fun θ : ℝ => ((frobMap hψ v : KF n _) : Langlands.GeneralLinear n ℝ → ℂ)
        (blockRotation n r θ * 1)) = (2 * (Real.pi : ℂ))⁻¹ • fun θ => ∑ᶠ j : ℤ,
          ((Int.sign j : ℤ) : ℂ) * blockFourierCoefficient n b j (B v) (blockRotation n r θ) := by
      funext θ
      rw [frobMap_coe, mul_one,
        frobFun_comp_apply_of_mem B hrep hsign v (blockRotation_mem_unitaryCompact n r θ)]
      rfl
    rw [h, coeff_smul]
    exact mul_ne_zero (inv_ne_zero (mul_ne_zero two_ne_zero
      (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))) hv

end Composite

/-! ## Mode expansions

A function `H` on matrices has the expansion `P` of order `N` along the rotations of the block
`b` if `H(r_b(t) X) = e^{-iNt} P(e^{it})(X)` for a polynomial `P` of degree `≤ 2N` whose
coefficients are functions on matrices: the coefficient `P_k` is the mode `k - N`. -/

section Expansion

/-- The commutative ring of complex functions on real `n × n` matrices. -/
abbrev MF (n : ℕ) := Matrix (Fin n) (Fin n) ℝ → ℂ

/-- `H(r_b(t) X) = e^{-iNt} P(e^{it})(X)` with `deg P ≤ 2N`. -/
def IsExpansion (b N : ℕ) (H : MF n) (P : Polynomial (MF n)) : Prop :=
  P.natDegree ≤ 2 * N ∧ ∀ (t : ℝ) (X : Matrix (Fin n) (Fin n) ℝ),
    H ((blockRotation n b t : Matrix (Fin n) (Fin n) ℝ) * X) =
      expMode (-(N : ℤ)) t * (P.map (Pi.evalRingHom (fun _ => ℂ) X)).eval (expMode 1 t)

theorem eval_map_eq_sum (P : Polynomial (MF n)) {m : ℕ} (hm : P.natDegree < m)
    (X : Matrix (Fin n) (Fin n) ℝ) (z : ℂ) :
    (P.map (Pi.evalRingHom (fun _ => ℂ) X)).eval z = ∑ k ∈ Finset.range m, P.coeff k X * z ^ k := by
  rw [Polynomial.eval_eq_sum_range' ((Polynomial.natDegree_map_le).trans_lt hm)]
  simp [Polynomial.coeff_map]

theorem expMode_one_pow (k : ℕ) (t : ℝ) : expMode 1 t ^ k = expMode k t := by
  simp only [expMode, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

theorem expMode_mul_expMode (j k : ℤ) (t : ℝ) : expMode j t * expMode k t = expMode (j + k) t :=
  congrFun (expMode_add j k) t

theorem IsExpansion.apply {b N : ℕ} {H : MF n} {P : Polynomial (MF n)} (h : IsExpansion b N H P)
    (t : ℝ) (X : Matrix (Fin n) (Fin n) ℝ) :
    H ((blockRotation n b t : Matrix (Fin n) (Fin n) ℝ) * X) =
      ∑ k ∈ Finset.range (2 * N + 1), P.coeff k X * expMode ((k : ℤ) - N) t := by
  rw [h.2, eval_map_eq_sum P (Nat.lt_succ_of_le h.1), Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [expMode_one_pow, mul_left_comm, expMode_mul_expMode]
  ring_nf

theorem isExpansion_zero (b N : ℕ) : IsExpansion b N (0 : MF n) 0 :=
  ⟨by simp, fun t X => by simp⟩

theorem IsExpansion.add {b N : ℕ} {H H' : MF n} {P P' : Polynomial (MF n)}
    (h : IsExpansion b N H P) (h' : IsExpansion b N H' P') : IsExpansion b N (H + H') (P + P') :=
  ⟨(Polynomial.natDegree_add_le _ _).trans (max_le h.1 h'.1), fun t X => by
    rw [Pi.add_apply, h.2, h'.2, Polynomial.map_add, Polynomial.eval_add, mul_add]⟩

theorem IsExpansion.mul {b N N' : ℕ} {H H' : MF n} {P P' : Polynomial (MF n)}
    (h : IsExpansion b N H P) (h' : IsExpansion b N' H' P') :
    IsExpansion b (N + N') (H * H') (P * P') :=
  ⟨(Polynomial.natDegree_mul_le).trans (by have := h.1; have := h'.1; omega), fun t X => by
    rw [Pi.mul_apply, h.2, h'.2, Polynomial.map_mul, Polynomial.eval_mul]
    have e : expMode (-((N + N' : ℕ) : ℤ)) t = expMode (-(N : ℤ)) t * expMode (-(N' : ℤ)) t := by
      rw [expMode_mul_expMode]
      push_cast
      ring_nf
    rw [e]
    ring⟩

theorem IsExpansion.const_mul {b N : ℕ} {H : MF n} {P : Polynomial (MF n)}
    (h : IsExpansion b N H P) (c : ℂ) :
    IsExpansion b N (c • H) (Polynomial.C (fun _ => c) * P) :=
  ⟨(Polynomial.natDegree_C_mul_le _ _).trans h.1, fun t X => by
    rw [Pi.smul_apply, h.2, Polynomial.map_mul, Polynomial.map_C, Polynomial.eval_mul,
      Polynomial.eval_C, smul_eq_mul]
    simp only [Pi.evalRingHom_apply]
    ring⟩

/-- The coefficients of the expansion are the block Fourier modes. -/
theorem coeff_finset_sum_nat (I : Finset ℕ) (F : ℕ → ℝ → ℂ) (hF : ∀ i ∈ I, Continuous (F i))
    (k : ℤ) : coeff k (fun θ => ∑ i ∈ I, F i θ) = ∑ i ∈ I, coeff k (F i) := by
  unfold coeff
  simp_rw [Finset.sum_mul]
  exact intervalIntegral.integral_finsetSum fun i hi => intervalIntegrable_coeff (hF i hi) k _ _

theorem coeff_sum_expMode (N m : ℕ) (c : ℕ → ℂ) (j : ℤ) :
    coeff j (fun t => ∑ k ∈ Finset.range m, c k * expMode ((k : ℤ) - N) t) =
      ∑ k ∈ Finset.range m, c k * (if (k : ℤ) - N = j then 2 * (Real.pi : ℂ) else 0) := by
  rw [coeff_finset_sum_nat _ (fun k t => c k * expMode ((k : ℤ) - N) t)
    fun k _ => continuous_const.mul (continuous_expMode _)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [show (fun t => c k * expMode ((k : ℤ) - N) t) = c k • expMode ((k : ℤ) - N) from rfl,
    coeff_smul, coeff_expMode]

theorem sum_ite_mode (N m : ℕ) (c : ℕ → ℂ) {j : ℤ} (hj0 : 0 ≤ j + N) (hjm : j + N < m) :
    ∑ k ∈ Finset.range m, c k * (if (k : ℤ) - N = j then 2 * (Real.pi : ℂ) else 0) =
      2 * (Real.pi : ℂ) * c (j + N).toNat := by
  rw [Finset.sum_eq_single (j + N).toNat]
  · rw [ite_eq_left (by omega)]
    ring
  · intro k _ hk
    rw [ite_eq_right (by omega), mul_zero]
  · intro h
    exact absurd (Finset.mem_range.mpr (by omega)) h

theorem sum_ite_mode_eq_zero (N m : ℕ) (c : ℕ → ℂ) {j : ℤ} (hj : j + N < 0 ∨ m ≤ j + N) :
    ∑ k ∈ Finset.range m, c k * (if (k : ℤ) - N = j then 2 * (Real.pi : ℂ) else 0) = 0 := by
  refine Finset.sum_eq_zero fun k hk => ?_
  rw [Finset.mem_range] at hk
  rw [ite_eq_right (by omega), mul_zero]

/-- **Modes of an expansion.** If `f` agrees with `H` along the orbit `r_b(t) κ` and `H` has
the expansion `P` of order `N`, then `Φ_j f (κ) = 2π P_{j+N}(κ)` for `|j| ≤ N`. -/
theorem blockFourierCoefficient_of_expansion {b N : ℕ} {H : MF n} {P : Polynomial (MF n)}
    (h : IsExpansion b N H P) {f : Langlands.GeneralLinear n ℝ → ℂ}
    {κ : Langlands.GeneralLinear n ℝ}
    (hf : ∀ t : ℝ, f (blockRotation n b t * κ) =
      H ((blockRotation n b t : Matrix (Fin n) (Fin n) ℝ) * (κ : Matrix (Fin n) (Fin n) ℝ)))
    (j : ℤ) :
    blockFourierCoefficient n b j f κ = ∑ k ∈ Finset.range (2 * N + 1),
      P.coeff k (κ : Matrix (Fin n) (Fin n) ℝ) *
        (if (k : ℤ) - N = j then 2 * (Real.pi : ℂ) else 0) := by
  rw [blockFourierCoefficient_eq_coeff]
  have e : (fun t => f (blockRotation n b t * κ)) = fun t => ∑ k ∈ Finset.range (2 * N + 1),
      P.coeff k (κ : Matrix (Fin n) (Fin n) ℝ) * expMode ((k : ℤ) - N) t := by
    funext t
    rw [hf, h.apply]
  rw [e, coeff_sum_expMode]

/-- **A multiplier on an expansion.** `(2π)⁻¹ Σᶠ_j μ_j Φ_j f (κ) = Σ_k μ_{k - N} P_k(κ)`. -/
theorem finsum_of_expansion {b N : ℕ} {H : MF n} {P : Polynomial (MF n)}
    (h : IsExpansion b N H P) {f : Langlands.GeneralLinear n ℝ → ℂ}
    {κ : Langlands.GeneralLinear n ℝ}
    (hf : ∀ t : ℝ, f (blockRotation n b t * κ) =
      H ((blockRotation n b t : Matrix (Fin n) (Fin n) ℝ) * (κ : Matrix (Fin n) (Fin n) ℝ)))
    (μ : ℤ → ℂ) :
    (2 * (Real.pi : ℂ))⁻¹ * ∑ᶠ j : ℤ, μ j * blockFourierCoefficient n b j f κ =
      ∑ k ∈ Finset.range (2 * N + 1), μ ((k : ℤ) - N) * P.coeff k (κ : Matrix (Fin n) (Fin n) ℝ) := by
  simp_rw [blockFourierCoefficient_of_expansion h hf]
  set c : ℕ → ℂ := fun k => P.coeff k (κ : Matrix (Fin n) (Fin n) ℝ) with hc
  set I : Finset ℤ := (Finset.range (2 * N + 1)).image fun k : ℕ => (k : ℤ) - N with hI
  rw [finsum_eq_sum_of_support_subset (s := I)]
  · have e : ∀ j ∈ I, μ j * ∑ k ∈ Finset.range (2 * N + 1),
        c k * (if (k : ℤ) - N = j then 2 * (Real.pi : ℂ) else 0) =
          ∑ k ∈ Finset.range (2 * N + 1),
            (if (k : ℤ) - N = j then 2 * (Real.pi : ℂ) * (μ ((k : ℤ) - N) * c k) else 0) := by
      intro j _
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      split_ifs with hkj
      · rw [hkj]
        ring
      · ring
    rw [Finset.sum_congr rfl e, Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hkI : (k : ℤ) - N ∈ I := Finset.mem_image_of_mem _ hk
    rw [Finset.sum_ite_eq, ite_eq_left hkI]
    field_simp
    rfl
  · intro j hj
    rw [Function.mem_support] at hj
    by_contra hjI
    apply hj
    rw [Finset.sum_eq_zero, mul_zero]
    intro k hk
    rw [ite_eq_right, mul_zero]
    intro hkj
    apply hjI
    rw [Finset.mem_coe, hI, Finset.mem_image]
    exact ⟨k, hk, hkj⟩

/-! ### Submodules closed under expansion -/

/-- Every `H ∈ S` has an expansion of order `N` along `b` with coefficients in `S` and top
coefficient in `T`. -/
def HasExpTop (b N : ℕ) (S T : Submodule ℂ (MF n)) : Prop :=
  ∀ H ∈ S, ∃ P : Polynomial (MF n), IsExpansion b N H P ∧ (∀ k, P.coeff k ∈ S) ∧
    P.coeff (2 * N) ∈ T

theorem hasExpTop_mul {b N N' : ℕ} {S S' T T' : Submodule ℂ (MF n)} (h : HasExpTop b N S T)
    (h' : HasExpTop b N' S' T') : HasExpTop b (N + N') (S * S') (T * T') := by
  intro H hH
  refine Submodule.mul_induction_on (C := fun H => ∃ P : Polynomial (MF n),
    IsExpansion b (N + N') H P ∧ (∀ k, P.coeff k ∈ S * S') ∧ P.coeff (2 * (N + N')) ∈ T * T')
    hH ?_ ?_
  · intro x hx y hy
    obtain ⟨P, hP, hPS, hPT⟩ := h x hx
    obtain ⟨P', hP', hPS', hPT'⟩ := h' y hy
    refine ⟨P * P', hP.mul hP', fun k => ?_, ?_⟩
    · rw [Polynomial.coeff_mul]
      exact Submodule.sum_mem _ fun i _ => Submodule.mul_mem_mul (hPS _) (hPS' _)
    · rw [show 2 * (N + N') = 2 * N + 2 * N' by ring,
        Polynomial.coeff_mul_add_eq_of_natDegree_le hP.1 hP'.1]
      exact Submodule.mul_mem_mul hPT hPT'
  · intro x y hx hy
    obtain ⟨P, hP, hPS, hPT⟩ := hx
    obtain ⟨P', hP', hPS', hPT'⟩ := hy
    refine ⟨P + P', hP.add hP', fun k => ?_, ?_⟩
    · rw [Polynomial.coeff_add]
      exact Submodule.add_mem _ (hPS k) (hPS' k)
    · rw [Polynomial.coeff_add]
      exact Submodule.add_mem _ hPT hPT'

theorem hasExpTop_one (b : ℕ) : HasExpTop b 0 (1 : Submodule ℂ (MF n)) 1 := by
  intro H hH
  refine ⟨Polynomial.C H, ⟨by rw [Polynomial.natDegree_C], fun t X => ?_⟩, fun k => ?_, ?_⟩
  · obtain ⟨c, rfl⟩ := Submodule.mem_one.mp hH
    simp [expMode_zero_left]
  · rw [Polynomial.coeff_C]
    split_ifs
    · exact hH
    · exact Submodule.zero_mem _
  · rw [Nat.mul_zero, Polynomial.coeff_C_zero]
    exact hH

theorem hasExpTop_pow {b N : ℕ} {S T : Submodule ℂ (MF n)} (h : HasExpTop b N S T) :
    ∀ m : ℕ, HasExpTop b (m * N) (S ^ m) (T ^ m)
  | 0 => by simpa using hasExpTop_one b
  | m + 1 => by
    rw [pow_succ, pow_succ, Nat.succ_mul]
    exact hasExpTop_mul (hasExpTop_pow h m) h

/-- The quadratic polynomial `a₂ X² + a₁ X + a₀`. -/
def quad (a₂ a₁ a₀ : MF n) : Polynomial (MF n) :=
  Polynomial.C a₂ * Polynomial.X ^ 2 + Polynomial.C a₁ * Polynomial.X + Polynomial.C a₀

theorem coeff_quad (a₂ a₁ a₀ : MF n) (k : ℕ) :
    (quad a₂ a₁ a₀).coeff k =
      (if k = 2 then a₂ else 0) + (if k = 1 then a₁ else 0) + (if k = 0 then a₀ else 0) := by
  simp only [quad, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
    Polynomial.coeff_X, Polynomial.coeff_C]
  rcases k with _ | _ | _ | k
  · simp
  · simp
  · simp
  · have h2 : k + 1 + 1 + 1 ≠ 2 := by omega
    simp [h2]

/-- **Generators.** If `g(r_b(t) X) = cos t A(X) + sin t B(X) + C(X)`, then `g` has the
expansion of order `1` with coefficients `(A + iB)/2, C, (A - iB)/2`. -/
theorem isExpansion_of_cos_sin {b : ℕ} {g A B C : MF n}
    (hg : ∀ (t : ℝ) (X : Matrix (Fin n) (Fin n) ℝ),
      g ((blockRotation n b t : Matrix (Fin n) (Fin n) ℝ) * X) =
        (Real.cos t : ℂ) * A X + (Real.sin t : ℂ) * B X + C X) :
    IsExpansion b 1 g (quad ((1 / 2 : ℂ) • (A - Complex.I • B)) C ((1 / 2 : ℂ) • (A + Complex.I • B))) := by
  refine ⟨Polynomial.natDegree_quadratic_le, fun t X => ?_⟩
  rw [hg]
  simp only [quad, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow,
    Polynomial.map_X, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_X, Pi.evalRingHom_apply, Pi.smul_apply, Pi.add_apply,
    Pi.sub_apply, smul_eq_mul]
  rw [show (-((1 : ℕ) : ℤ)) = -1 by norm_num, expMode_neg_one_eq, expMode_one_eq]
  have h1 := Real.sin_sq_add_cos_sq t
  have h1' : (Real.sin t : ℂ) ^ 2 + (Real.cos t : ℂ) ^ 2 = 1 := by exact_mod_cast h1
  linear_combination (-((1 / 2 : ℂ) * (A X - Complex.I * B X) *
      ((Real.cos t : ℂ) + Complex.I * Real.sin t) + C X)) * h1' +
    ((Real.sin t : ℂ) * B X + (Real.sin t : ℂ) ^ 2 * ((1 / 2 : ℂ) * (A X - Complex.I * B X) *
      ((Real.cos t : ℂ) + Complex.I * Real.sin t) + C X)) * Complex.I_sq

/-- **Spans of generators.** If every generator has an expansion of order `1` with coefficients
in the span and top coefficient in `T`, so has every element of the span. -/
theorem hasExpTop_span {b : ℕ} {s : Set (MF n)} {T : Submodule ℂ (MF n)}
    (hs : ∀ g ∈ s, ∃ P : Polynomial (MF n), IsExpansion b 1 g P ∧
      (∀ k, P.coeff k ∈ Submodule.span ℂ s) ∧ P.coeff 2 ∈ T) :
    HasExpTop b 1 (Submodule.span ℂ s) T := by
  intro H hH
  induction hH using Submodule.span_induction with
  | mem x hx => exact hs x hx
  | zero => exact ⟨0, isExpansion_zero b 1, fun k => by simp, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨P, hP, hPS, hPT⟩ := hx
    obtain ⟨P', hP', hPS', hPT'⟩ := hy
    refine ⟨P + P', hP.add hP', fun k => ?_, ?_⟩
    · rw [Polynomial.coeff_add]
      exact Submodule.add_mem _ (hPS k) (hPS' k)
    · rw [Polynomial.coeff_add]
      exact Submodule.add_mem _ hPT hPT'
  | smul c x _ hx =>
    obtain ⟨P, hP, hPS, hPT⟩ := hx
    refine ⟨Polynomial.C (fun _ => c) * P, hP.const_mul c, fun k => ?_, ?_⟩
    · rw [Polynomial.coeff_C_mul]
      have e : (fun _ => c) * P.coeff k = c • P.coeff k := by
        funext X
        simp
      rw [e]
      exact Submodule.smul_mem _ c (hPS k)
    · rw [Polynomial.coeff_C_mul]
      have e : (fun _ => c) * P.coeff 2 = c • P.coeff 2 := by
        funext X
        simp
      rw [e]
      exact Submodule.smul_mem _ c hPT

end Expansion

end RealInterlacedJacquet

end Langlands.Archimedean
