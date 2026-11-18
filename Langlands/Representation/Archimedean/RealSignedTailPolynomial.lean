import Langlands.Representation.Archimedean.RealCompactPolynomialFourierRelation

/-! # The spectral sign in canonical tail multipliers -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean.RealSignedTailPolynomial

open Polynomial Complex RealBlockMultiplier RealTailMultiplierPolynomial
open RealOrthogonalUncertainty

theorem canonical_sign {ℓ : ℕ} {ε : ℤ}
    (hε : ε = 0 ∨ ε = 1) (hpar : Even ((ℓ : ℤ) - 1 - ε)) :
    (-1 : ℂ) ^ ε.natAbs = -(-1 : ℂ) ^ ℓ := by
  rw [neg_one_pow_eq_pow_mod_two (n := ℓ)]
  rcases hε with rfl | rfl
  · have hp : ℓ % 2 = 1 := by rw [Int.even_iff] at hpar; omega
    rw [hp]
    norm_num
  · have hp : ℓ % 2 = 0 := by rw [Int.even_iff] at hpar; omega
    rw [hp]
    norm_num

theorem canonical_tail_eq {ℓ : ℕ} {ε j : ℤ}
    (hℓ : 0 < ℓ) (hε : ε = 0 ∨ ε = 1)
    (hpar : Even ((ℓ : ℤ) - 1 - ε)) (hj : Even (j - ε)) :
    tailMultiplier ℓ ε ((-1 : ℂ) ^ ε.natAbs) j =
      ((Int.sign j : ℤ) : ℂ) * (tailPolynomial ℓ).eval (j : ℂ) := by
  rcases lt_trichotomy j 0 with hn | hz | hp
  · have he : Even (-j - ε) := by
      rw [Int.even_iff] at hj ⊢
      omega
    have hs := isSymmetric_tailMultiplier hℓ hε hpar (neg_one_pow_sq ε.natAbs) j hj
    have hpoly := tailPolynomial_eq_of_nonneg hℓ hε hpar (by omega : 0 ≤ -j) he
    have hneg : tailMultiplier ℓ ε ((-1 : ℂ) ^ ε.natAbs) (-j) =
        (tailPolynomial ℓ).eval (-((j : ℤ) : ℂ)) := by
      simpa only [tailMultiplier, extend_of_nonneg (by omega : 0 ≤ -j),
        Int.cast_neg] using hpoly
    have hσ := canonical_sign hε hpar
    rw [hneg, tailPolynomial_neg] at hs
    have hs' := hs.trans
      (congrArg (fun σ : ℂ => σ * tailMultiplier ℓ ε ((-1 : ℂ) ^ ε.natAbs) j) hσ)
    have hpow : (-1 : ℂ) ^ ℓ ≠ 0 := pow_ne_zero _ (by norm_num)
    rw [Int.sign_eq_neg_one_of_neg hn, Int.cast_neg, Int.cast_one]
    apply mul_left_cancel₀ hpow
    linear_combination hs'
  · subst j
    have he : ε = 0 := by
      rw [Int.even_iff] at hj
      omega
    subst ε
    have hp : ℓ % 2 = 1 := by rw [Int.even_iff] at hpar; omega
    have hP : (tailPolynomial ℓ).eval (0 : ℂ) = 0 := by
      have hh := tailPolynomial_neg ℓ 0
      rw [neg_zero, neg_one_pow_eq_pow_mod_two (n := ℓ), hp] at hh
      norm_num at hh
      linear_combination hh / 2
    have ht := tailPolynomial_eq hℓ (Or.inl rfl) hpar 0 (by norm_num)
    have hs : tailMultiplier ℓ 0 ((-1 : ℂ) ^ (0 : ℤ).natAbs) 0 =
        tailMultiplier ℓ 0 ((-1 : ℂ) ^ ℓ) 0 := by
      simp only [tailMultiplier, extend_of_nonneg le_rfl]
    rw [hs, ht]
    simp [hP]
  · have hpoly := tailPolynomial_eq_of_nonneg hℓ hε hpar hp.le hj
    have hs : tailMultiplier ℓ ε ((-1 : ℂ) ^ ε.natAbs) j =
        tailMultiplier ℓ ε ((-1 : ℂ) ^ ℓ) j := by
      simp only [tailMultiplier, extend_of_nonneg hp.le]
    rw [hs, hpoly, Int.sign_eq_one_of_pos hp, Int.cast_one, one_mul]

section Spectral

variable {W : Type*} [AddCommGroup W] [Module ℂ W]
  {a : Module.End ℂ W} {π : ℤ → Module.End ℂ W} {S : Finset ℤ}

def spectralMultiplier (π : ℤ → Module.End ℂ W) (S : Finset ℤ) (μ : ℤ → ℂ) :
    Module.End ℂ W :=
  ∑ j ∈ S, μ j • π j

theorem proj_spectralMultiplier (hM : IsModeDecomposition a π S)
    (μ : ℤ → ℂ) (j : ℤ) (v : W) :
    π j (spectralMultiplier π S μ v) = μ j • π j v := by
  rw [spectralMultiplier, LinearMap.sum_apply, map_sum]
  simp_rw [LinearMap.smul_apply, map_smul, hM.proj_apply_proj]
  rw [Finset.sum_eq_single j]
  · simp
  · intro k _ hkj
    simp [Ne.symm hkj]
  · intro hj
    rw [hM.eq_zero j hj]
    simp

theorem spectralMultiplier_comp (hM : IsModeDecomposition a π S)
    (μ ν : ℤ → ℂ) :
    (spectralMultiplier π S μ).comp (spectralMultiplier π S ν) =
      spectralMultiplier π S (fun j => μ j * ν j) := by
  apply LinearMap.ext
  intro v
  rw [← hM.sum_apply ((spectralMultiplier π S μ).comp (spectralMultiplier π S ν) v),
    ← hM.sum_apply (spectralMultiplier π S (fun j => μ j * ν j) v)]
  apply Finset.sum_congr rfl
  intro j _
  change π j (spectralMultiplier π S μ (spectralMultiplier π S ν v)) = _
  rw [proj_spectralMultiplier hM, proj_spectralMultiplier hM,
    proj_spectralMultiplier hM, smul_smul]

theorem spectralMultiplier_aeval_comm (hM : IsModeDecomposition a π S)
    (μ : ℤ → ℂ) (P : ℂ[X]) (v : W) :
    spectralMultiplier π S μ (aeval (-I • a) P v) =
      aeval (-I • a) P (spectralMultiplier π S μ v) := by
  rw [← hM.sum_apply (spectralMultiplier π S μ (aeval (-I • a) P v)),
    ← hM.sum_apply (aeval (-I • a) P (spectralMultiplier π S μ v))]
  apply Finset.sum_congr rfl
  intro j _
  rw [proj_spectralMultiplier hM, RealPolynomialFourierPropagation.proj_aeval hM,
    RealPolynomialFourierPropagation.proj_aeval hM, proj_spectralMultiplier hM,
    smul_smul, smul_smul, mul_comm]

end Spectral

def signOperator (N : ℕ) {p : ℕ} (hp : p + 1 < 3) :
    Module.End ℂ (RealKTypeCount.degreeLE 3 N) :=
  spectralMultiplier (proj N hp) (Finset.Icc (-(N : ℤ)) N)
    (fun j => ((Int.sign j : ℤ) : ℂ))

open Langlands.LocalFactor.Archimedean RealBlockFrobeniusMap RealStandardFiltration
open RealKTypeCount RealCompactPolynomialFourierRelation RealPolynomialFourierPropagation

theorem frob_restrict_eq_spectral {N p : ℕ} {ds es : List RealBlock} {ε : ℤ} {τ : ℂ}
    {μ : ℤ → ℂ} (hdata : IsBlockFrobData 3 ds es p ε τ μ) (f : KF 3 ds)
    (hNf : restrictLinear 3 (f : Langlands.GeneralLinear 3 ℝ → ℂ) ∈ degreeLE 3 N) :
    restrictLinear 3 (blockFrobMap hdata f : Langlands.GeneralLinear 3 ℝ → ℂ) =
      (spectralMultiplier (proj N hdata.lt) (Finset.Icc (-(N : ℤ)) N) μ
        (vector (f : Langlands.GeneralLinear 3 ℝ → ℂ) hNf) :
          Matrix.unitaryGroup (Fin 3) ℝ → ℂ) := by
  let g := blockFrobMap hdata f
  obtain ⟨Ng, hNg⟩ := exists_degreeLE (RealBlockJacquet.continuous_coe g) g.2.2
  let T := max N Ng
  let u := spectralMultiplier (proj N hdata.lt) (Finset.Icc (-(N : ℤ)) N) μ
    (vector (f : Langlands.GeneralLinear 3 ℝ → ℂ) hNf)
  have hNgT : restrictLinear 3 (g : Langlands.GeneralLinear 3 ℝ → ℂ) ∈ degreeLE 3 T :=
    degreeLE_mono (le_max_right N Ng) hNg
  let vg : degreeLE 3 T := vector (g : Langlands.GeneralLinear 3 ℝ → ℂ) hNgT
  let vu : degreeLE 3 T :=
    ⟨(u : Matrix.unitaryGroup (Fin 3) ℝ → ℂ), degreeLE_mono (le_max_left N Ng) u.2⟩
  have hproj : ∀ j, proj T hdata.lt j vg = proj T hdata.lt j vu := by
    intro j
    apply Subtype.ext
    funext x
    have hs := proj_spectralMultiplier (isModeDecomposition N hdata.lt) μ j
      (vector (f : Langlands.GeneralLinear 3 ℝ → ℂ) hNf)
    have hv := congrFun (congrArg Subtype.val hs) x
    change projFun p j (u : Matrix.unitaryGroup (Fin 3) ℝ → ℂ) x =
      μ j * ((proj N hdata.lt j (vector (f : Langlands.GeneralLinear 3 ℝ → ℂ) hNf) :
        degreeLE 3 N) : Matrix.unitaryGroup (Fin 3) ℝ → ℂ) x at hv
    rw [proj_restrict_apply hdata.lt j hNf] at hv
    change ((proj T hdata.lt j (vector (g : Langlands.GeneralLinear 3 ℝ → ℂ) hNgT) :
        degreeLE 3 T) : Matrix.unitaryGroup (Fin 3) ℝ → ℂ) x = _
    rw [proj_restrict_apply hdata.lt j hNgT, proj_coe]
    change (2 * (Real.pi : ℂ))⁻¹ *
        blockFourierCoefficient 3 p j (blockFrobMap hdata f) (Unitary.toUnits x) =
      projFun p j (u : Matrix.unitaryGroup (Fin 3) ℝ → ℂ) x
    rw [blockFourierCoefficient_blockFrobMap hdata f x.2, hv]
    ring
  have heq : vg = vu := by
    rw [← sum_proj_apply T hdata.lt vg, ← sum_proj_apply T hdata.lt vu]
    exact Finset.sum_congr rfl fun j _ => hproj j
  exact congrArg Subtype.val heq

/-- Every actual rank-three Frobenius multiplier preserves a chosen compact polynomial degree. -/
theorem frob_mem_degree {N p : ℕ} {ds es : List RealBlock} {ε : ℤ} {τ : ℂ}
    {μ : ℤ → ℂ} (hdata : IsBlockFrobData 3 ds es p ε τ μ) (f : KF 3 ds)
    (hNf : restrictLinear 3 (f : Langlands.GeneralLinear 3 ℝ → ℂ) ∈ degreeLE 3 N) :
    restrictLinear 3 (blockFrobMap hdata f : Langlands.GeneralLinear 3 ℝ → ℂ) ∈ degreeLE 3 N := by
  rw [frob_restrict_eq_spectral hdata f hNf]
  exact (spectralMultiplier (proj N hdata.lt) (Finset.Icc (-(N : ℤ)) N) μ
    (vector (f : Langlands.GeneralLinear 3 ℝ → ℂ) hNf)).2

/-- A canonical tail includes the explicit spectral sign operator. -/
theorem canonical_tail_operator {N p ℓ : ℕ} {ds es : List RealBlock} {ε : ℤ}
    (hℓ : 0 < ℓ) (hε : ε = 0 ∨ ε = 1) (hpar : Even ((ℓ : ℤ) - 1 - ε))
    (hdata : IsBlockFrobData 3 ds es p ε ((-1 : ℂ) ^ ε.natAbs)
      (tailMultiplier ℓ ε ((-1 : ℂ) ^ ε.natAbs)))
    (f : KF 3 ds)
    (hNf : restrictLinear 3 (f : Langlands.GeneralLinear 3 ℝ → ℂ) ∈ degreeLE 3 N)
    (hNg : restrictLinear 3 (blockFrobMap hdata f : Langlands.GeneralLinear 3 ℝ → ℂ) ∈ degreeLE 3 N) :
    vector (blockFrobMap hdata f) hNg =
      signOperator N hdata.lt
        (aeval (-I • gen N hdata.lt) (tailPolynomial ℓ)
          (vector (f : Langlands.GeneralLinear 3 ℝ → ℂ) hNf)) := by
  have hpj : ∀ j, proj N hdata.lt j (vector (blockFrobMap hdata f) hNg) =
      proj N hdata.lt j
        (signOperator N hdata.lt
          (aeval (-I • gen N hdata.lt) (tailPolynomial ℓ)
            (vector (f : Langlands.GeneralLinear 3 ℝ → ℂ) hNf))) := by
    intro j
    rw [signOperator, proj_spectralMultiplier (isModeDecomposition N hdata.lt),
      proj_aeval (isModeDecomposition N hdata.lt)]
    apply Subtype.ext
    funext x
    change ((proj N hdata.lt j (vector (blockFrobMap hdata f) hNg) : degreeLE 3 N) :
        Matrix.unitaryGroup (Fin 3) ℝ → ℂ) x =
      ((Int.sign j : ℤ) : ℂ) *
        ((tailPolynomial ℓ).eval (j : ℂ) *
          ((proj N hdata.lt j (vector (f : Langlands.GeneralLinear 3 ℝ → ℂ) hNf) :
            degreeLE 3 N) : Matrix.unitaryGroup (Fin 3) ℝ → ℂ) x)
    rw [proj_restrict_apply hdata.lt j hNg, proj_restrict_apply hdata.lt j hNf,
      blockFourierCoefficient_blockFrobMap hdata f x.2]
    by_cases he : Even (j - ε)
    · rw [canonical_tail_eq hℓ hε hpar he]
      ring
    · rw [RealBlockJacquet.blockFourierCoefficient_eq_zero_of_not_even
        hdata.lt hdata.par f he (Unitary.toUnits x)]
      ring
  rw [← sum_proj_apply N hdata.lt (vector (blockFrobMap hdata f) hNg),
    ← sum_proj_apply N hdata.lt
      (signOperator N hdata.lt
        (aeval (-I • gen N hdata.lt) (tailPolynomial ℓ)
          (vector (f : Langlands.GeneralLinear 3 ℝ → ℂ) hNf)))]
  exact Finset.sum_congr rfl fun j _ => hpj j

theorem canonical_tail_operator_same_degree {N p ℓ : ℕ} {ds es : List RealBlock} {ε : ℤ}
    (hℓ : 0 < ℓ) (hε : ε = 0 ∨ ε = 1) (hpar : Even ((ℓ : ℤ) - 1 - ε))
    (hdata : IsBlockFrobData 3 ds es p ε ((-1 : ℂ) ^ ε.natAbs)
      (tailMultiplier ℓ ε ((-1 : ℂ) ^ ε.natAbs)))
    (f : KF 3 ds)
    (hNf : restrictLinear 3 (f : Langlands.GeneralLinear 3 ℝ → ℂ) ∈ degreeLE 3 N) :
    vector (blockFrobMap hdata f) (frob_mem_degree hdata f hNf) =
      signOperator N hdata.lt
        (aeval (-I • gen N hdata.lt) (tailPolynomial ℓ)
          (vector (f : Langlands.GeneralLinear 3 ℝ → ℂ) hNf)) :=
  canonical_tail_operator hℓ hε hpar hdata f hNf (frob_mem_degree hdata f hNf)

end Langlands.Archimedean.RealSignedTailPolynomial

namespace Langlands.Archimedean

open Polynomial Complex Langlands.LocalFactor.Archimedean RealBlockFrobeniusMap
  RealBlockMultiplier RealTailMultiplierPolynomial RealStandardFiltration RealKTypeCount
  RealCompactPolynomialFourierRelation RealOrthogonalUncertainty RealSignedTailPolynomial

/-- Canonical tail multipliers include a spectral sign and preserve compact polynomial degree. -/
def RealSignedTailPolynomialStatement : Prop :=
  (∀ (ℓ : ℕ) (ε j : ℤ), 0 < ℓ → (ε = 0 ∨ ε = 1) →
    Even ((ℓ : ℤ) - 1 - ε) → Even (j - ε) →
      tailMultiplier ℓ ε ((-1 : ℂ) ^ ε.natAbs) j =
        ((Int.sign j : ℤ) : ℂ) * (tailPolynomial ℓ).eval (j : ℂ)) ∧
  (∀ (N p ℓ : ℕ) (ds es : List RealBlock) (ε : ℤ),
    0 < ℓ → (ε = 0 ∨ ε = 1) → Even ((ℓ : ℤ) - 1 - ε) →
    ∀ (hdata : IsBlockFrobData 3 ds es p ε ((-1 : ℂ) ^ ε.natAbs)
        (tailMultiplier ℓ ε ((-1 : ℂ) ^ ε.natAbs))) (f : KF 3 ds)
      (hNf : restrictLinear 3 (f : Langlands.GeneralLinear 3 ℝ → ℂ) ∈ degreeLE 3 N),
    ∃ hNg : restrictLinear 3
        (blockFrobMap hdata f : Langlands.GeneralLinear 3 ℝ → ℂ) ∈ degreeLE 3 N,
      vector (blockFrobMap hdata f) hNg =
        signOperator N hdata.lt
          (aeval (-I • gen N hdata.lt) (tailPolynomial ℓ)
            (vector (f : Langlands.GeneralLinear 3 ℝ → ℂ) hNf)))

theorem realSignedTailPolynomial : RealSignedTailPolynomialStatement :=
  ⟨fun _ _ _ hℓ hε hpar hj => canonical_tail_eq hℓ hε hpar hj,
    fun _ _ _ _ _ _ hℓ hε hpar hdata f hNf =>
      ⟨frob_mem_degree hdata f hNf,
        canonical_tail_operator_same_degree hℓ hε hpar hdata f hNf⟩⟩

end Langlands.Archimedean
