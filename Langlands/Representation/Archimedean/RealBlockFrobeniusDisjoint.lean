import Langlands.Representation.Archimedean.RealBlockFrobeniusMap

/-!
# Frobenius maps on disjoint blocks commute

This derived unit computes an arbitrary disjoint block coefficient of a Frobenius
function, then proves commutation for a square of block Frobenius maps with common
source and target. No recurrence or invertibility assumption is needed.
-/

noncomputable section

set_option autoImplicit false

namespace Langlands.Archimedean

open Langlands.LocalFactor.Archimedean

namespace RealBlockFrobeniusDisjoint

open RealBlockRotation RealBlockFourierFinite RealBlockJacquet RealBlockFrobeniusMap

variable {n p q : ℕ} {ds es : List RealBlock} {μ : ℤ → ℂ}

/-- A block coefficient on the compact group depends only on the function there. -/
theorem blockFourierCoefficient_congr_on_compact
    {f g : Langlands.GeneralLinear n ℝ → ℂ}
    (hfg : ∀ k ∈ unitaryCompact ℝ n, f k = g k)
    {k : Langlands.GeneralLinear n ℝ} (hk : k ∈ unitaryCompact ℝ n) (i : ℤ) :
    blockFourierCoefficient n q i f k = blockFourierCoefficient n q i g k := by
  rw [blockFourierCoefficient_eq_coeff, blockFourierCoefficient_eq_coeff]
  congr 1
  funext θ
  exact hfg _ ((unitaryCompact ℝ n).mul_mem (blockRotation_mem_unitaryCompact n q θ) hk)

/-- A coefficient on a disjoint block can be passed through the multiplier sum. -/
theorem blockFourierCoefficient_frobFun_disjoint
    (hd : p + 1 < q ∨ q + 1 < p) {a : Fin n → ℂ} {e : Fin n → Fin 2}
    (hsign : ∀ (j : Fin n)
      (v : kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n)),
      blockJacquet n ds p μ (realStandardRep n ds (signReflection n j) v) =
        (-1) ^ (e j).val * blockJacquet n ds p μ v)
    (f : kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n)) (i : ℤ)
    {k : Langlands.GeneralLinear n ℝ} (hk : k ∈ unitaryCompact ℝ n) :
    blockFourierCoefficient n q i
        (RealJacquetFrobenius.frobFun (realStandardRep n ds) (blockJacquet n ds p μ) a e f) k =
      (2 * (Real.pi : ℂ))⁻¹ *
        ∑ᶠ j : ℤ, μ j * blockFourierCoefficient n p j
          (blockFourierCoefficient n q i f) k := by
  obtain ⟨D, hD⟩ := exists_bound_coe p f
  let I : Finset ℤ := Finset.Icc (-(D : ℤ)) D
  have hout (j : ℤ) (hj : j ∉ I) : (D : ℤ) < |j| := by
    rw [show I = Finset.Icc (-(D : ℤ)) D from rfl, Finset.mem_Icc, ← abs_le] at hj
    exact not_le.mp hj
  have horb : (fun φ : ℝ => RealJacquetFrobenius.frobFun (realStandardRep n ds)
      (blockJacquet n ds p μ) a e f (blockRotation n q φ * k)) =
      fun φ => ∑ j ∈ I, (2 * (Real.pi : ℂ))⁻¹ * μ j *
        blockFourierCoefficient n p j f (blockRotation n q φ * k) := by
    funext φ
    have hm := (unitaryCompact ℝ n).mul_mem (blockRotation_mem_unitaryCompact n q φ) hk
    rw [frobFun_apply_of_mem hsign f hm, finsum_eq_sum_of_support_subset (s := I),
      Finset.mul_sum]
    · simp_rw [mul_assoc]
    · intro j hj
      by_contra hjI
      exact hj (by simp [hD j (hout j hjI) _ hm])
  have hzero (j : ℤ) (hj : j ∉ I) :
      blockFourierCoefficient n p j (blockFourierCoefficient n q i f) k = 0 := by
    rw [blockFourierCoefficient_comm hd (continuous_coe f)]
    calc
      blockFourierCoefficient n q i (blockFourierCoefficient n p j f) k =
          blockFourierCoefficient n q i 0 k :=
        blockFourierCoefficient_congr_on_compact
          (fun g hg => hD j (hout j hj) g hg) hk i
      _ = 0 := blockFourierCoefficient_zero_fun q i k
  rw [blockFourierCoefficient_eq_coeff, horb, coeff_finset_sum I
    (fun j φ => (2 * (Real.pi : ℂ))⁻¹ * μ j *
      blockFourierCoefficient n p j f (blockRotation n q φ * k)) fun j _ =>
    continuous_const.mul ((continuous_blockFourierCoefficient p j (continuous_coe f)).comp
      ((continuous_blockRotation n q).mul continuous_const))]
  simp_rw [coeff_const_mul]
  change (∑ j ∈ I, (2 * (Real.pi : ℂ))⁻¹ * μ j *
      blockFourierCoefficient n q i (blockFourierCoefficient n p j f) k) = _
  simp_rw [← blockFourierCoefficient_comm hd (continuous_coe f)]
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum, finsum_eq_sum_of_support_subset (s := I)]
  · intro j hj
    by_contra hjI
    exact hj (by simp [hzero j hjI])

/-- The disjoint coefficient formula for maps of standard modules. -/
theorem blockFourierCoefficient_blockFrobMap_disjoint
    {ε : ℤ} {σ : ℂ} (h : IsBlockFrobData n ds es p ε σ μ)
    (hd : p + 1 < q ∨ q + 1 < p)
    (f : kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n)) (i : ℤ)
    {k : Langlands.GeneralLinear n ℝ} (hk : k ∈ unitaryCompact ℝ n) :
    blockFourierCoefficient n q i (blockFrobMap h f) k =
      (2 * (Real.pi : ℂ))⁻¹ *
        ∑ᶠ j : ℤ, μ j * blockFourierCoefficient n p j
          (blockFourierCoefficient n q i f) k :=
  blockFourierCoefficient_frobFun_disjoint hd h.hsign f i hk

/-- Two orders of disjoint Frobenius maps agree when their endpoints and
their multiplier at each position agree. -/
theorem blockFrobMap_disjoint_comm
    {fs gs : List RealBlock} {ε η : ℤ} {σ σ' τ τ' : ℂ} {ν : ℤ → ℂ}
    (h₁ : IsBlockFrobData n ds es p ε σ μ)
    (h₂ : IsBlockFrobData n es gs q η τ ν)
    (h₃ : IsBlockFrobData n ds fs q η τ' ν)
    (h₄ : IsBlockFrobData n fs gs p ε σ' μ)
    (hd : p + 1 < q ∨ q + 1 < p)
    (f : kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n)) :
    blockFrobMap h₂ (blockFrobMap h₁ f) = blockFrobMap h₄ (blockFrobMap h₃ f) := by
  refine eq_of_blockFourierCoefficient_eq h₁.lt fun i k hk => ?_
  rw [blockFourierCoefficient_blockFrobMap_disjoint h₂ hd.symm _ i hk,
    blockFourierCoefficient_blockFrobMap h₄ _ hk,
    blockFourierCoefficient_blockFrobMap_disjoint h₃ hd.symm _ i hk]
  have hcoeff (j : ℤ) :
      blockFourierCoefficient n q j
          (blockFourierCoefficient n p i (blockFrobMap h₁ f)) k =
        μ i * blockFourierCoefficient n q j (blockFourierCoefficient n p i f) k := by
    calc
      blockFourierCoefficient n q j
          (blockFourierCoefficient n p i (blockFrobMap h₁ f)) k =
          blockFourierCoefficient n q j (μ i • blockFourierCoefficient n p i f) k :=
        blockFourierCoefficient_congr_on_compact
          (fun g hg => blockFourierCoefficient_blockFrobMap h₁ f hg i) hk j
      _ = _ := blockFourierCoefficient_smul q j (μ i) _ k
  simp_rw [hcoeff]
  have hsum : (∑ᶠ j : ℤ, ν j *
      (μ i * blockFourierCoefficient n q j (blockFourierCoefficient n p i f) k)) =
      μ i * ∑ᶠ j : ℤ, ν j *
        blockFourierCoefficient n q j (blockFourierCoefficient n p i f) k := by
    rw [mul_finsum]
    congr 1
    funext j
    ring
  rw [hsum]
  ring

end RealBlockFrobeniusDisjoint

/-- A square of block Frobenius maps on disjoint blocks commutes if the
two routes have the same endpoints and the same multiplier at each position. -/
def RealDisjointBlockFrobeniusCommutationStatement : Prop :=
  ∀ (n p q : ℕ) (ds es fs gs : List RealBlock) (ε η : ℤ)
    (σ σ' τ τ' : ℂ) (μ ν : ℤ → ℂ)
    (h₁ : RealBlockFrobeniusMap.IsBlockFrobData n ds es p ε σ μ)
    (h₂ : RealBlockFrobeniusMap.IsBlockFrobData n es gs q η τ ν)
    (h₃ : RealBlockFrobeniusMap.IsBlockFrobData n ds fs q η τ' ν)
    (h₄ : RealBlockFrobeniusMap.IsBlockFrobData n fs gs p ε σ' μ),
    (p + 1 < q ∨ q + 1 < p) →
    (RealBlockFrobeniusMap.blockFrobMap h₂).comp (RealBlockFrobeniusMap.blockFrobMap h₁) =
      (RealBlockFrobeniusMap.blockFrobMap h₄).comp (RealBlockFrobeniusMap.blockFrobMap h₃)

theorem realDisjointBlockFrobeniusCommutation :
    RealDisjointBlockFrobeniusCommutationStatement := by
  intro n p q ds es fs gs ε η σ σ' τ τ' μ ν h₁ h₂ h₃ h₄ hd
  apply LinearMap.ext
  intro f
  exact RealBlockFrobeniusDisjoint.blockFrobMap_disjoint_comm h₁ h₂ h₃ h₄ hd f

end Langlands.Archimedean
