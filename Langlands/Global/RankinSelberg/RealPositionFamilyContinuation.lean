import Langlands.Analysis.LandauDirichlet
import Langlands.Analysis.SeveralComplex.CompactParameterEntireContinuation
import Langlands.Global.RankinSelberg.RealPositionPairPolynomial
import Langlands.Global.RankinSelberg.OrdinarySemilocalNormalization

/-! # Joint continuation by the expanded real factors -/

noncomputable section

open Metric Set

set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.RealBlockParameters

open Langlands.LocalFactor Langlands.LocalFactor.Archimedean
open Langlands.Analysis.SeveralComplex
open RealPrincipalSeries (expand)

private theorem differentiable_shiftProduct (l : List ℂ) :
    Differentiable ℂ (shiftProduct l) := by
  induction l with
  | nil => exact differentiable_const 1
  | cons a l ih => exact (differentiable_id.add_const a).div_const _ |>.mul ih

private theorem differentiable_product {k : ℕ} (f : Fin k → ℂ × ℂ → ℂ)
    (hf : ∀ i, Differentiable ℂ (f i)) :
    Differentiable ℂ (fun u => ∏ i, f i u) :=
  fun u => (HasFDerivAt.finsetProd (u := Finset.univ) (g := f)
    fun i _ => (hf i u).hasFDerivAt).differentiableAt

private theorem differentiable_positionPairDenominator {n m : ℕ}
    (sh : Fin n → Shape) (sh' : Fin m → Shape) (p : ℂ → Fin n → ℂ) (q : ℂ → Fin m → ℂ)
    (hp : Differentiable ℂ p) (hq : Differentiable ℂ q) :
    Differentiable ℂ (fun u : ℂ × ℂ =>
      (realPairLFactor (expand (blockList sh (p u.1))) (expand (blockList sh' (q u.1)))).denominator u.2) := by
  obtain ⟨shifts, hpoly⟩ := realPositionPairPolynomial
  simp only [hpoly]
  apply Differentiable.mul _ (differentiable_pairDenominator sh sh' (p ∘ Prod.fst) (q ∘ Prod.fst)
    (hp.comp differentiable_fst) (hq.comp differentiable_fst) Prod.snd differentiable_snd)
  refine differentiable_product (fun i u =>
    ∏ j, shiftProduct (shifts (sh i) (sh' j)) (u.2 + (p u.1 i + q u.1 j))) fun i => ?_
  refine differentiable_product (fun j u =>
    shiftProduct (shifts (sh i) (sh' j)) (u.2 + (p u.1 i + q u.1 j))) fun j => ?_
  exact
    (differentiable_shiftProduct (shifts (sh i) (sh' j))).comp
      (differentiable_snd.add (((differentiable_pi.mp hp i).comp differentiable_fst).add
        ((differentiable_pi.mp hq j).comp differentiable_fst)))

/-- For a jointly holomorphic ordinary integral on a parameter disk times a right
half-plane, entire normalizations by the expanded factors on slices in a disk about
zero extend to a jointly holomorphic normalization on the disk of radius `3 / 2`
times the spectral plane. -/
def RealPositionFamilyContinuationStatement : Prop :=
  ∀ {n m : ℕ} (sh : Fin n → Shape) (sh' : Fin m → Shape) (p : ℂ → Fin n → ℂ) (q : ℂ → Fin m → ℂ),
    Differentiable ℂ p → Differentiable ℂ q →
    ∀ (Z : ℂ × ℂ → ℂ) (σ : ℝ),
      DifferentiableOn ℂ Z (ball 0 3 ×ˢ {s : ℂ | σ < s.re}) →
      (∃ δ : ℝ, 0 < δ ∧ ∀ z ∈ ball 0 δ, Nonempty (OrdinaryIntegralNormalization (fun s => Z (z, s))
        (fun s => ((realPairLFactor (expand (blockList sh (p z)))
          (expand (blockList sh' (q z)))).denominator s)⁻¹))) →
      ∃ F : ℂ × ℂ → ℂ, DifferentiableOn ℂ F (ball 0 (3 / 2) ×ˢ (univ : Set ℂ)) ∧
        ∀ z ∈ ball 0 (3 / 2), ∀ s : ℂ, σ < s.re →
          F (z, s) = (realPairLFactor (expand (blockList sh (p z)))
            (expand (blockList sh' (q z)))).denominator s * Z (z, s)

theorem realPositionFamilyContinuation : RealPositionFamilyContinuationStatement := by
  intro n m sh sh' p q hp hq Z σ hZ ⟨δ, hδ, hN⟩
  let D (z : ℂ) := realPairLFactor (expand (blockList sh (p z))) (expand (blockList sh' (q z)))
  let T (u : ℂ × ℂ) := (D u.1).denominator u.2 * Z u
  have hT : DifferentiableOn ℂ T (ball 0 3 ×ˢ {s : ℂ | σ < s.re}) :=
    (differentiable_positionPairDenominator sh sh' p q hp hq).differentiableOn.mul hZ
  have hSlices : ∃ δ' : ℝ, 0 < δ' ∧
      ∀ z ∈ ball 0 δ', ∃ N : ℂ → ℂ, Differentiable ℂ N ∧
        EqOn N (fun s => T (z, s)) {s : ℂ | σ < s.re} := by
    refine ⟨min δ 3, lt_min hδ (by norm_num), fun z hz => ?_⟩
    have hzδ : z ∈ ball 0 δ := ball_subset_ball (min_le_left _ _) hz
    have hz₃ : z ∈ ball (0 : ℂ) 3 := ball_subset_ball (min_le_right _ _) hz
    obtain ⟨N⟩ := hN z hzδ
    have hEntire : Differentiable ℂ N.value := fun s => (N.analytic s (mem_univ s)).differentiableAt
    obtain ⟨τ, hτ⟩ := N.eq_on_right
    obtain ⟨ρ, hρ⟩ := ArchimedeanRealPairFactor.realLFactor_ne_zero
      (realPairBlocks (expand (blockList sh (p z))) (expand (blockList sh' (q z))))
    refine ⟨N.value, hEntire, Langlands.GeneralDirichlet.eqOn_halfPlane (σ₁ := max τ ρ)
      hEntire.differentiableOn ?_ ?_⟩
    · exact hT.comp ((differentiable_const z).prodMk differentiable_id).differentiableOn
        (fun s hs => ⟨hz₃, hs⟩)
    intro s hs
    have hD : (D z).denominator s ≠ 0 := hρ s ((le_max_right _ _).trans_lt hs)
    change N.value s = (D z).denominator s * Z (z, s)
    rw [hτ s ((le_max_left _ _).trans_lt hs)]
    change N.value s = (D z).denominator s * (N.value s * ((D z).denominator s)⁻¹)
    rw [← mul_assoc, mul_comm ((D z).denominator s) (N.value s), mul_assoc, mul_inv_cancel₀ hD,
      mul_one]
  obtain ⟨F, hF, htrace⟩ := compactParameterJointEntireContinuation T σ hT hSlices
  exact ⟨F, hF, fun z hz s hs => htrace (show (z, s) ∈ _ from ⟨hz, hs⟩)⟩

end Langlands.Global.RankinSelbergGlobal.RealBlockParameters
