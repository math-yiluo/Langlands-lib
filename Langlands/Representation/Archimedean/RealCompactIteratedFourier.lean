import Langlands.Representation.Archimedean.RealInducedTorusCore
import Langlands.Representation.Archimedean.RealInductionStagesSlice

/-! # Iterated Fourier coefficients determine the compact restriction -/

noncomputable section

open scoped Matrix.Norms.Operator

set_option autoImplicit false

namespace Langlands.Archimedean

open Langlands.LocalFactor.Archimedean
open RealInducedBlockBound RealInducedTorusCore RealBlockFourierFinite InductionStages

private abbrev G (n : ℕ) := Langlands.GeneralLinear n ℝ

/-- Iterated coefficients for every list of modes determine a continuous
compact-finite function on the compact group. -/
def RealCompactIteratedFourierStatement : Prop :=
  ∀ {n : ℕ} (L : List (Slot n)) {F H : Langlands.GeneralLinear n ℝ → ℂ},
    Continuous F → Continuous H → IsKFin F → IsKFin H →
    (∀ J : List ℤ, J.length = L.length →
      Set.EqOn (coeffs (withModes L J) F) (coeffs (withModes L J) H) (unitaryCompact ℝ n)) →
    Set.EqOn F H (unitaryCompact ℝ n)

theorem realCompactIteratedFourier : RealCompactIteratedFourierStatement := by
  intro n L F H hF hH hFK hHK hFourier
  induction L with
  | nil => exact hFourier [] rfl
  | cons t L ih =>
    apply ih
    intro J hJ k hk
    let L' := withModes L J
    change coeffs L' F k = coeffs L' H k
    rw [eq_finsum_blockFourierCoefficient t.hp (continuous_coeffs hF L')
      (isKFin_coeffs hF hFK L') hk,
      eq_finsum_blockFourierCoefficient t.hp (continuous_coeffs hH L')
        (isKFin_coeffs hH hHK L') hk]
    congr 2
    funext j
    have he := hFourier (j :: J) (by simpa only [List.length_cons] using congrArg Nat.succ hJ) hk
    simpa only [withModes, coeffs, setMode, L'] using he

private theorem coeffs_kRep {n : ℕ} {ds : List RealBlock} (L : List (Slot n))
    (f : KFin n ds) (k₀ : unitaryCompact ℝ n) (g : G n) :
    coeffs L (kRep n ds k₀ f).val g = coeffs L f.val (g * k₀.val) := by
  have h : (kRep n ds k₀ f).val = fun x => f.val (x * k₀.val) :=
    funext (kRep_apply_coe n ds k₀ f)
  rw [h, coeffs_mul_right]

/-- A linear map whose iterated Fourier coefficients are fixed multiples of
the input coefficients is equivariant for compact right translation. -/
theorem compactEquivariant_of_iteratedFourierMultiplier
    {n : ℕ} {ds es : List RealBlock} (L : List (Slot n)) (W : List ℤ → ℂ)
    (T : KFin n ds →ₗ[ℂ] KFin n es)
    (hT : ∀ J : List ℤ, J.length = L.length → ∀ f k, k ∈ unitaryCompact ℝ n →
      coeffs (withModes L J) (T f).val k = W J * coeffs (withModes L J) f.val k) :
    ∀ k f, T (kRep n ds k f) = kRep n es k (T f) := by
  intro k₀ f
  let F := T (kRep n ds k₀ f)
  let H := kRep n es k₀ (T f)
  change F = H
  apply Subtype.ext
  apply eq_of_eqOn_unitaryCompact_of_mem_principalSeries F.2.1.1 H.2.1.1
  apply realCompactIteratedFourier L
    (RealPrincipalSeriesDuality.continuous_of_mem_kFiniteFunctions F.2)
    (RealPrincipalSeriesDuality.continuous_of_mem_kFiniteFunctions H.2) F.2.2 H.2.2
  intro J hJ g hg
  change coeffs (withModes L J) (T (kRep n ds k₀ f)).val g =
    coeffs (withModes L J) (kRep n es k₀ (T f)).val g
  rw [hT J hJ _ _ hg, coeffs_kRep, coeffs_kRep, hT J hJ _ _ (mul_mem hg k₀.2)]

end Langlands.Archimedean
