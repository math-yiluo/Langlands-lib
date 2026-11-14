import Langlands.AllFieldBZ.Representation.Derivative.MirabolicProductMinusBoundary
import Langlands.AllFieldBZ.Representation.Derivative.MixedProductDerivativeStatement
import Langlands.Representation.Derivative.LeftMixedProductVanishing

/-!
# All-field port of `Langlands.Representation.Derivative.LeftMixedProductVanishing`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.Derivative.LeftMixedProductVanishing` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
noncomputable section
open CategoryTheory
namespace Langlands.AllFieldBZ.Derivative
open Langlands.Derivative hiding HasNonzeroDerivative IsHomogeneous LeftMixedProductDerivative LeftMixedProductDerivativeIso LeftMixedProductDerivativeVanishing MirabolicProductMinusCompatibilityStatement RightMixedProductPhiMinusDetection generalLinearDerivative generalLinearDerivativePositive generalLinearDerivativePositive_eq generalLinearDerivativePositive_obj generalLinearDerivative_of_pos generalLinearDerivative_succ generalLinearDerivative_succ_obj generalLinearDerivative_top_succ generalLinearDerivative_zero generalLinearRankCast generalLinearRankCast_refl generalLinearRankCast_symm_comp generalLinearRankCast_trans generalLinearRestriction generalLinearRestriction_map_apply generalLinearRestriction_map_toLinearMap hasNonzeroDerivative_iff isHomogeneous_of_subsingleton le_level_of_hasNonzeroDerivative level level_eq_iff level_eq_zero_iff level_eq_zero_of_subsingleton level_le mirabolicDerivative mirabolicDerivativeOfOrder mirabolicDerivativeOfOrder_eq mirabolicDerivativeOfOrder_obj mirabolicDerivativeOfOrder_obj_subsingleton mirabolicDerivativeOfOrder_one mirabolicDerivativeOfOrder_top mirabolicDerivative_eq mirabolicDerivative_obj_subsingleton mirabolicDerivative_succ mirabolicDerivative_zero mirabolicRankCast mirabolicRankCast_obj_subsingleton mirabolicRankCast_refl phiMinusIterate phiMinusIterate_obj_subsingleton phiMinusIterate_succ phiMinusIterate_zero
open Langlands.GeneralLinear
open Langlands.HarmonicAnalysis
universe uF uV

namespace LeftMixedProductVanishing
open Langlands.Derivative.LeftMixedProductVanishing hiding leftMixedProductDerivativeVanishing_of_leftPhiCompatibility mirabolicDerivative_leftMixedProduct_subsingleton mirabolicRankCast_obj_trans phiMinus_obj_rankCast
variable {F : LocalFieldPackage.{uF}}

section Maps
variable {G : Type*} [Group G] [TopologicalSpace G]

end Maps
/-- `Φ⁻` after a successor-rank transport is the transport after `Φ⁻`. -/
theorem phiMinus_obj_rankCast (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) {a b : ℕ}
    (e : a = b) (h : a + 1 = b + 1) :
    letI := T.topology
    ∀ X : SmoothRep.{0, uF, uV} ℂ (mirabolic (a + 1) F.Carrier),
      (Mirabolic.phiMinus T ψ b).obj ((mirabolicRankCast T h).obj X) =
        (mirabolicRankCast T e).obj ((Mirabolic.phiMinus T ψ a).obj X) := by
  subst e
  intros
  rfl

/-- Two successive transports are one transport, on objects. -/
theorem mirabolicRankCast_obj_trans (T : F.TopologicalData) {a b c : ℕ}
    (h : a = b) (h' : b = c) (h'' : a = c) :
    letI := T.topology
    ∀ X : SmoothRep.{0, uF, uV} ℂ (mirabolic a F.Carrier),
      (mirabolicRankCast T h').obj ((mirabolicRankCast T h).obj X) =
        (mirabolicRankCast T h'').obj X := by
  subst h h'
  intros
  rfl

/-- The core induction on the mirabolic rank `r`: after at least `r + 1` actual
`Φ⁻` steps, the derivative of `ρ × τ` (GL rank `k + 1`, `τ` on `P_(r+1)`) has zero
carrier, for every source transport `h`. -/
theorem mirabolicDerivative_leftMixedProduct_subsingleton (T : F.TopologicalData)
    (hPhi : MirabolicProductMinus.LeftPhiCompatibility.{uF, uV} F T)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (k : ℕ) :
    letI := T.topology
    ∀ (r : ℕ) (A : SmoothRep.{0, uF, uV} ℂ (GeneralLinear (k + 1) F.Carrier))
      (B : SmoothRep.{0, uF, uV} ℂ (mirabolic r F.Carrier)) (n j : ℕ)
      (h : k + 1 + r = n + j), r + 1 ≤ j →
      Subsingleton ((mirabolicDerivative T ψ n j).obj
        ((mirabolicRankCast T h).obj ((T.leftMixedProductFunctor.{uF, uV} (k + 1) r).obj (A, B)))) := by
  let _ := T.topology
  intro r
  induction r with
  | zero =>
    intro A B n j h hj
    obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    have e : k + 0 = n + j := by omega
    have hb : Subsingleton ((MirabolicProductMinus.leftPhiProduct T ψ k 0).obj (A, B)) :=
      MirabolicProductMinus.leftPhiBoundary T ψ k (A, B)
    change Subsingleton ((mirabolicDerivative T ψ n j).obj ((Mirabolic.phiMinus T ψ (n + j)).obj
      ((mirabolicRankCast T h).obj ((T.leftMixedProductFunctor.{uF, uV} (k + 1) 0).obj (A, B)))))
    rw [← mirabolicRankCast_obj_trans T (show k + 1 + 0 = k + 0 + 1 by omega)
      (show k + 0 + 1 = n + j + 1 by omega) h, phiMinus_obj_rankCast T ψ e]
    exact mirabolicDerivative_obj_subsingleton T ψ n j _
      (mirabolicRankCast_obj_subsingleton T e _ hb)
  | succ r ih =>
    intro A B n j h hj
    obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    have e : k + (r + 1) = n + j := by omega
    obtain ⟨φ⟩ := hPhi ψ k r
    change Subsingleton ((mirabolicDerivative T ψ n j).obj ((Mirabolic.phiMinus T ψ (n + j)).obj
      ((mirabolicRankCast T h).obj
        ((T.leftMixedProductFunctor.{uF, uV} (k + 1) (r + 1)).obj (A, B)))))
    rw [← mirabolicRankCast_obj_trans T (show k + 1 + (r + 1) = k + (r + 1) + 1 by omega)
      (show k + (r + 1) + 1 = n + j + 1 by omega) h, phiMinus_obj_rankCast T ψ e]
    have h' : k + 1 + r = n + j := by omega
    have hexp := ih A ((Mirabolic.phiMinus T ψ r).obj B) n j h' (by omega)
    rw [← mirabolicRankCast_obj_trans T (show k + 1 + r = k + r + 1 by omega) e h'] at hexp
    exact subsingleton_of_iso
      ((mirabolicDerivative T ψ n j).mapIso ((mirabolicRankCast T e).mapIso (φ.app (A, B))))
      hexp

/-- BZ77 4.14(a), vanishing half: given `LeftPhiCompatibility`, every order-`i`
derivative of `A × B` with `r + 1 < i ≤ k + r + 1` has zero carrier. -/
theorem leftMixedProductDerivativeVanishing_of_leftPhiCompatibility
    (T : F.TopologicalData)
    (hPhi : MirabolicProductMinus.LeftPhiCompatibility.{uF, uV} F T) :
    LeftMixedProductDerivativeVanishing.{uF, uV} F T := by
  let _ := T.topology
  intro ψ k r i hi hri A B
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  exact mirabolicDerivative_leftMixedProduct_subsingleton T hPhi ψ k r A B _ _
    (mirabolic_rank_eq_of_order hi) (by omega)

end LeftMixedProductVanishing
end Langlands.AllFieldBZ.Derivative
