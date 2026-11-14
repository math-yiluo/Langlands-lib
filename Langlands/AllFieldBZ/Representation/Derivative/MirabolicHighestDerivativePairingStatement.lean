import Langlands.AllFieldBZ.Representation.Derivative.Homogeneity
import Langlands.Representation.Derivative.MirabolicHighestDerivativePairingStatement

/-!
# All-field port of `Langlands.Representation.Derivative.MirabolicHighestDerivativePairingStatement`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.Derivative.MirabolicHighestDerivativePairingStatement` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
namespace Langlands.AllFieldBZ.Derivative
open Langlands.Derivative hiding HasNonzeroDerivative IsHomogeneous MirabolicHighestDerivativePairingStatement generalLinearDerivative generalLinearDerivativePositive generalLinearDerivativePositive_eq generalLinearDerivativePositive_obj generalLinearDerivative_of_pos generalLinearDerivative_succ generalLinearDerivative_succ_obj generalLinearDerivative_top_succ generalLinearDerivative_zero generalLinearRankCast generalLinearRankCast_refl generalLinearRankCast_symm_comp generalLinearRankCast_trans generalLinearRestriction generalLinearRestriction_map_apply generalLinearRestriction_map_toLinearMap hasNonzeroDerivative_iff isHomogeneous_of_subsingleton le_level_of_hasNonzeroDerivative level level_eq_iff level_eq_zero_iff level_eq_zero_of_subsingleton level_le mirabolicDerivative mirabolicDerivativeOfOrder mirabolicDerivativeOfOrder_eq mirabolicDerivativeOfOrder_obj mirabolicDerivativeOfOrder_obj_subsingleton mirabolicDerivativeOfOrder_one mirabolicDerivativeOfOrder_top mirabolicDerivative_eq mirabolicDerivative_obj_subsingleton mirabolicDerivative_succ mirabolicDerivative_zero mirabolicRankCast mirabolicRankCast_obj_subsingleton mirabolicRankCast_refl phiMinusIterate phiMinusIterate_obj_subsingleton phiMinusIterate_succ phiMinusIterate_zero
open Langlands.GeneralLinear
open Langlands.HarmonicAnalysis
open scoped NNReal
/-- Bernstein–Zelevinsky (1977), Proposition 3.8, for the actual order-`k` derivatives
`mirabolicDerivativeOfOrder T ψ N k hk` of `P_(N+1)`-representations `A` and `B` in
independent carrier universes. The source `Δ_P`-pairing is a form with simultaneous
covariance `g ↦ |det g|`; the conclusion is an invariant (covariance one) pairing. -/
def MirabolicHighestDerivativePairingStatement.{uF, uV, uW} (F : LocalFieldPackage.{uF}) (T : F.TopologicalData) : Prop :=
  letI := T.topology
  ∀ (ψ : UnitaryAdditiveCharacter F.Carrier) (N : ℕ)
    (A : SmoothRep.{0, uF, uV} ℂ (mirabolic N F.Carrier))
    (B : SmoothRep.{0, uF, uW} ℂ (mirabolic N F.Carrier))
    (k : ℕ) (hk : 0 < k ∧ k ≤ N + 1),
    Nontrivial ((mirabolicDerivativeOfOrder.{uF, uV} T ψ N k hk).obj A) →
    (∀ (j : ℕ) (hj : 0 < j ∧ j ≤ N + 1), k < j →
      Subsingleton ((mirabolicDerivativeOfOrder.{uF, uV} T ψ N j hj).obj A)) →
    ∀ β : InvariantBilinear.forms A.representation B.representation
        (fun g => ((((T.determinantNorm (N + 1)) g.val : ℝ≥0) : ℝ) : ℂ)),
      (∀ v : A, (∀ w : B, β.val v w = 0) → v = 0) →
      ∃ γ : InvariantBilinear.forms
          ((mirabolicDerivativeOfOrder.{uF, uV} T ψ N k hk).obj A).representation
          ((mirabolicDerivativeOfOrder.{uF, uW} T ψ N k hk).obj B).representation
          (fun _ => (1 : ℂ)),
        ∀ v : (mirabolicDerivativeOfOrder.{uF, uV} T ψ N k hk).obj A,
          (∀ w : (mirabolicDerivativeOfOrder.{uF, uW} T ψ N k hk).obj B,
            γ.val v w = 0) → v = 0

end Langlands.AllFieldBZ.Derivative
