import Langlands.AllFieldBZ.Representation.Classification.SupercuspidalTwist
import Langlands.AllFieldBZ.Representation.Derivative.Homogeneity
import Langlands.AllFieldBZ.Representation.Induction.BlockFactors
import Langlands.Representation.Derivative.OrderedCuspidalProductNondegeneracyStatement

/-!
# All-field port of `Langlands.Representation.Derivative.OrderedCuspidalProductNondegeneracyStatement`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.Derivative.OrderedCuspidalProductNondegeneracyStatement` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
namespace Langlands.AllFieldBZ.Derivative
open Langlands.Derivative hiding HasNonzeroDerivative IsHomogeneous OrderedCuspidalProductNoDegenerateSubmodules generalLinearDerivative generalLinearDerivativePositive generalLinearDerivativePositive_eq generalLinearDerivativePositive_obj generalLinearDerivative_of_pos generalLinearDerivative_succ generalLinearDerivative_succ_obj generalLinearDerivative_top_succ generalLinearDerivative_zero generalLinearRankCast generalLinearRankCast_refl generalLinearRankCast_symm_comp generalLinearRankCast_trans generalLinearRestriction generalLinearRestriction_map_apply generalLinearRestriction_map_toLinearMap hasNonzeroDerivative_iff isHomogeneous_of_subsingleton le_level_of_hasNonzeroDerivative level level_eq_iff level_eq_zero_iff level_eq_zero_of_subsingleton level_le mirabolicDerivative mirabolicDerivativeOfOrder mirabolicDerivativeOfOrder_eq mirabolicDerivativeOfOrder_obj mirabolicDerivativeOfOrder_obj_subsingleton mirabolicDerivativeOfOrder_one mirabolicDerivativeOfOrder_top mirabolicDerivative_eq mirabolicDerivative_obj_subsingleton mirabolicDerivative_succ mirabolicDerivative_zero mirabolicRankCast mirabolicRankCast_obj_subsingleton mirabolicRankCast_refl phiMinusIterate phiMinusIterate_obj_subsingleton phiMinusIterate_succ phiMinusIterate_zero
open Langlands.GeneralLinear
open Langlands.HarmonicAnalysis
universe uF uV

variable (F : LocalFieldPackage.{uF}) (T : F.TopologicalData)

/-- BZ77 Theorem 4.11: for an ordered family of irreducible supercuspidal blocks
with `ρ_j ≇ ν ρ_i` whenever `i < j`, every nonzero actual subrepresentation of
the restriction of `ρ_1 × ⋯ × ρ_r` to `P_(N+1)` has nonzero derivative of the
top order `N + 1`. -/
def OrderedCuspidalProductNoDegenerateSubmodules : Prop :=
  letI := T.topology
  ∀ (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (N : ℕ)
    (B : BlockShape (N + 1))
    (A : ∀ i : Fin B.length,
      SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := B.size i)),
    (∀ i j : Fin B.length, i < j →
      (⟨B.size j, (A j).isoClass⟩ :
          Σ d : ℕ, SupercuspidalClass.{uV, uF} (F := F.Carrier) (n := d)) ≠
        ⟨B.size i, T.supercuspidalClassRealPowerTwist (B.size i) 1 (A i).isoClass⟩) →
    ∀ U : Subrepresentation
        ((generalLinearRestriction.{uF, max uF uV} T N).obj
          ((T.normalizedProductInductionFunctor.{uF, uV} B).obj
            (fun i => (A i).obj))).representation,
      U ≠ ⊥ →
        Nontrivial
          ((mirabolicDerivativeOfOrder.{uF, max uF uV} T ψ N (N + 1)
              ⟨Nat.zero_lt_succ N, le_rfl⟩).obj
            (SmoothRep.subrepresentation
              ((generalLinearRestriction.{uF, max uF uV} T N).obj
                ((T.normalizedProductInductionFunctor.{uF, uV} B).obj
                  (fun i => (A i).obj))) U))

end Langlands.AllFieldBZ.Derivative
