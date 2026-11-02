import Langlands.Representation.Classification.SupercuspidalTwist
import Langlands.Representation.Induction.BlockFactors
import Langlands.Representation.Derivative.Homogeneity

/-!
# Ordered cuspidal products have no degenerate mirabolic submodules

Bernstein–Zelevinsky 1977, Theorem 4.11: if irreducible cuspidal blocks
`ρ_1, …, ρ_r` satisfy `ρ_j ≇ ν ρ_i` whenever `i < j`, then every nonzero
`P_n`-submodule of the normalized product `ρ_1 × ⋯ × ρ_r` has nonzero top
derivative. Only the sufficient direction is stated; no proof is asserted.
-/

namespace Langlands.Derivative

open GeneralLinear HarmonicAnalysis

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

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

end Langlands.Derivative
