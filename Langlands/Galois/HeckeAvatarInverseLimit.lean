import Langlands.Galois.FiniteHeckeAvatarLift
import Langlands.Global.IntegralFiniteAdeles
import Mathlib.Topology.Algebra.Ring.Compact

/-! # Integral coefficient quotients and the inverse-limit avatar -/

noncomputable section

universe uK uL

namespace Langlands.GaloisRepresentation

open Langlands.Global
open Topology

variable {L : Type uL} [Field L] [NumberField L]

private abbrev congruenceIdeal (lam : FinitePlace L) (n : ℕ) :
    Ideal (lam.adicCompletionIntegers L) :=
  IsLocalRing.maximalIdeal (lam.adicCompletionIntegers L) ^ (n + 1)

/-- Units of the actual quotient of the completed integer ring by
`𝔪^(n+1)`, equipped with the discrete topology. -/
def CompletionUnitQuotient (lam : FinitePlace L) (n : ℕ) :=
  ((lam.adicCompletionIntegers L) ⧸ congruenceIdeal lam n)ˣ

instance (lam : FinitePlace L) (n : ℕ) : CommGroup (CompletionUnitQuotient lam n) :=
  inferInstanceAs (CommGroup ((lam.adicCompletionIntegers L) ⧸ congruenceIdeal lam n)ˣ)

instance (lam : FinitePlace L) (n : ℕ) : TopologicalSpace (CompletionUnitQuotient lam n) := ⊥

instance (lam : FinitePlace L) (n : ℕ) : DiscreteTopology (CompletionUnitQuotient lam n) := ⟨rfl⟩

private theorem isOpen_congruenceIdeal (lam : FinitePlace L) (n : ℕ) :
    IsOpen (congruenceIdeal lam n : Set (lam.adicCompletionIntegers L)) := by
  let := isCompact_iff_compactSpace.mp (isCompact_adicCompletionIntegers L lam)
  exact IsLocalRing.isOpen_maximalIdeal_pow _ _

instance (lam : FinitePlace L) (n : ℕ) : Finite (CompletionUnitQuotient lam n) := by
  let := isCompact_iff_compactSpace.mp (isCompact_adicCompletionIntegers L lam)
  let : Finite ((lam.adicCompletionIntegers L) ⧸ congruenceIdeal lam n) :=
    IsLocalRing.isOpen_iff_finite_quotient.mp (isOpen_congruenceIdeal lam n)
  exact Finite.of_injective Units.val Units.val_injective

/-- Reduction of actual completed integer units modulo `𝔪^(n+1)`. -/
def completionUnitReduction (lam : FinitePlace L) (n : ℕ) :
    (lam.adicCompletionIntegers L)ˣ →ₜ* CompletionUnitQuotient lam n := by
  let r : (lam.adicCompletionIntegers L)ˣ →* CompletionUnitQuotient lam n :=
    Units.map (Ideal.Quotient.mk (congruenceIdeal lam n)).toMonoidHom
  refine ⟨r, continuous_of_continuousAt_one r ?_⟩
  rw [ContinuousAt, map_one, nhds_discrete (CompletionUnitQuotient lam n), Filter.tendsto_pure]
  have hopen : IsOpen {u : (lam.adicCompletionIntegers L)ˣ |
      (u : lam.adicCompletionIntegers L) - 1 ∈ congruenceIdeal lam n} :=
    (isOpen_congruenceIdeal lam n).preimage (Units.continuous_val.sub continuous_const)
  refine Filter.mem_of_superset (hopen.mem_nhds ?_) ?_
  · simp
  · intro u hu
    change r u = 1
    apply Units.ext
    change Ideal.Quotient.mk (congruenceIdeal lam n) (u : lam.adicCompletionIntegers L) = 1
    rw [← map_one (Ideal.Quotient.mk (congruenceIdeal lam n)), Ideal.Quotient.eq]
    exact hu

/-- The transition between the actual quotients, from the higher power to
the lower power. -/
def completionUnitTransition (lam : FinitePlace L) {n m : ℕ} (h : n ≤ m) :
    CompletionUnitQuotient lam m →ₜ* CompletionUnitQuotient lam n where
  toMonoidHom := Units.map (Ideal.Quotient.factor
    (Ideal.pow_le_pow_right (I := IsLocalRing.maximalIdeal (lam.adicCompletionIntegers L))
      (Nat.succ_le_succ h))).toMonoidHom
  continuous_toFun := continuous_of_discreteTopology

@[simp]
theorem completionUnitTransition_reduction (lam : FinitePlace L) {n m : ℕ} (h : n ≤ m)
    (u : (lam.adicCompletionIntegers L)ˣ) :
    completionUnitTransition lam h (completionUnitReduction lam m u) =
      completionUnitReduction lam n u := by
  apply Units.ext
  rfl

/-- Unique geometric lifts at all finite levels are coherent under the
actual quotient transitions and give a continuous integral avatar with the
same good-place comparison. -/
def HeckeAvatarInverseLimitStatement : Prop :=
  ∀ (K : Type uK) [Field K] [NumberField K] (L : Type uL) [Field L] [NumberField L]
    (lam : FinitePlace L) (S : Finset (FinitePlace K))
    (η : IdeleClasses K →ₜ* (lam.adicCompletionIntegers L)ˣ),
    (∀ n : ℕ, ∃! r : Field.absoluteGaloisGroup K →ₜ* CompletionUnitQuotient lam n,
      MatchesGeometricArtinOutside S ((completionUnitReduction lam n).comp η) r) →
    ∃ (r : ∀ n : ℕ, Field.absoluteGaloisGroup K →ₜ* CompletionUnitQuotient lam n)
      (ψ : Field.absoluteGaloisGroup K →ₜ* (lam.adicCompletionIntegers L)ˣ),
      (∀ n, MatchesGeometricArtinOutside S ((completionUnitReduction lam n).comp η) (r n)) ∧
      (∀ (n m : ℕ) (h : n ≤ m), (completionUnitTransition lam h).comp (r m) = r n) ∧
      (∀ n, (completionUnitReduction lam n).comp ψ = r n) ∧
      MatchesGeometricArtinOutside S η ψ

end Langlands.GaloisRepresentation
