import Langlands.GroupTheory.CocycleCohomology
import Mathlib.Basic.Real.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Basic
import Mathlib.SetTheory.Cardinal.Finite

/-! # Cyclic Herbrand quotients of two full invariant lattices in one real representation -/

namespace Langlands.GroupTheory

open NormalizedTwoCocycle

universe v w

/-- Let a finite cyclic group `G` act by real linear automorphisms `ρ` on a
finite-dimensional real vector space `V`. Let `M` and `N` be ordinary
lifted-integer representations of `G`, embedded injectively and equivariantly
into `V`, each with image the `ℤ`-span of an `ℝ`-basis of `V`. If `H¹(G,M)` and
`H²(G,M)` are finite, then `H¹(G,N)` and `H²(G,N)` are finite and
`|H²(G,M)| * |H¹(G,N)| = |H²(G,N)| * |H¹(G,M)|`.
This states Milne VII, Lemma 3.5. The declaration states the result; it does not
prove it. -/
def CyclicLatticeHerbrandInvariance : Prop :=
  ∀ (G : Type v) [Group G] [Finite G] [IsCyclic G]
    (V : Type w) [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (ρ : G →* (V ≃ₗ[ℝ] V))
    (M N : Rep.{v} CoefficientScalars.{v} G) (ιM : M →+ V) (ιN : N →+ V),
    Function.Injective ιM → Function.Injective ιN →
    (∀ (g : G) (x : M), ιM (M.ρ g x) = ρ g (ιM x)) →
    (∀ (g : G) (x : N), ιN (N.ρ g x) = ρ g (ιN x)) →
    (∃ (ι : Type w) (b : Module.Basis ι ℝ V),
      Set.range ιM = (Submodule.span ℤ (Set.range b) : Set V)) →
    (∃ (ι : Type w) (b : Module.Basis ι ℝ V),
      Set.range ιN = (Submodule.span ℤ (Set.range b) : Set V)) →
    Finite (groupCohomology M 1 : Type v) → Finite (groupCohomology M 2 : Type v) →
      Finite (groupCohomology N 1 : Type v) ∧ Finite (groupCohomology N 2 : Type v) ∧
        Nat.card (groupCohomology M 2 : Type v) * Nat.card (groupCohomology N 1 : Type v) =
          Nat.card (groupCohomology N 2 : Type v) * Nat.card (groupCohomology M 1 : Type v)

end Langlands.GroupTheory
