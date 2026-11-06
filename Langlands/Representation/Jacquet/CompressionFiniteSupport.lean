import Langlands.Representation.Jacquet.StableCompressionPower
import Langlands.Representation.Jacquet.StableCompressionPropagation

/-! # Compression stability for sums with finite fixed-vector support

Pointwise eventual stability suffices on a sum if only finitely many summands
have nonzero fixed vectors at the compact open subgroup. Finiteness is explicit.
-/

noncomputable section

namespace Langlands.Jacquet

open Langlands.LinearAlgebra.StableEndomorphism

universe uG uI uV

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {κ : Type uI} {V : κ → Type uV}
  [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]

/-- Only finitely many actual fixed-vector component modules are nonzero. -/
def FiniteFixedVectorSupport
    (ρ : ∀ i, Representation ℂ G (V i)) (H : Subgroup G) : Prop :=
  Set.Finite {i | Nontrivial (fixedVectors (ρ i) H)}

/-- A finite set of visible summands admits a common positive stable exponent;
the other fixed-vector components are zero and impose no bound. -/
theorem compressedAction_eventuallyStable_directSum_of_finite_support
    (ρ : ∀ i, Representation ℂ G (V i)) (hρ : ∀ i, IsSmooth (ρ i))
    (hsum : IsSmooth (Representation.directSum ρ))
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (g : G)
    (hfinite : FiniteFixedVectorSupport ρ K.toSubgroup)
    (hpoint : ∀ i, EventuallyStable (compressedAction (ρ i) (hρ i) K hK g)) :
    EventuallyStable (compressedAction (Representation.directSum ρ) hsum K hK g) := by
  classical
  choose b hb using fun i =>
    (compactCompression_eventuallyStable_iff_exists_stationaryFrom
      (ρ i) (hρ i) K hK g).mp (hpoint i)
  change Set.Finite {i | Nontrivial (fixedVectors (ρ i) K.toSubgroup)} at hfinite
  let S := hfinite.toFinset
  let B := max 1 (S.sup b)
  refine ⟨B, by dsimp [B]; omega, ?_⟩
  apply (compressedAction_stablePower_directSum_iff ρ hρ hsum K hK g B).mpr
  intro i
  by_cases hi : Nontrivial (fixedVectors (ρ i) K.toSubgroup)
  · have hiS : i ∈ S := hfinite.mem_toFinset.mpr hi
    have hbi : b i ≤ B :=
      (Finset.le_sup (f := b) hiS).trans (Nat.le_max_right _ _)
    exact compactCompressionStablePower_of_stationaryFrom (ρ i) (hρ i) K hK g
      ((hb i).mono hbi)
  · have : Subsingleton (fixedVectors (ρ i) K.toSubgroup) :=
      not_nontrivial_iff_subsingleton.mp hi
    constructor <;> exact Subsingleton.elim _ _

end Langlands.Jacquet
