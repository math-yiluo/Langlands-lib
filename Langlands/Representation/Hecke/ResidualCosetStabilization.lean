import Langlands.Representation.Hecke.DoubleCosetSandwich
import Mathlib.Order.WellQuasiOrder
import Mathlib.Order.Minimal
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Data.Set.Card

/-! # Finite residual coset stabilization for Hecke multiplication -/

noncomputable section

namespace Langlands.Hecke

universe uΔ uG

/-- An antitone natural-valued function on a finite orthant has finitely many
points below which one can preserve its value. This also covers the empty
coordinate type. -/
theorem exists_finite_antitone_frontier {Δ : Type uΔ} [Finite Δ]
    (f : (Δ → ℕ) → ℕ) (hf : Antitone f) :
    ∃ S : Set (Δ → ℕ), S.Finite ∧
      ∀ n, ∃ m ∈ S, m ≤ n ∧ f m = f n := by
  let P : ((Δ → ℕ) × ℕ) → Prop := fun p => f p.1 = p.2
  have hfin : {p | Minimal P p}.Finite :=
    WellQuasiOrderedLE.finite_of_isAntichain (setOfPred_minimal_antichain P)
  refine ⟨Prod.fst '' {p | Minimal P p}, hfin.image _, ?_⟩
  intro n
  obtain ⟨p, hp, hpmin⟩ :=
    exists_minimal_le_of_wellFoundedLT P (n, f n) rfl
  refine ⟨p.1, ⟨p, hpmin, rfl⟩, hp.1, ?_⟩
  exact le_antisymm (hpmin.1.trans_le hp.2) (hf hp.1)

variable {G : Type uG} [Group G] [TopologicalSpace G]

/-- The actual right `K`-cosets met by `U f`, for a subgroup `U`. -/
def residualCosets (K : OpenSubgroup G) (U : Subgroup G) (f : G) :
    Set (G ⧸ K.toSubgroup) :=
  (fun u : G => QuotientGroup.mk (u * f)) '' (U : Set G)

theorem residualCosets_mono (K : OpenSubgroup G) {U V : Subgroup G}
    (hUV : U ≤ V) (f : G) :
    residualCosets K U f ⊆ residualCosets K V f :=
  Set.image_mono hUV

variable [IsTopologicalGroup G]

/-- Compactness of `K` and openness of its right cosets make these actual
coset sets finite. The residual element need not normalize `K`. -/
theorem finite_residualCosets (K : OpenSubgroup G)
    (hK : IsCompact (K : Set G)) (U : Subgroup G) (hU : U ≤ K.toSubgroup)
    (f : G) : (residualCosets K U f).Finite := by
  let : DiscreteTopology (G ⧸ K.toSubgroup) :=
    QuotientGroup.discreteTopology K.isOpen
  apply Set.Finite.subset
    ((hK.image (QuotientGroup.continuous_mk.comp (continuous_id.mul_const f))).finite_of_discrete)
  exact Set.image_mono hU

/-- An antitone family of subgroups of `K` has a finite frontier preserving
the full right-coset set of every one fixed residual element. -/
theorem exists_finite_residualCoset_frontier {Δ : Type uΔ} [Finite Δ]
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
    (U : (Δ → ℕ) → Subgroup G) (hU : ∀ n, U n ≤ K.toSubgroup)
    (hanti : Antitone U) (f : G) :
    ∃ S : Set (Δ → ℕ), S.Finite ∧
      ∀ n, ∃ m ∈ S, m ≤ n ∧
        residualCosets K (U m) f = residualCosets K (U n) f := by
  have hfin (n) := finite_residualCosets K hK (U n) (hU n) f
  have hmono {m n} (hmn : m ≤ n) :
      residualCosets K (U n) f ⊆ residualCosets K (U m) f :=
    residualCosets_mono K (hanti hmn) f
  obtain ⟨S, hS, hfront⟩ := exists_finite_antitone_frontier
    (fun n => (residualCosets K (U n) f).ncard)
    (fun _ _ hmn => Set.ncard_le_ncard (hmono hmn) (hfin _))
  refine ⟨S, hS, fun n => ?_⟩
  obtain ⟨m, hm, hmn, hcard⟩ := hfront n
  exact ⟨m, hm, hmn,
    (Set.eq_of_subset_of_ncard_le (hmono hmn) hcard.le (hfin m)).symm⟩

end Langlands.Hecke
