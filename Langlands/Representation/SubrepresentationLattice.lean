import Mathlib.RepresentationTheory.Intertwining
import Mathlib.Algebra.Module.Submodule.Map

/-!
# The complete lattice of subrepresentations

Mathlib supplies only the lattice and bounded order. Arbitrary suprema and
infima are the submodule suprema and infima, which are again invariant. The
existing binary operations, top and bottom are reused, so no instance diamond
is introduced.
-/

namespace Langlands.Subrepresentation

universe uA uG uW

variable {A : Type uA} {G : Type uG} {W : Type uW} [Semiring A] [Monoid G]
  [AddCommMonoid W] [Module A W] {ρ : Representation A G W}

/-- The submodule supremum of invariant submodules is invariant. -/
instance instSupSet : SupSet (Subrepresentation ρ) where
  sSup S := ⟨⨆ s ∈ S, s.toSubmodule, by
    intro g v hv
    have h : (⨆ s ∈ S, s.toSubmodule) ≤ (⨆ s ∈ S, s.toSubmodule).comap (ρ g) := by
      refine iSup₂_le fun s hs w hw => ?_
      exact le_iSup₂ (f := fun s (_ : s ∈ S) => s.toSubmodule) s hs
        (s.apply_mem_toSubmodule g hw)
    exact h hv⟩

/-- The submodule infimum of invariant submodules is invariant. -/
instance instInfSet : InfSet (Subrepresentation ρ) where
  sInf S := ⟨⨅ s ∈ S, s.toSubmodule, by
    intro g v hv
    simp only [Submodule.mem_iInf] at hv ⊢
    exact fun s hs => s.apply_mem_toSubmodule g (hv s hs)⟩

theorem toSubmodule_sSup (S : Set (Subrepresentation ρ)) :
    (sSup S).toSubmodule = ⨆ s ∈ S, s.toSubmodule := rfl

theorem toSubmodule_sInf (S : Set (Subrepresentation ρ)) :
    (sInf S).toSubmodule = ⨅ s ∈ S, s.toSubmodule := rfl

instance instCompleteLattice : CompleteLattice (Subrepresentation ρ) :=
  _root_.Subrepresentation.toSubmodule_injective.completeLattice _ .rfl .rfl
    (fun _ _ => rfl) (fun _ _ => rfl) toSubmodule_sSup toSubmodule_sInf rfl rfl

theorem toSubmodule_iSup {ι : Sort*} (f : ι → Subrepresentation ρ) :
    (⨆ i, f i).toSubmodule = ⨆ i, (f i).toSubmodule := by
  rw [iSup, toSubmodule_sSup, iSup_range]

theorem toSubmodule_iInf {ι : Sort*} (f : ι → Subrepresentation ρ) :
    (⨅ i, f i).toSubmodule = ⨅ i, (f i).toSubmodule := by
  rw [iInf, toSubmodule_sInf, iInf_range]

theorem mem_iInf {ι : Sort*} (f : ι → Subrepresentation ρ) (v : W) :
    v ∈ ⨅ i, f i ↔ ∀ i, v ∈ f i := by
  change v ∈ (⨅ i, f i).toSubmodule ↔ _
  rw [toSubmodule_iInf, Submodule.mem_iInf]
  rfl

/-- An intertwiner mapping each member of a family into a fixed subrepresentation
maps their supremum into it. -/
theorem mapsTo_iSup {W' : Type*} [AddCommMonoid W'] [Module A W']
    {σ : Representation A G W'} (φ : ρ.IntertwiningMap σ) {ι : Sort*}
    (S : ι → Subrepresentation ρ) (T : Subrepresentation σ)
    (h : ∀ i, Set.MapsTo φ (S i : Set W) (T : Set W')) :
    Set.MapsTo φ ((⨆ i, S i : Subrepresentation ρ) : Set W) (T : Set W') := by
  intro v hv
  have hle : (⨆ i, S i).toSubmodule ≤ T.toSubmodule.comap φ.toLinearMap := by
    rw [toSubmodule_iSup]
    exact iSup_le fun i _ hw => h i hw
  exact hle hv

end Langlands.Subrepresentation
