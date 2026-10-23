import Langlands.Representation.Exponents.Central
import Mathlib.Data.ENat.Basic

/-!
# Uniform nilpotence index of a generalized central-character space

The index is the least exponent that works on the whole generalized space,
or infinity when no such common exponent exists.
-/

noncomputable section

namespace Langlands

universe uR uG uV uW

variable {R : Type uR} [CommRing R] {G : Type uG} [Group G]
  {V : Type uV} [AddCommGroup V] [Module R V]
  {W : Type uW} [AddCommGroup W] [Module R W]

/-- A single power that annihilates every vector in the generalized character
space, uniformly over all central elements. -/
def IsCentralNilpotenceBound (ρ : Representation R G V)
    (χ : Subgroup.center G →* Rˣ) (n : ℕ) : Prop :=
  generalizedCentralCharacterSpace ρ χ ≤ centralCharacterSpace ρ χ n

/-- The least common nilpotence exponent of the generalized central-character
space, with infinity if there is no finite bound. The zero space has index zero. -/
def centralCharacterNilpotenceIndex (ρ : Representation R G V)
    (χ : Subgroup.center G →* Rˣ) : ℕ∞ := by
  classical
  exact if h : ∃ n, IsCentralNilpotenceBound ρ χ n then (Nat.find h : ℕ∞) else ⊤

theorem isCentralNilpotenceBound_mono (ρ : Representation R G V)
    (χ : Subgroup.center G →* Rˣ) {m n : ℕ} (hmn : m ≤ n)
    (hm : IsCentralNilpotenceBound ρ χ m) : IsCentralNilpotenceBound ρ χ n :=
  hm.trans (centralCharacterSpace_mono ρ χ hmn)

/-- The index is at most n exactly when n annihilates the whole component. -/
theorem centralCharacterNilpotenceIndex_le_iff (ρ : Representation R G V)
    (χ : Subgroup.center G →* Rˣ) (n : ℕ) :
    centralCharacterNilpotenceIndex ρ χ ≤ (n : ℕ∞) ↔
      IsCentralNilpotenceBound ρ χ n := by
  classical
  by_cases h : ∃ k, IsCentralNilpotenceBound ρ χ k
  · rw [centralCharacterNilpotenceIndex, dite_eq_left h, ENat.natCast_le_natCast]
    constructor
    · intro hle
      exact isCentralNilpotenceBound_mono ρ χ hle (Nat.find_spec h)
    · intro hn
      exact Nat.find_min' h hn
  · have hn : ¬ IsCentralNilpotenceBound ρ χ n := fun hn => h ⟨n, hn⟩
    simp [centralCharacterNilpotenceIndex, h, hn]

/-- An absent character has index zero, and index zero forces absence. -/
theorem centralCharacterNilpotenceIndex_eq_zero_iff (ρ : Representation R G V)
    (χ : Subgroup.center G →* Rˣ) :
    centralCharacterNilpotenceIndex ρ χ = 0 ↔
      generalizedCentralCharacterSpace ρ χ = ⊥ := by
  rw [← le_zero_iff, ← Nat.cast_zero (R := ℕ∞),
    centralCharacterNilpotenceIndex_le_iff]
  simp [IsCentralNilpotenceBound]

/-- Infinity records precisely the failure of a uniform finite bound. -/
theorem centralCharacterNilpotenceIndex_eq_top_iff (ρ : Representation R G V)
    (χ : Subgroup.center G →* Rˣ) :
    centralCharacterNilpotenceIndex ρ χ = ⊤ ↔
      ¬ ∃ n, IsCentralNilpotenceBound ρ χ n := by
  classical
  by_cases h : ∃ n, IsCentralNilpotenceBound ρ χ n
  · simp [centralCharacterNilpotenceIndex, h]
  · simp [centralCharacterNilpotenceIndex, h]

/-- The bound is equivalently stabilization of the increasing character spaces. -/
theorem isCentralNilpotenceBound_iff_eq (ρ : Representation R G V)
    (χ : Subgroup.center G →* Rˣ) (n : ℕ) :
    IsCentralNilpotenceBound ρ χ n ↔
      centralCharacterSpace ρ χ n = generalizedCentralCharacterSpace ρ χ := by
  have hle : centralCharacterSpace ρ χ n ≤ generalizedCentralCharacterSpace ρ χ :=
    le_iSup (fun k => (centralCharacterSpace ρ χ k).toSubmodule) n
  exact ⟨fun h => le_antisymm hle h, fun h => h.ge⟩

variable {ρ : Representation R G V} {σ : Representation R G W}

/-- Equivariant linear equivalence preserves every common bound. -/
theorem isCentralNilpotenceBound_equiv_iff (e : ρ.Equiv σ)
    (χ : Subgroup.center G →* Rˣ) (n : ℕ) :
    IsCentralNilpotenceBound ρ χ n ↔ IsCentralNilpotenceBound σ χ n := by
  constructor
  · intro h v hv
    have hv' := map_mem_generalizedCentralCharacterSpace e.symm.toIntertwiningMap χ hv
    have hm := map_mem_centralCharacterSpace e.toIntertwiningMap χ n (h hv')
    simpa using hm
  · intro h v hv
    have hv' := map_mem_generalizedCentralCharacterSpace e.toIntertwiningMap χ hv
    have hm := map_mem_centralCharacterSpace e.symm.toIntertwiningMap χ n (h hv')
    simpa using hm

/-- The constructed index depends only on the equivariant isomorphism class. -/
theorem centralCharacterNilpotenceIndex_equiv (e : ρ.Equiv σ)
    (χ : Subgroup.center G →* Rˣ) :
    centralCharacterNilpotenceIndex ρ χ = centralCharacterNilpotenceIndex σ χ := by
  have hpred : IsCentralNilpotenceBound ρ χ = IsCentralNilpotenceBound σ χ :=
    funext fun n => propext (isCentralNilpotenceBound_equiv_iff e χ n)
  unfold centralCharacterNilpotenceIndex
  rw [hpred]

end Langlands
