import Langlands.Representation.Conductor.Congruence
import Langlands.Representation.Smooth.Definitions
import Mathlib.Data.Nat.Find
import Mathlib.Order.WithBot

/-!
# Fixed levels and newvectors

This is the concrete fixed-level construction. It does not assert that every
representation has a finite newvector level, or identify that level with an
epsilon exponent. See JPSS (1981), Section 5.1, page 211.
-/

noncomputable section

namespace Langlands.Conductor

universe uK uF uV

open Matrix

variable {K : Type uK} [CommRing K]
variable {F : Type uF} [Field F] [ValuativeRel F]
variable {V : Type uV} [AddCommGroup V] [Module K V]
variable {n : ℕ}

/-- The actual invariant submodule for the level-`a` newvector subgroup. -/
def levelFixedVectors (ρ : Representation K (GeneralLinearGroup (Fin (n + 1)) F) V)
    (a : ℕ) : Submodule K V :=
  Langlands.fixedVectors ρ (levelSubgroup F n a)

theorem mem_levelFixedVectors
    (ρ : Representation K (GeneralLinearGroup (Fin (n + 1)) F) V) (a : ℕ) (v : V) :
    v ∈ levelFixedVectors ρ a ↔ ∀ g ∈ levelSubgroup F n a, ρ g v = v := by
  change (∀ g : levelSubgroup F n a, ρ g v = v) ↔ _
  exact ⟨fun h g hg => h ⟨g, hg⟩, fun h g => h g g.property⟩

/-- Higher levels have larger invariant submodules. -/
theorem levelFixedVectors_mono
    (ρ : Representation K (GeneralLinearGroup (Fin (n + 1)) F) V) :
    Monotone (levelFixedVectors ρ) := by
  intro a b hab v hv
  exact (mem_levelFixedVectors ρ b v).2 fun g hg =>
    (mem_levelFixedVectors ρ a v).1 hv g (levelSubgroup_antitone F n hab hg)

/-- The explicit prerequisite for a finite newvector level. -/
def HasNewvectorLevel
    (ρ : Representation K (GeneralLinearGroup (Fin (n + 1)) F) V) : Prop :=
  ∃ a : ℕ, levelFixedVectors ρ a ≠ ⊥

/-- `a` is the least level with a nonzero fixed vector. This is an intrinsic
fixed-vector characterization, not a supplied factor function. -/
def IsNewvectorConductor
    (ρ : Representation K (GeneralLinearGroup (Fin (n + 1)) F) V) (a : ℕ) : Prop :=
  levelFixedVectors ρ a ≠ ⊥ ∧ ∀ b < a, levelFixedVectors ρ b = ⊥

/-- The least nonzero fixed level, with its existence proof visible. -/
def newvectorConductor
    (ρ : Representation K (GeneralLinearGroup (Fin (n + 1)) F) V)
    (h : HasNewvectorLevel ρ) : ℕ :=
  Nat.find h

/-- The chosen level satisfies both the nonvanishing and minimality conditions. -/
theorem newvectorConductor_spec
    (ρ : Representation K (GeneralLinearGroup (Fin (n + 1)) F) V)
    (h : HasNewvectorLevel ρ) :
    IsNewvectorConductor ρ (newvectorConductor ρ h) := by
  classical
  refine ⟨Nat.find_spec h, ?_⟩
  intro b hb
  exact Classical.not_not.mp (Nat.find_min h hb)

/-- The intrinsic conductor characterization determines a unique level. -/
theorem IsNewvectorConductor.unique
    {ρ : Representation K (GeneralLinearGroup (Fin (n + 1)) F) V} {a b : ℕ}
    (ha : IsNewvectorConductor ρ a) (hb : IsNewvectorConductor ρ b) : a = b := by
  apply le_antisymm
  · by_contra h
    exact hb.1 (ha.2 b (Nat.lt_of_not_ge h))
  · by_contra h
    exact ha.1 (hb.2 a (Nat.lt_of_not_ge h))

/-- Equality with the chosen conductor is equivalent to the intrinsic relation. -/
theorem newvectorConductor_eq_iff
    (ρ : Representation K (GeneralLinearGroup (Fin (n + 1)) F) V)
    (h : HasNewvectorLevel ρ) (a : ℕ) :
    newvectorConductor ρ h = a ↔ IsNewvectorConductor ρ a := by
  constructor
  · rintro rfl
    exact newvectorConductor_spec ρ h
  · exact (newvectorConductor_spec ρ h).unique

/-- A total first-level object. Its value is infinity when all fixed spaces
vanish; infinity is not identified with a finite conductor exponent. -/
def firstFixedLevel
    (ρ : Representation K (GeneralLinearGroup (Fin (n + 1)) F) V) : WithTop ℕ := by
  classical
  exact if h : HasNewvectorLevel ρ then (newvectorConductor ρ h : WithTop ℕ) else ⊤

theorem firstFixedLevel_eq_top_iff
    (ρ : Representation K (GeneralLinearGroup (Fin (n + 1)) F) V) :
    firstFixedLevel ρ = ⊤ ↔ ¬ HasNewvectorLevel ρ := by
  classical
  unfold firstFixedLevel
  split <;> simp_all

theorem firstFixedLevel_of_hasNewvectorLevel
    (ρ : Representation K (GeneralLinearGroup (Fin (n + 1)) F) V)
    (h : HasNewvectorLevel ρ) :
    firstFixedLevel ρ = (newvectorConductor ρ h : WithTop ℕ) := by
  classical
  simp [firstFixedLevel, h]

/-- The fixed submodule at the least nonzero level. It is not called a line
until a dimension-one theorem has been proved for the representation. -/
def newvectorSpace
    (ρ : Representation K (GeneralLinearGroup (Fin (n + 1)) F) V)
    (h : HasNewvectorLevel ρ) : Submodule K V :=
  levelFixedVectors ρ (newvectorConductor ρ h)

/-- A nonzero vector in the first nonzero fixed space. This construction
does not choose a Whittaker normalization or assert essentiality. -/
def newvector
    (ρ : Representation K (GeneralLinearGroup (Fin (n + 1)) F) V)
    (h : HasNewvectorLevel ρ) :
    {v : V // v ∈ newvectorSpace ρ h ∧ v ≠ 0} :=
  let hex := (newvectorSpace ρ h).ne_bot_iff.mp (newvectorConductor_spec ρ h).1
  ⟨Classical.choose hex, Classical.choose_spec hex⟩

section LocalField

variable [TopologicalSpace F] [IsNonarchimedeanLocalField F]

/-- Every vector in one of these concrete fixed spaces is a smooth vector. -/
theorem isSmoothVector_of_mem_levelFixedVectors
    (ρ : Representation K (GeneralLinearGroup (Fin (n + 1)) F) V)
    {a : ℕ} {v : V} (hv : v ∈ levelFixedVectors ρ a) :
    Langlands.IsSmoothVector ρ v :=
  ⟨levelOpenSubgroup F n a, hv⟩

/-- Admissibility applies to each of the proved open level subgroups. -/
theorem finite_levelFixedVectors
    (ρ : Representation K (GeneralLinearGroup (Fin (n + 1)) F) V)
    (hρ : Langlands.IsAdmissible ρ) (a : ℕ) :
    Module.Finite K (levelFixedVectors ρ a) :=
  hρ.2 (levelOpenSubgroup F n a)

end LocalField

section Normalization

variable {k : Type uK} [Field k] [Module k V]

/-- Normalize a specified fixed vector by a specified nonvanishing linear
functional. In a Whittaker model the functional can be evaluation at one.
No nonvanishing or uniqueness theorem is implicit in this constructor. -/
def normalizeFixedVector
    (ρ : Representation k (GeneralLinearGroup (Fin (n + 1)) F) V) (a : ℕ)
    (ℓ : V →ₗ[k] k) (v : levelFixedVectors ρ a) (hv : ℓ v ≠ 0) :
    {w : levelFixedVectors ρ a // ℓ w = 1} :=
  ⟨(ℓ v)⁻¹ • v, by simp [map_smul, hv]⟩

end Normalization

end Langlands.Conductor
