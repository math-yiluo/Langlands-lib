import Langlands.Representation.Classification.Supercuspidal
import Langlands.Representation.Conductor.ClassLevel

/-!
# Fixed-invariant subsets of genuine supercuspidal classes

The underlying classes use the actual Jacquet-quotient vanishing condition.
No abstract substitute for supercuspidality or theorem of finiteness is used.
-/

noncomputable section

namespace Langlands.GeneralLinear.SupercuspidalClass

universe uF uV

variable {F : Type uF} [Field F] [TopologicalSpace F] {n : ℕ}

/-- Scalar action of a prescribed character of the actual center. -/
def HasCentralCharacter (χ : Subgroup.center (GeneralLinear n F) →* ℂˣ)
    (a : SupercuspidalClass.{uV, uF} (F := F) (n := n)) : Prop :=
  SmoothDualClass.HasCentralCharacter χ a.toSmoothDualClass

/-- A nonzero vector fixed by the specified actual subgroup. -/
def HasFixedVector (K : Subgroup (GeneralLinear n F))
    (a : SupercuspidalClass.{uV, uF} (F := F) (n := n)) : Prop :=
  SmoothDualClass.HasFixedVector K a.toSmoothDualClass

@[simp]
theorem hasCentralCharacter_isoClass
    (χ : Subgroup.center (GeneralLinear n F) →* ℂˣ)
    (A : SupercuspidalRep.{uF, uV} (F := F) (n := n)) :
    HasCentralCharacter χ A.isoClass ↔ A.obj.HasCentralCharacter χ := Iff.rfl

@[simp]
theorem hasFixedVector_isoClass (K : Subgroup (GeneralLinear n F))
    (A : SupercuspidalRep.{uF, uV} (F := F) (n := n)) :
    HasFixedVector K A.isoClass ↔ fixedVectors A.obj.representation K ≠ ⊥ := Iff.rfl

/-- The actual supercuspidal subset with prescribed center action and fixed vectors. -/
def centralFixedStratum (χ : Subgroup.center (GeneralLinear n F) →* ℂˣ)
    (K : Subgroup (GeneralLinear n F)) :
    Set (SupercuspidalClass.{uV, uF} (F := F) (n := n)) :=
  {a | HasCentralCharacter χ a ∧ HasFixedVector K a}

section Level

variable [ValuativeRel F]

/-- The first nonzero newvector level on genuine supercuspidal classes;
infinity is retained until finite-level existence is established. -/
def firstFixedLevel
    (a : SupercuspidalClass.{uV, uF} (F := F) (n := n + 1)) : WithTop ℕ :=
  SmoothDualClass.firstFixedLevel a.toSmoothDualClass

@[simp]
theorem firstFixedLevel_isoClass
    (A : SupercuspidalRep.{uF, uV} (F := F) (n := n + 1)) :
    firstFixedLevel A.isoClass = Conductor.firstFixedLevel A.obj.representation := rfl

/-- The finite bound is equivalent to nonzero invariants at that exact level. -/
theorem firstFixedLevel_le_iff
    (a : SupercuspidalClass.{uV, uF} (F := F) (n := n + 1)) (b : ℕ) :
    firstFixedLevel a ≤ (b : WithTop ℕ) ↔
      HasFixedVector (Conductor.levelSubgroup F n b) a :=
  SmoothDualClass.firstFixedLevel_le_iff a.toSmoothDualClass b

/-- Fixed central character and bounded first nonzero last-row level.
This is not a definition of the general epsilon-factor conductor. -/
def centralLevelStratum
    (χ : Subgroup.center (GeneralLinear (n + 1) F) →* ℂˣ) (b : ℕ) :
    Set (SupercuspidalClass.{uV, uF} (F := F) (n := n + 1)) :=
  {a | HasCentralCharacter χ a ∧ firstFixedLevel a ≤ (b : WithTop ℕ)}

/-- This bounded-level stratum is precisely the corresponding fixed-space stratum. -/
theorem centralLevelStratum_eq
    (χ : Subgroup.center (GeneralLinear (n + 1) F) →* ℂˣ) (b : ℕ) :
    centralLevelStratum.{uF, uV} χ b =
      centralFixedStratum χ (Conductor.levelSubgroup F n b) := by
  ext a
  exact and_congr Iff.rfl (firstFixedLevel_le_iff a b)

end Level
end Langlands.GeneralLinear.SupercuspidalClass
