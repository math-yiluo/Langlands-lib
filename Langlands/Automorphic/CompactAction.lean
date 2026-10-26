import Langlands.Automorphic.CompactTranslationProof
import Langlands.Automorphic.OperatorCore

/-! # The compact action on the full space of actual automorphic forms -/

noncomputable section
universe u

namespace Langlands.Automorphic

open Langlands.Global

variable (K : Type u) [Field K] [NumberField K] (n : ℕ)

local instance compactActionRationalAddCommGroup :
    AddCommGroup (RationalInvariantFunctions K n) := Submodule.addCommGroup _
local instance compactActionContinuousAddCommGroup :
    AddCommGroup (ContinuousRationalFunctions K n) := Submodule.addCommGroup _
local instance compactActionSmoothAddCommGroup :
    AddCommGroup (FiniteSmoothRationalFunctions K n) := Submodule.addCommGroup _
local instance compactActionFormsAddCommGroup :
    AddCommGroup (AutomorphicForms K n) := Submodule.addCommGroup _
local instance compactActionStableAddCommGroup :
    AddCommGroup (StableAutomorphicFunctions K n) := Submodule.addCommGroup _

/-- The full automorphic subspace is stable under the actual standard compact group. -/
def automorphicCompactSubrepresentation :
    Subrepresentation (finiteSmoothCompactRightAction K n) where
  toSubmodule := (automorphicSubrepresentation K n).toSubmodule
  apply_mem_toSubmodule k f hf :=
    (mem_automorphicSubrepresentation K n _).mpr
      (automorphicCompactTranslation K n k _
        ((mem_automorphicSubrepresentation K n f).mp hf))

/-- Actual positive right translation by the standard infinite compact on all forms. -/
def automorphicCompactRightAction :
    Representation ℂ (standardInfiniteCompact K n) (AutomorphicForms K n) :=
  (automorphicCompactSubrepresentation K n).toRepresentation

@[simp]
theorem automorphicCompactRightAction_val (k : standardInfiniteCompact K n)
    (f : AutomorphicForms K n) :
    (automorphicCompactRightAction K n k f).val =
      finiteSmoothCompactRightAction K n k f.val := rfl

/-- The concrete inclusion into finite-smooth functions intertwines compact translation. -/
def automorphicCompactFiniteSmoothInclusion :
    (automorphicCompactRightAction K n).IntertwiningMap
      (finiteSmoothCompactRightAction K n) where
  toLinearMap := (automorphicSubrepresentation K n).toSubmodule.subtype
  isIntertwining' _ := by ext; rfl

theorem automorphicCompactFiniteSmoothInclusion_injective :
    Function.Injective (automorphicCompactFiniteSmoothInclusion K n) :=
  Subtype.val_injective

/-- The faithful continuous-function realization intertwines the compact actions. -/
def automorphicCompactContinuousInclusion :
    (automorphicCompactRightAction K n).IntertwiningMap
      (infiniteSubgroupRightAction K n (standardInfiniteCompact K n)) where
  toLinearMap := automorphicToContinuous K n
  isIntertwining' _ := by ext; rfl

theorem automorphicCompactContinuousInclusion_injective :
    Function.Injective (automorphicCompactContinuousInclusion K n) :=
  automorphicToContinuous_injective K n

@[simp]
theorem automorphicToContinuous_compactRightAction (k : standardInfiniteCompact K n)
    (f : AutomorphicForms K n) :
    automorphicToContinuous K n (automorphicCompactRightAction K n k f) =
      infiniteSubgroupRightAction K n (standardInfiniteCompact K n) k
        (automorphicToContinuous K n f) := rfl

@[simp]
theorem evaluate_automorphicCompactRightAction (k : standardInfiniteCompact K n)
    (f : AutomorphicForms K n) (x : AdelicGL K n) :
    ContinuousRationalFunctions.evaluate K n
        (automorphicToContinuous K n (automorphicCompactRightAction K n k f)) x =
      ContinuousRationalFunctions.evaluate K n
        (automorphicToContinuous K n f) (x * AdelicGL.ofInfinite K n k.val) := rfl

/-- Every vector of this full automorphic representation is compact-finite. -/
theorem automorphicCompactRightAction_isFiniteVector (f : AutomorphicForms K n) :
    FiniteVectors.IsFiniteVector (automorphicCompactRightAction K n) f := by
  apply (FiniteVectors.isFiniteVector_map_iff
    (automorphicCompactContinuousInclusion K n)
    (automorphicCompactContinuousInclusion_injective K n) f).mp
  exact ((mem_automorphicSubrepresentation K n f.val).mp f.property).2.1

/-- Finite adelic translation and compact translation commute on the same full form space. -/
theorem automorphicFiniteRightAction_compactRightAction
    (d : FiniteAdelicGL K n) (k : standardInfiniteCompact K n)
    (f : AutomorphicForms K n) :
    automorphicFiniteRightAction K n d (automorphicCompactRightAction K n k f) =
      automorphicCompactRightAction K n k (automorphicFiniteRightAction K n d f) := by
  apply (automorphicToContinuous_injective K n)
  exact Representation.IntertwiningMap.isIntertwining _ _
    (finiteTranslateIntertwiner K n (standardInfiniteCompact K n) d) k
    (automorphicToContinuous K n f)

/-- Each compact translation is a finite adelic intertwiner on the full form space. -/
def automorphicCompactFiniteIntertwiner (k : standardInfiniteCompact K n) :
    (automorphicFiniteRightAction K n).IntertwiningMap
      (automorphicFiniteRightAction K n) where
  toLinearMap := automorphicCompactRightAction K n k
  isIntertwining' d := by
    apply LinearMap.ext
    intro f
    exact (automorphicFiniteRightAction_compactRightAction K n d k f).symm

/-- The previous stable core embeds equivariantly for the compact action as well. -/
def stableAutomorphicCompactInclusion :
    (stableAutomorphicCompactAction K n).IntertwiningMap
      (automorphicCompactRightAction K n) where
  toLinearMap := (stableAutomorphicInclusion K n).toLinearMap
  isIntertwining' _ := by ext; rfl

theorem stableAutomorphicCompactInclusion_injective :
    Function.Injective (stableAutomorphicCompactInclusion K n) :=
  stableAutomorphicInclusion_injective K n

/-- After compact closure, full operator-core equality is exactly differential preservation. -/
theorem automorphicOperatorCore_eq_iff_differential :
    (automorphicOperatorCore K n).toSubmodule =
      (automorphicSubrepresentation K n).toSubmodule ↔
        AutomorphicDifferentialPreservationStatement K n := by
  rw [automorphicOperatorCore_eq_iff]
  exact ⟨And.right, fun h => ⟨automorphicCompactTranslation K n, h⟩⟩

end Langlands.Automorphic
