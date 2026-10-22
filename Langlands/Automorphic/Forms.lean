import Langlands.Automorphic.FiniteDifferential
import Langlands.Automorphic.FiniteVectors
import Langlands.Global.FiniteAdelicGL.StandardIntegralCompact
import Langlands.Global.ArchimedeanCompactMaximalityProof
import Langlands.Global.ArchimedeanHilbertGrowthComparison

/-! # Actual automorphic forms and their finite adelic action -/

noncomputable section
universe u

namespace Langlands.Automorphic

open Langlands.Global NumberField ContinuousRationalFunctions

set_option backward.isDefEq.respectTransparency false

variable (K : Type u) [Field K] [NumberField K] (n : ℕ)

local instance : AddCommGroup (RationalInvariantFunctions K n) := Submodule.addCommGroup _
local instance : AddCommGroup (ContinuousRationalFunctions K n) := Submodule.addCommGroup _
local instance : AddCommGroup (FiniteSmoothRationalFunctions K n) := Submodule.addCommGroup _

/-- A common open finite stabilizer is equivalent to actual compact finite level. -/
theorem hasFiniteLevel_iff_mem_finiteSmooth (f : ContinuousRationalFunctions K n) :
    HasFiniteLevel K n f ↔ f ∈ finiteSmoothSubrepresentation K n :=
  ⟨hasFiniteLevel_mem_finiteSmooth K n f,
    finiteSmooth_hasFiniteLevel K n (FiniteAdelicGL.standardIntegral K n)
      (FiniteAdelicGL.isCompact_standardIntegral K n) f⟩

/-- The automorphic conditions on actual smooth rational-invariant functions.
The center ideal is common to all slices; growth is imposed separately on each slice. -/
def IsAutomorphicForm (f : SmoothRationalFunctions K n) : Prop :=
  HasFiniteLevel K n f.val ∧
    IsInfiniteFinite K n (standardInfiniteCompact K n) f.val ∧
    IsCenterFinite K n f ∧ HasPolynomialGrowth K n f.val

/-- The concrete form space inside the actual common-finite-stabilizer smooth functions. -/
def automorphicSubrepresentation : Subrepresentation (finiteSmoothFiniteRightAction K n) where
  toSubmodule := centerFiniteFiniteSmoothFunctions K n ⊓
    (((infiniteFiniteSubrepresentation K n (standardInfiniteCompact K n)).toSubmodule ⊓
      (polynomialGrowthSubrepresentation K n).toSubmodule).comap
        (finiteSmoothRationalSubrepresentation K n).toSubmodule.subtype)
  apply_mem_toSubmodule d _ hf :=
    ⟨isCenterFinite_finiteSmoothFiniteRightAction K n d hf.1,
      isInfiniteFinite_finiteRightAction K n (standardInfiniteCompact K n) d hf.2.1,
      (polynomialGrowthSubrepresentation K n).apply_mem_toSubmodule
        (AdelicGL.ofFinite K n d) hf.2.2⟩

@[simp]
theorem mem_automorphicSubrepresentation (f : FiniteSmoothRationalFunctions K n) :
    f ∈ automorphicSubrepresentation K n ↔
      IsAutomorphicForm K n (finiteSmoothInclusion K n f) := by
  change (IsCenterFinite K n (finiteSmoothInclusion K n f) ∧
      IsInfiniteFinite K n (standardInfiniteCompact K n) f.val ∧
      f.val ∈ polynomialGrowthSubrepresentation K n) ↔ _
  rw [mem_polynomialGrowthSubrepresentation]
  constructor
  · rintro ⟨hc, hk, hg⟩
    exact ⟨(hasFiniteLevel_iff_mem_finiteSmooth K n f.val).mpr f.property.2, hk, hc, hg⟩
  · rintro ⟨_, hk, hc, hg⟩
    exact ⟨hc, hk, hg⟩

/-- Every form in the smooth ambient space has the concrete finite-smooth realization. -/
theorem isAutomorphicForm_iff_exists_finiteSmooth (f : SmoothRationalFunctions K n) :
    IsAutomorphicForm K n f ↔
      ∃ F : FiniteSmoothRationalFunctions K n,
        F ∈ automorphicSubrepresentation K n ∧ finiteSmoothInclusion K n F = f := by
  constructor
  · intro hf
    let F : FiniteSmoothRationalFunctions K n :=
      ⟨f.val, f.property.1, (hasFiniteLevel_iff_mem_finiteSmooth K n f.val).mp hf.1⟩
    have hF : finiteSmoothInclusion K n F = f := Subtype.ext rfl
    exact ⟨F, (mem_automorphicSubrepresentation K n F).mpr (hF.symm ▸ hf), hF⟩
  · rintro ⟨F, hF, rfl⟩
    exact (mem_automorphicSubrepresentation K n F).mp hF

/-- Actual complex automorphic forms on the adelic matrix group. -/
abbrev AutomorphicForms := (automorphicSubrepresentation K n).toSubmodule

/-- The type of finite adelic representations on the constructed form space. -/
abbrev AutomorphicFiniteAction :=
  Representation ℂ (FiniteAdelicGL K n) (AutomorphicForms K n)

/-- Actual finite adelic right translation on automorphic forms. -/
def automorphicFiniteRightAction : AutomorphicFiniteAction K n :=
  (automorphicSubrepresentation K n).toRepresentation

/-- The finite adelic action has an open stabilizer for every form. -/
theorem automorphicFiniteRightAction_isSmooth :
    Langlands.IsSmooth (automorphicFiniteRightAction K n) := by
  intro f
  obtain ⟨L, hL⟩ := f.val.property.2
  refine ⟨L, ?_⟩
  intro l
  apply Subtype.ext
  apply Subtype.ext
  exact hL l

/-- Inclusion into actual finite-smooth functions intertwines finite translation. -/
def automorphicFiniteSmoothInclusion :
    (automorphicFiniteRightAction K n).IntertwiningMap
      (finiteSmoothFiniteRightAction K n) where
  toLinearMap := (automorphicSubrepresentation K n).toSubmodule.subtype
  isIntertwining' _ := by ext; rfl

theorem automorphicFiniteSmoothInclusion_injective :
    Function.Injective (automorphicFiniteSmoothInclusion K n) := Subtype.val_injective

/-- Realization as continuous rational-invariant adelic functions. -/
def automorphicToContinuous : AutomorphicForms K n →ₗ[ℂ] ContinuousRationalFunctions K n :=
  (finiteSmoothRationalSubrepresentation K n).toSubmodule.subtype.comp
    (automorphicSubrepresentation K n).toSubmodule.subtype

theorem automorphicToContinuous_injective :
    Function.Injective (automorphicToContinuous K n) :=
  Subtype.val_injective.comp Subtype.val_injective

@[simp]
theorem automorphicToContinuous_finiteRightAction (d : FiniteAdelicGL K n)
    (f : AutomorphicForms K n) :
    automorphicToContinuous K n (automorphicFiniteRightAction K n d f) =
      finiteRightAction K n d (automorphicToContinuous K n f) := rfl

@[simp]
theorem evaluate_automorphicFiniteRightAction (d : FiniteAdelicGL K n)
    (f : AutomorphicForms K n) (x : AdelicGL K n) :
    evaluate K n (automorphicToContinuous K n (automorphicFiniteRightAction K n d f)) x =
      evaluate K n (automorphicToContinuous K n f) (x * AdelicGL.ofFinite K n d) := rfl

/-- The explicit conditions, using a single finite-codimensional ideal and the source norm. -/
theorem isAutomorphicForm_iff_source_conditions (f : SmoothRationalFunctions K n) :
    IsAutomorphicForm K n f ↔
      HasFiniteLevel K n f.val ∧
      IsInfiniteFinite K n (standardInfiniteCompact K n) f.val ∧
      (∃ I : Ideal (ArchimedeanGL.EnvelopingCenter K n),
        Module.Finite ℂ (ArchimedeanGL.EnvelopingCenter K n ⧸ I.restrictScalars ℂ) ∧
        ∀ z ∈ I, ∀ b,
          ArchimedeanGL.centerAction K n z (smoothInfiniteSlice K n b f) = 0) ∧
      (∀ b : FiniteAdelicGL K n, ∃ C : ℝ, 0 ≤ C ∧ ∃ d : ℕ,
        ∀ a : InfiniteAdelicGL K n,
          ‖evaluate K n f.val (AdelicGL.pair K n a b)‖ ≤
            C * infiniteAdelicHilbertNorm K n a ^ d) := by
  unfold IsAutomorphicForm
  rw [isCenterFinite_iff_exists_ideal]
  exact and_congr_right fun _ => and_congr_right fun _ => and_congr_right fun _ =>
    adelicHilbertGrowthEquivalence K n f.val

end Langlands.Automorphic
