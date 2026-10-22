import Langlands.Automorphic.DifferentialCenterFinite

/-! # Commuting finite adelic and genuine differential actions -/

noncomputable section
universe u

namespace Langlands.Automorphic

open Langlands.Global NumberField ContinuousRationalFunctions

set_option backward.isDefEq.respectTransparency false

variable (K : Type u) [Field K] [NumberField K] (n : ℕ)

local instance : AddCommGroup (RationalInvariantFunctions K n) :=
  Submodule.addCommGroup _
local instance : AddCommGroup (ContinuousRationalFunctions K n) :=
  Submodule.addCommGroup _
local instance : AddCommGroup (FiniteSmoothRationalFunctions K n) :=
  Submodule.addCommGroup _

/-- Restriction of actual right translation to the finite adelic factor. -/
def finiteSmoothFiniteRightAction :
    Representation ℂ (FiniteAdelicGL K n) (FiniteSmoothRationalFunctions K n) :=
  (finiteSmoothRightAction K n).comp (AdelicGL.ofFinite K n).toMonoidHom

/-- Finite translation only reindexes the genuine infinite slices. -/
theorem finiteSmoothSlice_finiteRightAction (d b : FiniteAdelicGL K n)
    (f : FiniteSmoothRationalFunctions K n) :
    finiteSmoothSlice K n b (finiteSmoothFiniteRightAction K n d f) =
      finiteSmoothSlice K n (b * d) f := by
  apply Subtype.ext
  funext a
  change evaluate K n f.val (AdelicGL.pair K n a b * AdelicGL.ofFinite K n d) =
    evaluate K n f.val (AdelicGL.pair K n a (b * d))
  rw [AdelicGL.ofFinite_eq_pair, AdelicGL.pair_mul, mul_one]

/-- Finite translation commutes with each actual enveloping differential operator. -/
theorem finiteSmoothFiniteRightAction_envelopingAction
    (d : FiniteAdelicGL K n) (a : ArchimedeanGL.EnvelopingAlgebra K n)
    (f : FiniteSmoothRationalFunctions K n) :
    finiteSmoothFiniteRightAction K n d (finiteSmoothEnvelopingAction K n a f) =
      finiteSmoothEnvelopingAction K n a (finiteSmoothFiniteRightAction K n d f) := by
  apply finiteSmoothSlice_injective K n
  funext b
  simp only [finiteSmoothSlice_finiteRightAction, finiteSmoothSlice_envelopingAction]

/-- Finite translation intertwines the genuine center representation. -/
def finiteSmoothFiniteCenterIntertwiner (d : FiniteAdelicGL K n) :
    (finiteSmoothCenterRepresentation K n).IntertwiningMap
      (finiteSmoothCenterRepresentation K n) where
  toLinearMap := finiteSmoothFiniteRightAction K n d
  isIntertwining' z := by
    apply LinearMap.ext
    intro f
    exact finiteSmoothFiniteRightAction_envelopingAction K n d
      (ArchimedeanGL.centerInclusion K n z) f

theorem isCenterFinite_finiteSmoothFiniteRightAction (d : FiniteAdelicGL K n)
    {f : FiniteSmoothRationalFunctions K n}
    (hf : IsCenterFinite K n (finiteSmoothInclusion K n f)) :
    IsCenterFinite K n
      (finiteSmoothInclusion K n (finiteSmoothFiniteRightAction K n d f)) := by
  apply (isCenterFinite_iff_finiteSmoothCenterVector K n _).mpr
  exact ((isCenterFinite_iff_finiteSmoothCenterVector K n f).mp hf).map
    (finiteSmoothFiniteCenterIntertwiner K n d)

/-- Reindexing by an invertible finite matrix retains exactly the common annihilator. -/
theorem centerFamilyAnnihilator_finiteRightAction
    (d : FiniteAdelicGL K n) (f : FiniteSmoothRationalFunctions K n) :
    centerFamilyAnnihilator K n
        (finiteSmoothCenterSlices K n (finiteSmoothFiniteRightAction K n d f)) =
      centerFamilyAnnihilator K n (finiteSmoothCenterSlices K n f) := by
  ext z
  simp only [mem_centerFamilyAnnihilator, finiteSmoothCenterSlices_apply,
    finiteSmoothSlice_finiteRightAction]
  constructor
  · intro h b
    simpa only [inv_mul_cancel_right] using h (b * d⁻¹)
  · intro h b
    exact h (b * d)

/-- The actual simultaneous center-finite space is stable under finite translation. -/
def centerFiniteFiniteSmoothSubrepresentation :
    Subrepresentation (finiteSmoothFiniteRightAction K n) where
  toSubmodule := centerFiniteFiniteSmoothFunctions K n
  apply_mem_toSubmodule d _ hf := isCenterFinite_finiteSmoothFiniteRightAction K n d hf

/-- The type of finite adelic representations on the existing center-finite space. -/
abbrev CenterFiniteFiniteAction :=
  Representation ℂ (FiniteAdelicGL K n) (CenterFiniteFiniteSmoothRationalFunctions K n)

/-- Actual finite adelic right translation on the center-finite finite-smooth functions. -/
def centerFiniteFiniteSmoothRightAction : CenterFiniteFiniteAction K n :=
  (centerFiniteFiniteSmoothSubrepresentation K n).toRepresentation

@[simp]
theorem centerFiniteFiniteSmoothRightAction_val (d : FiniteAdelicGL K n)
    (f : CenterFiniteFiniteSmoothRationalFunctions K n) :
    (centerFiniteFiniteSmoothRightAction K n d f).val =
      finiteSmoothFiniteRightAction K n d f.val := rfl

/-- This finite adelic representation is smooth for the actual group topology. -/
theorem centerFiniteFiniteSmoothRightAction_isSmooth :
    Langlands.IsSmooth (centerFiniteFiniteSmoothRightAction K n) := by
  intro f
  obtain ⟨L, hL⟩ := f.val.property.2
  refine ⟨L, ?_⟩
  intro l
  apply Subtype.ext
  apply Subtype.ext
  exact hL l

/-- Both previously constructed actions commute on the actual common space. -/
theorem centerFiniteFiniteSmoothRightAction_envelopingAction
    (d : FiniteAdelicGL K n) (a : ArchimedeanGL.EnvelopingAlgebra K n)
    (f : CenterFiniteFiniteSmoothRationalFunctions K n) :
    centerFiniteFiniteSmoothRightAction K n d (centerFiniteEnvelopingAction K n a f) =
      centerFiniteEnvelopingAction K n a (centerFiniteFiniteSmoothRightAction K n d f) := by
  apply Subtype.ext
  exact finiteSmoothFiniteRightAction_envelopingAction K n d a f.val

/-- Each genuine differential operator is now a finite adelic intertwiner. -/
def centerFiniteDifferentialFiniteIntertwiner (a : ArchimedeanGL.EnvelopingAlgebra K n) :
    (centerFiniteFiniteSmoothRightAction K n).IntertwiningMap
      (centerFiniteFiniteSmoothRightAction K n) where
  toLinearMap := centerFiniteEnvelopingAction K n a
  isIntertwining' d := by
    apply LinearMap.ext
    intro f
    exact (centerFiniteFiniteSmoothRightAction_envelopingAction K n d a f).symm

/-- The concrete inclusion intertwines finite translations. -/
def centerFiniteFiniteSmoothInclusion :
    (centerFiniteFiniteSmoothRightAction K n).IntertwiningMap
      (finiteSmoothFiniteRightAction K n) where
  toLinearMap := (centerFiniteFiniteSmoothFunctions K n).subtype
  isIntertwining' _ := by ext; rfl

theorem centerFiniteFiniteSmoothInclusion_injective :
    Function.Injective (centerFiniteFiniteSmoothInclusion K n) := Subtype.val_injective

@[simp]
theorem centerFiniteFiniteSmoothInclusion_envelopingAction
    (a : ArchimedeanGL.EnvelopingAlgebra K n)
    (f : CenterFiniteFiniteSmoothRationalFunctions K n) :
    centerFiniteFiniteSmoothInclusion K n (centerFiniteEnvelopingAction K n a f) =
      finiteSmoothEnvelopingAction K n a (centerFiniteFiniteSmoothInclusion K n f) := rfl

@[simp]
theorem evaluate_centerFiniteFiniteSmoothRightAction (d : FiniteAdelicGL K n)
    (f : CenterFiniteFiniteSmoothRationalFunctions K n) (x : AdelicGL K n) :
    evaluate K n (centerFiniteFiniteSmoothRightAction K n d f).val.val x =
      evaluate K n f.val.val (x * AdelicGL.ofFinite K n d) := rfl

end Langlands.Automorphic
