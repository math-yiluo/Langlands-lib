import Langlands.Automorphic.EnvelopingAction
import Langlands.Automorphic.CenterFinite

/-! # The genuine differential action on simultaneous center-finite functions -/

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

/-- The multiplicative representation underlying the actual center action. -/
def finiteSmoothCenterRepresentation :
    Representation ℂ (ArchimedeanGL.EnvelopingCenter K n)
      (FiniteSmoothRationalFunctions K n) :=
  (finiteSmoothCenterAction K n).toMonoidHom

/-- Extraction of all slices intertwines the actual center actions. -/
def finiteSmoothCenterSlices :
    (finiteSmoothCenterRepresentation K n).IntertwiningMap
      (centerFamilyRepresentation K n) where
  toLinearMap := LinearMap.pi (finiteSmoothSlice K n)
  isIntertwining' z := by
    apply LinearMap.ext
    intro f
    funext b
    exact finiteSmoothSlice_centerAction K n z f b

@[simp]
theorem finiteSmoothCenterSlices_apply (f : FiniteSmoothRationalFunctions K n)
    (b : FiniteAdelicGL K n) :
    finiteSmoothCenterSlices K n f b = finiteSmoothSlice K n b f := rfl

theorem finiteSmoothCenterSlices_injective :
    Function.Injective (finiteSmoothCenterSlices K n) :=
  finiteSmoothSlice_injective K n

/-- The faithful family is exactly the published slice extraction after inclusion. -/
theorem finiteSmoothCenterSlices_eq (f : FiniteSmoothRationalFunctions K n) :
    finiteSmoothCenterSlices K n f =
      smoothSliceFamily K n (finiteSmoothInclusion K n f) := rfl

/-- One finite center orbit on actual functions is the common slice-family condition. -/
theorem isCenterFinite_iff_finiteSmoothCenterVector
    (f : FiniteSmoothRationalFunctions K n) :
    IsCenterFinite K n (finiteSmoothInclusion K n f) ↔
      FiniteVectors.IsFiniteVector (finiteSmoothCenterRepresentation K n) f :=
  FiniteVectors.isFiniteVector_map_iff (finiteSmoothCenterSlices K n)
    (finiteSmoothCenterSlices_injective K n) f

/-- Every enveloping operator commutes with every actual central operator. -/
theorem finiteSmoothEnvelopingAction_center_commute
    (a : ArchimedeanGL.EnvelopingAlgebra K n)
    (z : ArchimedeanGL.EnvelopingCenter K n)
    (f : FiniteSmoothRationalFunctions K n) :
    finiteSmoothEnvelopingAction K n a (finiteSmoothCenterAction K n z f) =
      finiteSmoothCenterAction K n z (finiteSmoothEnvelopingAction K n a f) := by
  change finiteSmoothEnvelopingAction K n a
      (finiteSmoothEnvelopingAction K n (ArchimedeanGL.centerInclusion K n z) f) =
    finiteSmoothEnvelopingAction K n (ArchimedeanGL.centerInclusion K n z)
      (finiteSmoothEnvelopingAction K n a f)
  rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul,
    ArchimedeanGL.centerInclusion_commute]

/-- Differentiation is an intertwiner for the center representation. -/
def finiteSmoothDifferentialCenterIntertwiner
    (a : ArchimedeanGL.EnvelopingAlgebra K n) :
    (finiteSmoothCenterRepresentation K n).IntertwiningMap
      (finiteSmoothCenterRepresentation K n) where
  toLinearMap := finiteSmoothEnvelopingAction K n a
  isIntertwining' z := by
    apply LinearMap.ext
    intro f
    exact finiteSmoothEnvelopingAction_center_commute K n a z f

/-- The full enveloping action preserves simultaneous center finiteness. -/
theorem isCenterFinite_finiteSmoothEnvelopingAction
    (a : ArchimedeanGL.EnvelopingAlgebra K n)
    {f : FiniteSmoothRationalFunctions K n}
    (hf : IsCenterFinite K n (finiteSmoothInclusion K n f)) :
    IsCenterFinite K n
      (finiteSmoothInclusion K n (finiteSmoothEnvelopingAction K n a f)) := by
  apply (isCenterFinite_iff_finiteSmoothCenterVector K n _).mpr
  exact ((isCenterFinite_iff_finiteSmoothCenterVector K n f).mp hf).map
    (finiteSmoothDifferentialCenterIntertwiner K n a)

/-- Every common annihilating ideal is retained by differentiation. -/
theorem centerFamilyAnnihilator_le_differential
    (a : ArchimedeanGL.EnvelopingAlgebra K n)
    (f : FiniteSmoothRationalFunctions K n) :
    centerFamilyAnnihilator K n (finiteSmoothCenterSlices K n f) ≤
      centerFamilyAnnihilator K n
        (finiteSmoothCenterSlices K n (finiteSmoothEnvelopingAction K n a f)) := by
  intro z hz
  have hzero : finiteSmoothCenterAction K n z f = 0 := by
    apply finiteSmoothCenterSlices_injective K n
    change (fun b => finiteSmoothSlice K n b (finiteSmoothCenterAction K n z f)) =
      (fun b => finiteSmoothSlice K n b 0)
    funext b
    rw [finiteSmoothSlice_centerAction, map_zero]
    exact (mem_centerFamilyAnnihilator K n _ z).mp hz b
  apply (mem_centerFamilyAnnihilator K n _ z).mpr
  intro b
  change ArchimedeanGL.centerAction K n z
    (finiteSmoothSlice K n b (finiteSmoothEnvelopingAction K n a f)) = 0
  rw [← finiteSmoothSlice_centerAction, ← finiteSmoothEnvelopingAction_center_commute,
    hzero, map_zero, map_zero]

/-- Actual finite-smooth functions whose full family has one finite center orbit. -/
def centerFiniteFiniteSmoothFunctions : Submodule ℂ (FiniteSmoothRationalFunctions K n) :=
  (centerFiniteSmoothFunctions K n).comap (finiteSmoothInclusion K n).toLinearMap

@[simp]
theorem mem_centerFiniteFiniteSmoothFunctions (f : FiniteSmoothRationalFunctions K n) :
    f ∈ centerFiniteFiniteSmoothFunctions K n ↔
      IsCenterFinite K n (finiteSmoothInclusion K n f) := Iff.rfl

abbrev CenterFiniteFiniteSmoothRationalFunctions := centerFiniteFiniteSmoothFunctions K n

/-- The type of complex algebra actions on the actual center-finite space. -/
abbrev CenterFiniteDifferentialAction :=
    ArchimedeanGL.EnvelopingAlgebra K n →ₐ[ℂ]
      Module.End ℂ (CenterFiniteFiniteSmoothRationalFunctions K n)

/-- Restrict the genuine enveloping action to the simultaneous center-finite space. -/
def centerFiniteEnvelopingAction : CenterFiniteDifferentialAction K n where
  toFun a := (finiteSmoothEnvelopingAction K n a).restrict
    fun _ hf => isCenterFinite_finiteSmoothEnvelopingAction K n a hf
  map_zero' := by
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    exact LinearMap.congr_fun (map_zero (finiteSmoothEnvelopingAction K n)) f.val
  map_one' := by
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    exact LinearMap.congr_fun (map_one (finiteSmoothEnvelopingAction K n)) f.val
  map_add' a b := by
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    exact LinearMap.congr_fun (map_add (finiteSmoothEnvelopingAction K n) a b) f.val
  map_mul' a b := by
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    exact LinearMap.congr_fun (map_mul (finiteSmoothEnvelopingAction K n) a b) f.val
  commutes' c := by
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    exact LinearMap.congr_fun ((finiteSmoothEnvelopingAction K n).commutes c) f.val

@[simp]
theorem centerFiniteEnvelopingAction_val (a : ArchimedeanGL.EnvelopingAlgebra K n)
    (f : CenterFiniteFiniteSmoothRationalFunctions K n) :
    (centerFiniteEnvelopingAction K n a f).val =
      finiteSmoothEnvelopingAction K n a f.val := rfl

end Langlands.Automorphic
