import Langlands.Automorphic.FiniteDifferential
import Langlands.Representation.Hecke.CornerAction

/-! # Commuting actual Hecke and enveloping actions -/

noncomputable section
universe u

namespace Langlands.Automorphic

open Langlands.Global NumberField ContinuousRationalFunctions
open MeasureTheory Langlands.Hecke

variable (K : Type u) [Field K] [NumberField K] (n : ℕ)

local instance heckeDifferentialRationalAddCommGroup : AddCommGroup (RationalInvariantFunctions K n) := Submodule.addCommGroup _
local instance heckeDifferentialContinuousAddCommGroup : AddCommGroup (ContinuousRationalFunctions K n) := Submodule.addCommGroup _
local instance heckeDifferentialSmoothAddCommGroup : AddCommGroup (FiniteSmoothRationalFunctions K n) := Submodule.addCommGroup _
local instance heckeDifferentialCenterFiniteAddCommGroup : AddCommGroup (CenterFiniteFiniteSmoothRationalFunctions K n) :=
  Submodule.addCommGroup _

/-- The actual finite action is smooth by the common open stabilizer condition. -/
theorem finiteSmoothFiniteRightAction_isSmooth :
    Langlands.IsSmooth (finiteSmoothFiniteRightAction K n) := by
  intro f
  obtain ⟨L, hL⟩ := f.property.2
  refine ⟨L, ?_⟩
  intro l
  apply Subtype.ext
  exact hL l

/-- Each genuine differential operator intertwines finite right translations. -/
def finiteSmoothDifferentialFiniteIntertwiner (a : ArchimedeanGL.EnvelopingAlgebra K n) :
    (finiteSmoothFiniteRightAction K n).IntertwiningMap
      (finiteSmoothFiniteRightAction K n) where
  toLinearMap := finiteSmoothEnvelopingAction K n a
  isIntertwining' d := by
    apply LinearMap.ext
    intro f
    exact (finiteSmoothFiniteRightAction_envelopingAction K n d a f).symm

section Hecke
variable [MeasurableSpace (FiniteAdelicGL K n)] [BorelSpace (FiniteAdelicGL K n)]
variable (μ : Measure (FiniteAdelicGL K n)) [μ.IsHaarMeasure]

/-- Type of the actual finite Hecke action on finite-smooth functions. -/
abbrev FiniteSmoothHeckeAction :=
  HeckeAlgebra μ →ₙₐ[ℂ] Module.End ℂ (FiniteSmoothRationalFunctions K n)

/-- Integrate actual finite right translation on finite-smooth adelic functions. -/
def finiteSmoothHeckeAction : FiniteSmoothHeckeAction K n μ :=
  Hecke.heckeAction μ (finiteSmoothFiniteRightAction K n)
    (finiteSmoothFiniteRightAction_isSmooth K n)

/-- Finite Hecke integration commutes with every actual enveloping differential. -/
theorem finiteSmoothEnvelopingAction_heckeAction
    (a : ArchimedeanGL.EnvelopingAlgebra K n) (h : HeckeAlgebra μ)
    (f : FiniteSmoothRationalFunctions K n) :
    finiteSmoothEnvelopingAction K n a (finiteSmoothHeckeAction K n μ h f) =
      finiteSmoothHeckeAction K n μ h (finiteSmoothEnvelopingAction K n a f) :=
  Hecke.integratedAction_intertwiner μ
    (finiteSmoothFiniteRightAction_isSmooth K n)
    (finiteSmoothFiniteRightAction_isSmooth K n)
    (finiteSmoothDifferentialFiniteIntertwiner K n a) h f

/-- The Hecke operator has the usual scalar integral formula on actual functions. -/
theorem evaluate_finiteSmoothHeckeAction (h : HeckeAlgebra μ)
    (f : FiniteSmoothRationalFunctions K n) (x : AdelicGL K n) :
    evaluate K n (finiteSmoothHeckeAction K n μ h f).val x =
      ∫ d, h d * evaluate K n f.val (x * AdelicGL.ofFinite K n d) ∂μ :=
  Hecke.integratedAction_dual μ (finiteSmoothFiniteRightAction K n)
    (finiteSmoothFiniteRightAction_isSmooth K n) h f
    { toFun := fun F => evaluate K n F.val x
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

/-- Type of the actual finite Hecke action on simultaneous center-finite functions. -/
abbrev CenterFiniteHeckeAction :=
  HeckeAlgebra μ →ₙₐ[ℂ] Module.End ℂ (CenterFiniteFiniteSmoothRationalFunctions K n)

/-- The actual finite Hecke action on simultaneous center-finite functions. -/
def centerFiniteHeckeAction : CenterFiniteHeckeAction K n μ :=
  Hecke.heckeAction μ (centerFiniteFiniteSmoothRightAction K n)
    (centerFiniteFiniteSmoothRightAction_isSmooth K n)

/-- The faithful inclusion realizes the restricted Hecke operator in the ambient space. -/
theorem centerFiniteFiniteSmoothInclusion_heckeAction (h : HeckeAlgebra μ)
    (f : CenterFiniteFiniteSmoothRationalFunctions K n) :
    centerFiniteFiniteSmoothInclusion K n (centerFiniteHeckeAction K n μ h f) =
      finiteSmoothHeckeAction K n μ h (centerFiniteFiniteSmoothInclusion K n f) :=
  Hecke.integratedAction_intertwiner μ
    (centerFiniteFiniteSmoothRightAction_isSmooth K n)
    (finiteSmoothFiniteRightAction_isSmooth K n)
    (centerFiniteFiniteSmoothInclusion K n) h f

/-- Both actions commute on the actual simultaneous center-finite space. -/
theorem centerFiniteEnvelopingAction_heckeAction
    (a : ArchimedeanGL.EnvelopingAlgebra K n) (h : HeckeAlgebra μ)
    (f : CenterFiniteFiniteSmoothRationalFunctions K n) :
    centerFiniteEnvelopingAction K n a (centerFiniteHeckeAction K n μ h f) =
      centerFiniteHeckeAction K n μ h (centerFiniteEnvelopingAction K n a f) :=
  Hecke.integratedAction_intertwiner μ
    (centerFiniteFiniteSmoothRightAction_isSmooth K n)
    (centerFiniteFiniteSmoothRightAction_isSmooth K n)
    (centerFiniteDifferentialFiniteIntertwiner K n a) h f

/-- A finite Hecke operator retains every common central annihilator of all slices. -/
theorem centerFamilyAnnihilator_le_heckeAction (h : HeckeAlgebra μ)
    (f : FiniteSmoothRationalFunctions K n) :
    centerFamilyAnnihilator K n (finiteSmoothCenterSlices K n f) ≤
      centerFamilyAnnihilator K n
        (finiteSmoothCenterSlices K n (finiteSmoothHeckeAction K n μ h f)) := by
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
  rw [finiteSmoothCenterSlices_apply, ← finiteSmoothSlice_centerAction]
  change finiteSmoothSlice K n b
    (finiteSmoothEnvelopingAction K n (ArchimedeanGL.centerInclusion K n z)
      (finiteSmoothHeckeAction K n μ h f)) = 0
  rw [finiteSmoothEnvelopingAction_heckeAction]
  change finiteSmoothSlice K n b (finiteSmoothHeckeAction K n μ h
    (finiteSmoothCenterAction K n z f)) = 0
  rw [hzero, map_zero, map_zero]

end Hecke

/-- Existing fixed vectors for a subgroup of the finite adelic group. -/
abbrev CenterFiniteFixedVectors (L : Subgroup (FiniteAdelicGL K n)) :=
  fixedVectors (centerFiniteFiniteSmoothRightAction K n) L

/-- Type of the genuine enveloping action at a fixed finite level. -/
abbrev CenterFiniteFixedEnvelopingAction (L : Subgroup (FiniteAdelicGL K n)) :=
  ArchimedeanGL.EnvelopingAlgebra K n →ₐ[ℂ]
    Module.End ℂ (CenterFiniteFixedVectors K n L)

/-- The actual enveloping action on existing fixed vectors for any finite adelic subgroup. -/
def centerFiniteFixedEnvelopingAction (L : Subgroup (FiniteAdelicGL K n)) :
    CenterFiniteFixedEnvelopingAction K n L where
  toFun a := fixedVectorsMap (centerFiniteDifferentialFiniteIntertwiner K n a) L
  map_zero' := by
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    exact LinearMap.congr_fun (map_zero (centerFiniteEnvelopingAction K n)) f.val
  map_one' := by
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    exact LinearMap.congr_fun (map_one (centerFiniteEnvelopingAction K n)) f.val
  map_add' a b := by
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    exact LinearMap.congr_fun (map_add (centerFiniteEnvelopingAction K n) a b) f.val
  map_mul' a b := by
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    exact LinearMap.congr_fun (map_mul (centerFiniteEnvelopingAction K n) a b) f.val
  commutes' c := by
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    exact LinearMap.congr_fun ((centerFiniteEnvelopingAction K n).commutes c) f.val

@[simp]
theorem centerFiniteFixedEnvelopingAction_val (L : Subgroup (FiniteAdelicGL K n))
    (a : ArchimedeanGL.EnvelopingAlgebra K n)
    (f : fixedVectors (centerFiniteFiniteSmoothRightAction K n) L) :
    (centerFiniteFixedEnvelopingAction K n L a f).val =
      centerFiniteEnvelopingAction K n a f.val := rfl

section Corner
variable [MeasurableSpace (FiniteAdelicGL K n)] [BorelSpace (FiniteAdelicGL K n)]
variable (μ : Measure (FiniteAdelicGL K n)) [μ.IsHaarMeasure]
variable (L : OpenSubgroup (FiniteAdelicGL K n))
variable (hL : IsCompact (L : Set (FiniteAdelicGL K n)))

/-- Type of the unital finite Hecke corner action at a fixed finite level. -/
abbrev CenterFiniteHeckeCornerAction :=
  HeckeAlgebra.Corner μ L hL →ₐ[ℂ]
    Module.End ℂ (CenterFiniteFixedVectors K n L.toSubgroup)

/-- The unital finite Hecke corner acts on these same actual fixed vectors. -/
def centerFiniteHeckeCornerAction : CenterFiniteHeckeCornerAction K n μ L hL :=
  Hecke.cornerAction μ (centerFiniteFiniteSmoothRightAction K n)
    (centerFiniteFiniteSmoothRightAction_isSmooth K n) L hL

/-- The unital fixed-level Hecke and enveloping actions commute. -/
theorem centerFiniteFixedEnvelopingAction_heckeCornerAction
    (a : ArchimedeanGL.EnvelopingAlgebra K n) (h : HeckeAlgebra.Corner μ L hL)
    (f : fixedVectors (centerFiniteFiniteSmoothRightAction K n) L.toSubgroup) :
    centerFiniteFixedEnvelopingAction K n L.toSubgroup a
        (centerFiniteHeckeCornerAction K n μ L hL h f) =
      centerFiniteHeckeCornerAction K n μ L hL h
        (centerFiniteFixedEnvelopingAction K n L.toSubgroup a f) :=
  Hecke.cornerAction_intertwiner μ (centerFiniteFiniteSmoothRightAction K n)
    (centerFiniteFiniteSmoothRightAction_isSmooth K n) L hL
    (centerFiniteFiniteSmoothRightAction_isSmooth K n)
    (centerFiniteDifferentialFiniteIntertwiner K n a) h f

end Corner
end Langlands.Automorphic
