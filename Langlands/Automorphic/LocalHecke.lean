import Langlands.Automorphic.LocalAction
import Langlands.Automorphic.FiniteHecke

/-! # Actual finite local Hecke operators on automorphic forms -/

noncomputable section
universe u

namespace Langlands.Automorphic

open Langlands.Global NumberField ContinuousRationalFunctions
open MeasureTheory Langlands.Hecke

variable (K : Type u) [Field K] [NumberField K] (n : ℕ)

local instance localHeckeRationalAddCommGroup : AddCommGroup (RationalInvariantFunctions K n) := Submodule.addCommGroup _
local instance localHeckeContinuousAddCommGroup : AddCommGroup (ContinuousRationalFunctions K n) := Submodule.addCommGroup _
local instance localHeckeSmoothAddCommGroup : AddCommGroup (FiniteSmoothRationalFunctions K n) := Submodule.addCommGroup _
local instance localHeckeFormsAddCommGroup : AddCommGroup (AutomorphicForms K n) := Submodule.addCommGroup _

variable (v : Langlands.Global.FinitePlace K)
variable [MeasurableSpace (FiniteLocalGL K n v)] [BorelSpace (FiniteLocalGL K n v)]
variable (μ : Measure (FiniteLocalGL K n v)) [μ.IsHaarMeasure]

/-- The type of actual local Hecke actions on all automorphic forms. -/
abbrev AutomorphicLocalHeckeAction :=
  HeckeAlgebra μ →ₙₐ[ℂ] Module.End ℂ (AutomorphicForms K n)

/-- Integrate the smooth action of the actual local matrix group. -/
def automorphicLocalHeckeAction : AutomorphicLocalHeckeAction K n v μ :=
  Hecke.heckeAction μ (automorphicLocalRightAction K n v)
    (automorphicLocalRightAction_isSmooth K n v)

/-- Scalar evaluation is the genuine local right-translation integral. -/
theorem evaluate_automorphicLocalHeckeAction (h : HeckeAlgebra μ)
    (f : AutomorphicForms K n) (x : AdelicGL K n) :
    evaluate K n (automorphicToContinuous K n (automorphicLocalHeckeAction K n v μ h f)) x =
      ∫ g, h g * evaluate K n (automorphicToContinuous K n f)
        (x * AdelicGL.ofFinite K n (FiniteAdelicGL.localInclusion K n v g)) ∂μ :=
  Hecke.integratedAction_dual μ (automorphicLocalRightAction K n v)
    (automorphicLocalRightAction_isSmooth K n v) h f (automorphicEvaluation K n x)

/-- The genuine unital local corner acts on the existing local fixed-vector space. -/
def automorphicLocalHeckeCornerAction (L : OpenSubgroup (FiniteLocalGL K n v))
    (hL : IsCompact (L : Set (FiniteLocalGL K n v))) :
    HeckeAlgebra.Corner μ L hL →ₐ[ℂ]
      Module.End ℂ (Langlands.fixedVectors (automorphicLocalRightAction K n v) L.toSubgroup) :=
  Hecke.cornerAction μ (automorphicLocalRightAction K n v)
    (automorphicLocalRightAction_isSmooth K n v) L hL

/-- Compact-open averaging fixes exactly the corresponding local fixed vectors. -/
theorem automorphicLocalHeckeAction_normalizedIndicator_eq_self_iff
    (L : OpenSubgroup (FiniteLocalGL K n v))
    (hL : IsCompact (L : Set (FiniteLocalGL K n v))) (f : AutomorphicForms K n) :
    automorphicLocalHeckeAction K n v μ (HeckeAlgebra.normalizedIndicator μ L hL) f = f ↔
      f ∈ Langlands.fixedVectors (automorphicLocalRightAction K n v) L.toSubgroup := by
  constructor
  · intro hf
    rw [← hf]
    exact Hecke.heckeAction_normalizedIndicator_mem μ (automorphicLocalRightAction K n v)
      (automorphicLocalRightAction_isSmooth K n v) L hL f
  · exact Hecke.heckeAction_normalizedIndicator_of_fixed μ (automorphicLocalRightAction K n v)
      (automorphicLocalRightAction_isSmooth K n v) L hL

/-- Intersect the open stabilizer with the actual compact open integral subgroup. -/
theorem automorphicLocalHeckeAction_exists_localUnit (f : AutomorphicForms K n) :
    ∃ (L : OpenSubgroup (FiniteLocalGL K n v))
      (hL : IsCompact (L : Set (FiniteLocalGL K n v))),
      automorphicLocalHeckeAction K n v μ (HeckeAlgebra.normalizedIndicator μ L hL) f = f := by
  obtain ⟨U, hU⟩ := automorphicLocalRightAction_isSmooth K n v f
  let L := FiniteAdelicGL.localIntegral K n v ⊓ U
  have hL : IsCompact (L : Set (FiniteLocalGL K n v)) :=
    (FiniteAdelicGL.isCompact_localIntegral K n v).inter_right U.isClosed
  refine ⟨L, hL, ?_⟩
  apply (automorphicLocalHeckeAction_normalizedIndicator_eq_self_iff K n v μ L hL f).mpr
  exact fun g => hU ⟨g, g.property.2⟩

theorem automorphicLocalHeckeAction_nondegenerate (f : AutomorphicForms K n)
    (hf : ∀ h : HeckeAlgebra μ, automorphicLocalHeckeAction K n v μ h f = 0) : f = 0 := by
  obtain ⟨L, hL, h⟩ := automorphicLocalHeckeAction_exists_localUnit K n v μ f
  rw [← h, hf]

/-- The local integral corner on actual spherical vectors, with no Satake assertion. -/
abbrev automorphicLocalSphericalAction :=
  automorphicLocalHeckeCornerAction K n v μ (FiniteAdelicGL.localIntegral K n v)
    (FiniteAdelicGL.isCompact_localIntegral K n v)

variable (S : Subrepresentation (continuousRightAction K n))

local instance localHeckeRestrictedAddCommGroup : AddCommGroup (RestrictedAutomorphicForms K n S) := Submodule.addCommGroup _

/-- Integrate the inherited local action on an actual invariant restriction of forms. -/
def restrictedAutomorphicLocalHeckeAction :
    HeckeAlgebra μ →ₙₐ[ℂ] Module.End ℂ (RestrictedAutomorphicForms K n S) :=
  Hecke.heckeAction μ (restrictedAutomorphicLocalRightAction K n S v)
    (restrictedAutomorphicLocalRightAction_isSmooth K n S v)

theorem restrictedAutomorphicLocalInclusion_heckeAction (h : HeckeAlgebra μ)
    (f : RestrictedAutomorphicForms K n S) :
    restrictedAutomorphicLocalInclusion K n S v
        (restrictedAutomorphicLocalHeckeAction K n v μ S h f) =
      automorphicLocalHeckeAction K n v μ h (restrictedAutomorphicLocalInclusion K n S v f) :=
  Hecke.integratedAction_intertwiner μ
    (restrictedAutomorphicLocalRightAction_isSmooth K n S v)
    (automorphicLocalRightAction_isSmooth K n v)
    (restrictedAutomorphicLocalInclusion K n S v) h f

theorem evaluate_restrictedAutomorphicLocalHeckeAction (h : HeckeAlgebra μ)
    (f : RestrictedAutomorphicForms K n S) (x : AdelicGL K n) :
    evaluate K n (restrictedAutomorphicToContinuous K n S
        (restrictedAutomorphicLocalHeckeAction K n v μ S h f)) x =
      ∫ g, h g * evaluate K n (restrictedAutomorphicToContinuous K n S f)
        (x * AdelicGL.ofFinite K n (FiniteAdelicGL.localInclusion K n v g)) ∂μ := by
  change automorphicEvaluation K n x
    (restrictedAutomorphicLocalInclusion K n S v
      (restrictedAutomorphicLocalHeckeAction K n v μ S h f)) = _
  rw [restrictedAutomorphicLocalInclusion_heckeAction]
  exact evaluate_automorphicLocalHeckeAction K n v μ h f.val x

/-- Restricted forms inherit the same actual compact-open local units. -/
theorem restrictedAutomorphicLocalHeckeAction_exists_localUnit
    (f : RestrictedAutomorphicForms K n S) :
    ∃ (L : OpenSubgroup (FiniteLocalGL K n v))
      (hL : IsCompact (L : Set (FiniteLocalGL K n v))),
      restrictedAutomorphicLocalHeckeAction K n v μ S
        (HeckeAlgebra.normalizedIndicator μ L hL) f = f := by
  obtain ⟨L, hL, hf⟩ := automorphicLocalHeckeAction_exists_localUnit K n v μ f.val
  refine ⟨L, hL, ?_⟩
  apply restrictedAutomorphicLocalInclusion_injective K n S v
  rw [restrictedAutomorphicLocalInclusion_heckeAction]
  exact hf

theorem restrictedAutomorphicLocalHeckeAction_nondegenerate
    (f : RestrictedAutomorphicForms K n S)
    (hf : ∀ h : HeckeAlgebra μ, restrictedAutomorphicLocalHeckeAction K n v μ S h f = 0) :
    f = 0 := by
  obtain ⟨L, hL, h⟩ := restrictedAutomorphicLocalHeckeAction_exists_localUnit K n v μ S f
  rw [← h, hf]

/-- The genuine local corner also acts on the restricted form space's local fixed vectors. -/
def restrictedAutomorphicLocalHeckeCornerAction
    (L : OpenSubgroup (FiniteLocalGL K n v))
    (hL : IsCompact (L : Set (FiniteLocalGL K n v))) :
    HeckeAlgebra.Corner μ L hL →ₐ[ℂ] Module.End ℂ
      (Langlands.fixedVectors (restrictedAutomorphicLocalRightAction K n S v) L.toSubgroup) :=
  Hecke.cornerAction μ (restrictedAutomorphicLocalRightAction K n S v)
    (restrictedAutomorphicLocalRightAction_isSmooth K n S v) L hL

section DistinctPlaces
variable (w : Langlands.Global.FinitePlace K) (hvw : v ≠ w)
include hvw

omit [MeasurableSpace (FiniteLocalGL K n v)] [BorelSpace (FiniteLocalGL K n v)] in
/-- Translation at the other place is an intertwiner of the first local action. -/
def automorphicOtherPlaceIntertwiner (g : FiniteLocalGL K n w) :
    (automorphicLocalRightAction K n v).IntertwiningMap
      (automorphicLocalRightAction K n v) where
  toLinearMap := automorphicLocalRightAction K n w g
  isIntertwining' g' :=
    (automorphicLocalRightAction_commute K n w v hvw.symm g g').eq

theorem automorphicOtherPlace_localHeckeAction (g : FiniteLocalGL K n w)
    (h : HeckeAlgebra μ) (f : AutomorphicForms K n) :
    automorphicLocalRightAction K n w g (automorphicLocalHeckeAction K n v μ h f) =
      automorphicLocalHeckeAction K n v μ h (automorphicLocalRightAction K n w g f) :=
  Hecke.integratedAction_intertwiner μ
    (automorphicLocalRightAction_isSmooth K n v)
    (automorphicLocalRightAction_isSmooth K n v)
    (automorphicOtherPlaceIntertwiner K n v w hvw g) h f

/-- A local Hecke operator intertwines every distinct-place local action. -/
def automorphicLocalHeckeOtherPlaceIntertwiner (h : HeckeAlgebra μ) :
    (automorphicLocalRightAction K n w).IntertwiningMap
      (automorphicLocalRightAction K n w) where
  toLinearMap := automorphicLocalHeckeAction K n v μ h
  isIntertwining' g := by
    apply LinearMap.ext
    intro f
    exact (automorphicOtherPlace_localHeckeAction K n v μ w hvw g h f).symm

variable [MeasurableSpace (FiniteLocalGL K n w)] [BorelSpace (FiniteLocalGL K n w)]
variable (ν : Measure (FiniteLocalGL K n w)) [ν.IsHaarMeasure]

/-- Hecke operators integrated at distinct finite places commute. -/
theorem automorphicLocalHeckeAction_commute (h : HeckeAlgebra μ) (h' : HeckeAlgebra ν) :
    Commute (automorphicLocalHeckeAction K n v μ h)
      (automorphicLocalHeckeAction K n w ν h') := by
  apply LinearMap.ext
  intro f
  exact Hecke.integratedAction_intertwiner ν
    (automorphicLocalRightAction_isSmooth K n w)
    (automorphicLocalRightAction_isSmooth K n w)
    (automorphicLocalHeckeOtherPlaceIntertwiner K n v μ w hvw h) h' f

end DistinctPlaces
end Langlands.Automorphic
