import Langlands.Automorphic.CuspidalForms
import Langlands.Representation.Hecke.CornerAction

/-! # Actual finite Hecke operators on automorphic forms -/

noncomputable section
universe u

namespace Langlands.Automorphic

open Langlands.Global NumberField ContinuousRationalFunctions
open MeasureTheory Langlands.Hecke

variable (K : Type u) [Field K] [NumberField K] (n : ℕ)

local instance : AddCommGroup (RationalInvariantFunctions K n) := Submodule.addCommGroup _
local instance : AddCommGroup (ContinuousRationalFunctions K n) := Submodule.addCommGroup _
local instance : AddCommGroup (FiniteSmoothRationalFunctions K n) := Submodule.addCommGroup _
local instance : AddCommGroup (AutomorphicForms K n) := Submodule.addCommGroup _

variable [MeasurableSpace (FiniteAdelicGL K n)] [BorelSpace (FiniteAdelicGL K n)]
variable (μ : Measure (FiniteAdelicGL K n)) [μ.IsHaarMeasure]

/-- The type of finite Hecke actions on the actual automorphic form space. -/
abbrev AutomorphicHeckeAction :=
  HeckeAlgebra μ →ₙₐ[ℂ] Module.End ℂ (AutomorphicForms K n)

/-- Integrate the actual smooth finite right action, with the supplied left Haar measure. -/
def automorphicHeckeAction : AutomorphicHeckeAction K n μ :=
  Hecke.heckeAction μ (automorphicFiniteRightAction K n)
    (automorphicFiniteRightAction_isSmooth K n)

/-- Evaluation at an actual adelic point, as an algebraic linear functional. -/
def automorphicEvaluation (x : AdelicGL K n) : AutomorphicForms K n →ₗ[ℂ] ℂ where
  toFun f := evaluate K n (automorphicToContinuous K n f) x
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The operator is the usual positive right-translation integral on actual functions. -/
theorem evaluate_automorphicHeckeAction (h : HeckeAlgebra μ)
    (f : AutomorphicForms K n) (x : AdelicGL K n) :
    evaluate K n (automorphicToContinuous K n (automorphicHeckeAction K n μ h f)) x =
      ∫ d, h d * evaluate K n (automorphicToContinuous K n f)
        (x * AdelicGL.ofFinite K n d) ∂μ :=
  Hecke.integratedAction_dual μ (automorphicFiniteRightAction K n)
    (automorphicFiniteRightAction_isSmooth K n) h f (automorphicEvaluation K n x)

omit [MeasurableSpace (FiniteAdelicGL K n)] [BorelSpace (FiniteAdelicGL K n)] in
/-- Fixed vectors in the actual form space agree with the previously defined finite level. -/
theorem mem_automorphicFixedVectors (L : Subgroup (FiniteAdelicGL K n))
    (f : AutomorphicForms K n) :
    f ∈ fixedVectors (automorphicFiniteRightAction K n) L ↔
      automorphicToContinuous K n f ∈ levelSubmodule K n L := by
  constructor
  · intro hf l
    exact congrArg (automorphicToContinuous K n) (hf l)
  · intro hf l
    exact automorphicToContinuous_injective K n (hf l)

/-- The genuine unital Hecke corner acts on the existing finite-level automorphic forms. -/
def automorphicHeckeCornerAction (L : OpenSubgroup (FiniteAdelicGL K n))
    (hL : IsCompact (L : Set (FiniteAdelicGL K n))) :
    HeckeAlgebra.Corner μ L hL →ₐ[ℂ]
      Module.End ℂ (fixedVectors (automorphicFiniteRightAction K n) L.toSubgroup) :=
  Hecke.cornerAction μ (automorphicFiniteRightAction K n)
    (automorphicFiniteRightAction_isSmooth K n) L hL

/-- The normalized indicator fixes exactly the forms of the indicated finite level. -/
theorem automorphicHeckeAction_normalizedIndicator_eq_self_iff
    (L : OpenSubgroup (FiniteAdelicGL K n))
    (hL : IsCompact (L : Set (FiniteAdelicGL K n))) (f : AutomorphicForms K n) :
    automorphicHeckeAction K n μ (HeckeAlgebra.normalizedIndicator μ L hL) f = f ↔
      automorphicToContinuous K n f ∈ levelSubmodule K n L.toSubgroup := by
  rw [← mem_automorphicFixedVectors]
  constructor
  · intro hf
    rw [← hf]
    exact Hecke.heckeAction_normalizedIndicator_mem μ (automorphicFiniteRightAction K n)
      (automorphicFiniteRightAction_isSmooth K n) L hL f
  · exact Hecke.heckeAction_normalizedIndicator_of_fixed μ (automorphicFiniteRightAction K n)
      (automorphicFiniteRightAction_isSmooth K n) L hL

/-- Actual compact finite level supplies a normalized local unit for each form. -/
theorem automorphicHeckeAction_exists_localUnit (f : AutomorphicForms K n) :
    ∃ (L : OpenSubgroup (FiniteAdelicGL K n))
      (hL : IsCompact (L : Set (FiniteAdelicGL K n))),
      automorphicHeckeAction K n μ (HeckeAlgebra.normalizedIndicator μ L hL) f = f := by
  have hf := ((mem_automorphicSubrepresentation K n f.val).mp f.property).1
  obtain ⟨L, ho, hc, hfix⟩ := hf
  exact ⟨⟨L, ho⟩, hc,
    (automorphicHeckeAction_normalizedIndicator_eq_self_iff K n μ ⟨L, ho⟩ hc f).mpr hfix⟩

/-- All finite Hecke operators together detect a nonzero automorphic form. -/
theorem automorphicHeckeAction_nondegenerate (f : AutomorphicForms K n)
    (hf : ∀ h : HeckeAlgebra μ, automorphicHeckeAction K n μ h f = 0) : f = 0 := by
  obtain ⟨L, hL, h⟩ := automorphicHeckeAction_exists_localUnit K n μ f
  rw [← h, hf]

variable (S : Subrepresentation (continuousRightAction K n))

local instance : AddCommGroup (RestrictedAutomorphicForms K n S) := Submodule.addCommGroup _

/-- Finite Hecke operators on an actual invariant restriction of the form space. -/
def restrictedAutomorphicHeckeAction :
    HeckeAlgebra μ →ₙₐ[ℂ] Module.End ℂ (RestrictedAutomorphicForms K n S) :=
  Hecke.heckeAction μ (restrictedAutomorphicFiniteRightAction K n S)
    (restrictedAutomorphicFiniteRightAction_isSmooth K n S)

/-- The faithful inclusion intertwines the genuine integrated operators. -/
theorem restrictedAutomorphicInclusion_heckeAction (h : HeckeAlgebra μ)
    (f : RestrictedAutomorphicForms K n S) :
    restrictedAutomorphicInclusion K n S (restrictedAutomorphicHeckeAction K n μ S h f) =
      automorphicHeckeAction K n μ h (restrictedAutomorphicInclusion K n S f) :=
  Hecke.integratedAction_intertwiner μ
    (restrictedAutomorphicFiniteRightAction_isSmooth K n S)
    (automorphicFiniteRightAction_isSmooth K n)
    (restrictedAutomorphicInclusion K n S) h f

/-- Restricted operators have the same right-translation integral formula. -/
theorem evaluate_restrictedAutomorphicHeckeAction (h : HeckeAlgebra μ)
    (f : RestrictedAutomorphicForms K n S) (x : AdelicGL K n) :
    evaluate K n (restrictedAutomorphicToContinuous K n S
      (restrictedAutomorphicHeckeAction K n μ S h f)) x =
      ∫ d, h d * evaluate K n (restrictedAutomorphicToContinuous K n S f)
        (x * AdelicGL.ofFinite K n d) ∂μ := by
  change automorphicEvaluation K n x
    (restrictedAutomorphicInclusion K n S (restrictedAutomorphicHeckeAction K n μ S h f)) = _
  rw [restrictedAutomorphicInclusion_heckeAction]
  exact evaluate_automorphicHeckeAction K n μ h f.val x

/-- The same normalized local units work in each actual invariant restriction. -/
theorem restrictedAutomorphicHeckeAction_exists_localUnit
    (f : RestrictedAutomorphicForms K n S) :
    ∃ (L : OpenSubgroup (FiniteAdelicGL K n))
      (hL : IsCompact (L : Set (FiniteAdelicGL K n))),
      restrictedAutomorphicHeckeAction K n μ S
        (HeckeAlgebra.normalizedIndicator μ L hL) f = f := by
  obtain ⟨L, hL, hf⟩ := automorphicHeckeAction_exists_localUnit K n μ f.val
  refine ⟨L, hL, ?_⟩
  apply restrictedAutomorphicInclusion_injective K n S
  rw [restrictedAutomorphicInclusion_heckeAction]
  exact hf

/-- The restricted finite Hecke action is nondegenerate. -/
theorem restrictedAutomorphicHeckeAction_nondegenerate
    (f : RestrictedAutomorphicForms K n S)
    (hf : ∀ h : HeckeAlgebra μ, restrictedAutomorphicHeckeAction K n μ S h f = 0) :
    f = 0 := by
  obtain ⟨L, hL, h⟩ := restrictedAutomorphicHeckeAction_exists_localUnit K n μ S f
  rw [← h, hf]

/-- Finite Hecke action on forms with the specified idele-class central character. -/
abbrev centralCharacterAutomorphicHeckeAction (χ : IdeleClassGroup (𝓞 K) K →ₜ* ℂˣ) :=
  restrictedAutomorphicHeckeAction K n μ (centralCharacterSubrepresentation K n χ)

section Cuspidal
variable [CompactSpace (AdeleQuotient K)]

/-- Finite Hecke action on actual cusp forms. -/
abbrev cuspidalAutomorphicHeckeAction :=
  restrictedAutomorphicHeckeAction K n μ (cuspidalSubrepresentation (K := K) (n := n))

/-- The type of finite Hecke actions on the specified-character cusp space. -/
abbrev CentralCharacterCuspidalHeckeAction (χ : IdeleClassGroup (𝓞 K) K →ₜ* ℂˣ) :=
  HeckeAlgebra μ →ₙₐ[ℂ] Module.End ℂ (CentralCharacterCuspidalForms K n χ)

/-- Finite Hecke action on cusp forms with the specified central character. -/
abbrev centralCharacterCuspidalHeckeAction (χ : IdeleClassGroup (𝓞 K) K →ₜ* ℂˣ) :
    CentralCharacterCuspidalHeckeAction K n μ χ :=
  restrictedAutomorphicHeckeAction K n μ
    (centralCharacterSubrepresentation K n χ ⊓
      cuspidalSubrepresentation (K := K) (n := n))

end Cuspidal
end Langlands.Automorphic
