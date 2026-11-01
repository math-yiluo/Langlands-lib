import Langlands.Automorphic.OperatorSubquotient

/-! # Actual presentations for images of whole-operator quotient maps -/

noncomputable section
universe uF uV
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Automorphic

open Langlands.Global

variable {F : Type uF} [Field F] [NumberField F] {n : ℕ}

local instance imageRationalGroup : AddCommGroup (RationalInvariantFunctions F n) :=
  Submodule.addCommGroup _
local instance imageContinuousGroup : AddCommGroup (ContinuousRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance imageSmoothGroup : AddCommGroup (FiniteSmoothRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance imageFormGroup : AddCommGroup (AutomorphicForms F n) :=
  Submodule.addCommGroup _
local instance imageStableGroup : AddCommGroup (StableAutomorphicFunctions F n) :=
  Submodule.addCommGroup _
local instance imageRealizationGroup (S : OperatorRealization F n) :
    AddCommGroup S.Space := Submodule.addCommGroup _

namespace OperatorSubquotient

variable (Q : OperatorSubquotient F n)
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {ρ : Representation ℂ (automorphicOperatorAlgebra F n) V}
  (L : Q.representation.IntertwiningMap ρ)

/-- Retain the actual numerator and divide by the kernel of the composite map. -/
def imagePresentation : OperatorSubquotient F n :=
  ⟨Q.upper, (L.comp Q.projection).ker⟩

@[simp] theorem mem_imagePresentation_lower (f : Q.upper.Space) :
    f ∈ (Q.imagePresentation L).lower ↔ L (Q.projection f) = 0 := Iff.rfl

theorem lower_le_imagePresentation_lower :
    Q.lower ≤ (Q.imagePresentation L).lower := by
  intro f hf
  change L (Q.projection f) = 0
  rw [(Q.projection_eq_zero_iff f).mpr hf, map_zero]

/-- The original quotient maps canonically onto the new actual image presentation. -/
def imageProjection :
    Q.representation.IntertwiningMap (Q.imagePresentation L).representation :=
  Q.lift (Q.imagePresentation L).projection (by
    intro f hf
    change (Q.imagePresentation L).projection f = 0
    exact ((Q.imagePresentation L).projection_eq_zero_iff f).mpr
      (Q.lower_le_imagePresentation_lower L hf))

@[simp] theorem imageProjection_projection (f : Q.upper.Space) :
    Q.imageProjection L (Q.projection f) = (Q.imagePresentation L).projection f := rfl

theorem imageProjection_surjective : Function.Surjective (Q.imageProjection L) := by
  intro v
  obtain ⟨f, hfv⟩ := (Q.imagePresentation L).projection_surjective v
  exact ⟨Q.projection f, hfv⟩

@[simp] theorem imageProjection_eq_zero_iff (v : Q.Space) :
    Q.imageProjection L v = 0 ↔ L v = 0 := by
  obtain ⟨f, hfv⟩ := Q.projection_surjective v
  have hf : (Q.imagePresentation L).projection f = 0 ↔ L (Q.projection f) = 0 :=
    ((Q.imagePresentation L).projection_eq_zero_iff f).trans
      (Q.mem_imagePresentation_lower L f)
  have hf' : Q.imageProjection L (Q.projection f) = 0 ↔ L (Q.projection f) = 0 := hf
  exact Eq.mp (congrArg
    (fun w : Q.Space => Q.imageProjection L w = 0 ↔ L w = 0) hfv) hf'

@[simp] theorem imageProjection_ker : (Q.imageProjection L).ker = L.ker := by
  apply Subrepresentation.toSubmodule_injective
  apply Submodule.ext
  exact Q.imageProjection_eq_zero_iff L

/-- The map from the new quotient into the original target is always injective. -/
def imageInclusion : (Q.imagePresentation L).representation.IntertwiningMap ρ :=
  (Q.imagePresentation L).lift (L.comp Q.projection) le_rfl

@[simp] theorem imageInclusion_projection (f : Q.upper.Space) :
    Q.imageInclusion L ((Q.imagePresentation L).projection f) = L (Q.projection f) := rfl

theorem imageInclusion_injective : Function.Injective (Q.imageInclusion L) := by
  apply LinearMap.ker_eq_bot.mp
  exact Submodule.ker_liftQ_eq_bot _ _ _ le_rfl

set_option maxHeartbeats 800000 in
@[simp] theorem imageInclusion_imageProjection (v : Q.Space) :
    Q.imageInclusion L (Q.imageProjection L v) = L v := by
  obtain ⟨f, hfv⟩ := Q.projection_surjective v
  calc
    Q.imageInclusion L (Q.imageProjection L v) =
        Q.imageInclusion L (Q.imageProjection L (Q.projection f)) :=
      congrArg (fun w : Q.Space => Q.imageInclusion L (Q.imageProjection L w)) hfv.symm
    _ = Q.imageInclusion L ((Q.imagePresentation L).projection f) :=
      congrArg (fun w : (Q.imagePresentation L).Space => Q.imageInclusion L w)
        (Q.imageProjection_projection L f)
    _ = L (Q.projection f) := Q.imageInclusion_projection L f
    _ = L v := congrArg (fun w : Q.Space => L w) hfv

theorem image_factorization :
    (Q.imageInclusion L).comp (Q.imageProjection L) = L := by
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  exact Q.imageInclusion_imageProjection L

theorem imageInclusion_mem_range (v : (Q.imagePresentation L).Space) :
    Q.imageInclusion L v ∈ L.range := by
  obtain ⟨f, hfv⟩ := (Q.imagePresentation L).projection_surjective v
  refine ⟨Q.projection f, ?_⟩
  exact (Q.imageInclusion_projection L f).symm.trans
    (congrArg (fun w : (Q.imagePresentation L).Space => Q.imageInclusion L w) hfv)

@[simp] theorem imageInclusion_range : (Q.imageInclusion L).range = L.range := by
  apply Subrepresentation.toSubmodule_injective
  apply Submodule.ext
  intro v
  constructor
  · rintro ⟨w, hw⟩
    exact hw ▸ Q.imageInclusion_mem_range L w
  · rintro ⟨w, hw⟩
    exact ⟨Q.imageProjection L w, (Q.imageInclusion_imageProjection L w).trans hw⟩

/-- Restrict the injective factor to the genuine invariant range of the supplied map. -/
def imageRangeMap :
    (Q.imagePresentation L).representation.IntertwiningMap L.range.toRepresentation where
  toLinearMap := (Q.imageInclusion L).toLinearMap.codRestrict L.range.toSubmodule
    (Q.imageInclusion_mem_range L)
  isIntertwining' a := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    exact Representation.IntertwiningMap.isIntertwining _ _ (Q.imageInclusion L) a v

@[simp] theorem imageRangeMap_val (v : (Q.imagePresentation L).Space) :
    (Q.imageRangeMap L v).val = Q.imageInclusion L v := rfl

set_option maxHeartbeats 800000 in
theorem imageRangeMap_bijective : Function.Bijective (Q.imageRangeMap L) := by
  constructor
  · intro v w h
    have hvw : Q.imageInclusion L v = Q.imageInclusion L w :=
      congrArg (fun x : L.range.toSubmodule => x.val) h
    exact Q.imageInclusion_injective L hvw
  · intro v
    obtain ⟨w, hw⟩ := v.property
    refine ⟨Q.imageProjection L w, Subtype.ext ?_⟩
    exact (Q.imageInclusion_imageProjection L w).trans hw

/-- The new actual presentation represents exactly the whole-operator range. -/
def imageEquivRange :
    (Q.imagePresentation L).representation.Equiv L.range.toRepresentation :=
  (Q.imageRangeMap L).ofBijective (Q.imageRangeMap_bijective L)

@[simp] theorem imageEquivRange_val (v : (Q.imagePresentation L).Space) :
    (Q.imageEquivRange L v).val = Q.imageInclusion L v := rfl

@[simp] theorem imageEquivRange_imageProjection (v : Q.Space) :
    (Q.imageEquivRange L (Q.imageProjection L v)).val = L v :=
  Q.imageInclusion_imageProjection L v

theorem imageInclusion_surjective (hL : Function.Surjective L) :
    Function.Surjective (Q.imageInclusion L) := by
  intro v
  obtain ⟨w, hw⟩ := hL v
  exact ⟨Q.imageProjection L w, (Q.imageInclusion_imageProjection L w).trans hw⟩

/-- Every supplied whole-operator quotient of an actual quotient has an actual presentation. -/
def imageEquivOfSurjective (hL : Function.Surjective L) :
    (Q.imagePresentation L).representation.Equiv ρ :=
  (Q.imageInclusion L).ofBijective
    ⟨Q.imageInclusion_injective L, Q.imageInclusion_surjective L hL⟩

@[simp] theorem imageEquivOfSurjective_imageProjection
    (hL : Function.Surjective L) (v : Q.Space) :
    Q.imageEquivOfSurjective L hL (Q.imageProjection L v) = L v :=
  Q.imageInclusion_imageProjection L v

theorem imagePresentation_isoClass_eq {T : OperatorSubquotient F n}
    (M : Q.representation.IntertwiningMap T.representation)
    (hM : Function.Surjective M) :
    (Q.imagePresentation M).isoClass = T.isoClass :=
  ((Q.imagePresentation M).isoClass_eq_iff T).mpr ⟨Q.imageEquivOfSurjective M hM⟩

end OperatorSubquotient
end Langlands.Automorphic
