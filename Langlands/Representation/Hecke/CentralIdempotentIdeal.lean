import Langlands.Representation.Hecke.CentralMultiplier
import Mathlib.RingTheory.NonUnitalSubring.Basic

/-! # The two-sided Hecke ideal of a categorical central idempotent -/

noncomputable section

open CategoryTheory MeasureTheory

namespace Langlands.Hecke

universe u v w

variable {G : Type u} [Group G] [TopologicalSpace G] [T2Space G]
  [NonarchimedeanGroup G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
  (μ : Measure G) [μ.IsHaarMeasure]
  (hl : IsSmooth (HarmonicAnalysis.GroupAction.leftTests (G := G)))
  (z : CatCenter (SmoothRep.{0,u,max u v} ℂ G))

/-- The fixed Hecke elements of the central multiplier, with their inherited ring operations. -/
def centralIdeal : NonUnitalSubring (HeckeAlgebra μ) where
  carrier := {a | centralMultiplier μ hl z a = a}
  zero_mem' := map_zero _
  add_mem' := by
    intro a b ha hb
    change centralMultiplier μ hl z (a + b) = a + b
    rw [map_add, ha, hb]
  neg_mem' := by
    intro a ha
    change centralMultiplier μ hl z (-a) = -a
    rw [map_neg, ha]
  mul_mem' := by
    intro a b _ hb
    change centralMultiplier μ hl z (a * b) = a * b
    rw [centralMultiplier_mul_right, hb]

@[simp] theorem mem_centralIdeal (a : HeckeAlgebra μ) :
    a ∈ centralIdeal μ hl z ↔ centralMultiplier μ hl z a = a := Iff.rfl

/-- The fixed elements form a two-sided ideal in the actual nonunital Hecke algebra. -/
theorem centralIdeal_twoSided (a b : HeckeAlgebra μ) (hb : b ∈ centralIdeal μ hl z) :
    a * b ∈ centralIdeal μ hl z ∧ b * a ∈ centralIdeal μ hl z := by
  constructor
  · change centralMultiplier μ hl z (a * b) = a * b
    rw [centralMultiplier_mul_right, (mem_centralIdeal μ hl z b).mp hb]
  · change centralMultiplier μ hl z (b * a) = b * a
    rw [centralMultiplier_mul_left, (mem_centralIdeal μ hl z b).mp hb]

variable (hz : IsIdempotentElem z)

include hz

omit [T2Space G] [LocallyCompactSpace G] in
/-- An idempotent central element induces an idempotent Hecke multiplier. -/
theorem centralMultiplier_idempotent (a : HeckeAlgebra μ) :
    centralMultiplier μ hl z (centralMultiplier μ hl z a) = centralMultiplier μ hl z a := by
  rw [← centralMultiplier_mul, hz.eq]

/-- In the idempotent case, the fixed ideal is precisely the image of the multiplier. -/
theorem mem_centralIdeal_iff_range (a : HeckeAlgebra μ) :
    a ∈ centralIdeal μ hl z ↔ ∃ b, centralMultiplier μ hl z b = a := by
  constructor
  · intro ha
    exact ⟨a, ha⟩
  · rintro ⟨b, rfl⟩
    exact centralMultiplier_idempotent μ hl z hz b

/-- The image condition expressed on the exact lifted regular carrier. -/
theorem mem_centralIdeal_iff_regular (a : HeckeAlgebra μ) :
    a ∈ centralIdeal μ hl z ↔ ∃ b : HeckeAlgebra μ,
      SmoothRep.hom (z.app (regularLift.{u,v} hl))
          (ULift.up (HeckeAlgebra.toTestFunction μ b)) =
        ULift.up (HeckeAlgebra.toTestFunction μ a) := by
  rw [mem_centralIdeal_iff_range μ hl z hz]
  constructor
  · rintro ⟨b, hb⟩
    exact ⟨b, by rw [← centralMultiplier_up, hb]⟩
  · rintro ⟨b, hb⟩
    exact ⟨b, congrArg (fun x => (HeckeAlgebra.toTestFunction μ).symm x.down) hb⟩

/-- The central idempotent multiplier is multiplicative. -/
theorem centralMultiplier_map_mul (a b : HeckeAlgebra μ) :
    centralMultiplier μ hl z (a * b) =
      centralMultiplier μ hl z a * centralMultiplier μ hl z b := by
  calc
    centralMultiplier μ hl z (a * b) =
        centralMultiplier μ hl z (centralMultiplier μ hl z (a * b)) :=
      (centralMultiplier_idempotent μ hl z hz (a * b)).symm
    _ = centralMultiplier μ hl z a * centralMultiplier μ hl z b := by
      rw [centralMultiplier_mul_left μ hl z a b, centralMultiplier_mul_right]

/-- The actual nonunital ring projection onto the central ideal. -/
def centralIdealProjection : HeckeAlgebra μ →ₙ+* centralIdeal μ hl z where
  toFun a := ⟨centralMultiplier μ hl z a, centralMultiplier_idempotent μ hl z hz a⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' a b := Subtype.ext (map_add _ a b)
  map_mul' a b := Subtype.ext (centralMultiplier_map_mul μ hl z hz a b)

@[simp] theorem centralIdealProjection_val (a : HeckeAlgebra μ) :
    (centralIdealProjection μ hl z hz a : HeckeAlgebra μ) = centralMultiplier μ hl z a := rfl

@[simp] theorem centralIdealProjection_subtype (a : centralIdeal μ hl z) :
    centralIdealProjection μ hl z hz (a : HeckeAlgebra μ) = a :=
  Subtype.ext a.property

end Langlands.Hecke
