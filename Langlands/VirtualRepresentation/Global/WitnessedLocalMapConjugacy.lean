import Langlands.VirtualRepresentation.Global.RelativeImages
import Langlands.ClassFieldTheory.Global.LocalRelativeWeilMapPlaceConjugacy

/-!
# Local maps of witnessed generators are conjugate

The local maps `W_{F_v} → W_{E/F}` of any two witnessed relative generators at `v` are
conjugate in `W_{E/F}`, even at different places above `v`. Hence the local component of
a representation of `W_{E/F}`, and its class in continuous exact K0, do not depend on the
local map.
-/

noncomputable section

universe uF uW uP

set_option autoImplicit false

namespace Langlands.ClassFieldTheory.Global.RelativeWeilGroup

open Langlands.Global.CompletionPadic

variable {F E : Type uF} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  [IsGalois F E] {c : FundamentalClass.ClassFamily.{uF}} {v : Langlands.Global.FinitePlace F}

/-- Conjugate local maps have equivalent local components: `S(t)` intertwines them. -/
def localComponentConjEquiv (S : FiniteRepresentation.{0, uF, uW} ℂ (RelativeWeilGroup c F E))
    (ι ι' : Weil.Local.localWeilGroup (padicField v) →ₜ* RelativeWeilGroup c F E)
    (t : RelativeWeilGroup c F E) (h : ∀ g, ι' g = t * ι g * t⁻¹) :
    FiniteRepresentation.Equiv (localComponent S ι) (localComponent S ι') := by
  let e : S ≃ₗ[ℂ] S := LinearEquiv.ofLinearMap (S.representation t) (S.representation t⁻¹)
    (by rw [← Module.End.mul_eq_comp, ← map_mul, mul_inv_cancel, map_one]; rfl)
    (by rw [← Module.End.mul_eq_comp, ← map_mul, inv_mul_cancel, map_one]; rfl)
  refine Representation.Equiv.mk e fun g => LinearMap.ext fun x => ?_
  have key : ∀ y : S, S.representation t (S.representation (ι g) y) =
      S.representation (ι' g) (S.representation t y) := fun y => by
    rw [h g, ← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul,
      inv_mul_cancel_right]
  exact key x

end Langlands.ClassFieldTheory.Global.RelativeWeilGroup

namespace Langlands.VirtualRepresentation.RelativeGlobal

open Langlands.Global Langlands.Global.CompletionPadic Langlands.ClassFieldTheory.Global

variable (F E : Type uF) [Field F] [NumberField F] [Field E] [NumberField E]
  [Algebra F E] [IsGalois F E]
  (c : FundamentalClass.ClassFamily.{uF}) (v : FinitePlace F)

/-- The local exact class does not change under conjugation of the local map. -/
theorem localExactClass_eq_of_conj
    (S : FiniteRepresentation.{0, uF, uW} ℂ (RelativeWeilGroup c F E)) (hS : S.IsContinuous)
    (ι ι' : Weil.Local.localWeilGroup (padicField v) →ₜ* RelativeWeilGroup c F E)
    (t : RelativeWeilGroup c F E) (h : ∀ g, ι' g = t * ι g * t⁻¹) :
    localExactClass F E c v S hS ι' = localExactClass F E c v S hS ι := by
  unfold localExactClass
  exact (ExactGrothendieckGroup.ofRepresentation_eq_of_equiv _
    (RelativeWeilGroup.localComponentConjEquiv S ι ι' t h)).symm

variable [CompactSpace (AdeleQuotient F)]

/-- The local maps of two witnessed generators are conjugate in `W_{E/F}`. -/
theorem WitnessedGenerator.exists_conj_localMap
    (d d' : WitnessedGenerator.{uF, uW, uP} F E c v) :
    ∃ t : RelativeWeilGroup c F E, ∀ g, d'.localMap g = t * d.localMap g * t⁻¹ := by
  have : d.placeOver.1.asIdeal.LiesOver v.asIdeal := d.placeOver.2
  have : d'.placeOver.1.asIdeal.LiesOver v.asIdeal := d'.placeOver.2
  exact RelativeWeilGroup.exists_conj_of_isLocalRelativeWeilMap d.localMap_spec d'.localMap_spec

/-- The local exact class of any continuous representation is the same along the local maps of
any two witnessed generators. -/
theorem WitnessedGenerator.localExactClass_localMap_eq
    (d d' : WitnessedGenerator.{uF, uW, uP} F E c v)
    (S : FiniteRepresentation.{0, uF, uW} ℂ (RelativeWeilGroup c F E)) (hS : S.IsContinuous) :
    localExactClass F E c v S hS d'.localMap = localExactClass F E c v S hS d.localMap := by
  obtain ⟨t, ht⟩ := WitnessedGenerator.exists_conj_localMap F E c v d d'
  exact localExactClass_eq_of_conj F E c v S hS d.localMap d'.localMap t ht

end Langlands.VirtualRepresentation.RelativeGlobal
