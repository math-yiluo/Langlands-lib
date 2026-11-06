import Langlands.Geometry.Building.KPLocalSplitNorm

/-! # Relative unit norms for intermediate fields of a fixed finite extension -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped NNReal
open Langlands.LocalGalois.Separable

namespace Langlands.Geometry.Building

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  (L : IntermediateField (UnramifiedClosure F) (SeparableClosure F))
  [FiniteDimensional (UnramifiedClosure F) L]
  (E : IntermediateField (UnramifiedClosure F) L)

/-- Local unit-norm surjectivity for a subfield of the prescribed finite extension. -/
theorem intermediate_unit_norm_surjective (a : Eˣ)
    (ha : intermediateValuation F L (algebraMap E L (a : E)) = 1) :
    ∃ b : Lˣ, intermediateValuation F L (b : L) = 1 ∧
      Units.map (Algebra.norm E) b = a := by
  let : Algebra (UnramifiedClosure F) E := E.toSubalgebra.algebra
  let E' : IntermediateField (UnramifiedClosure F) (SeparableClosure F) := IntermediateField.lift E
  let L' : IntermediateField E' (SeparableClosure F) :=
    IntermediateField.extendScalars (IntermediateField.lift_le E)
  have : FiniteDimensional (UnramifiedClosure F) E' :=
    FiniteDimensional.of_injective
      (IntermediateField.inclusion (IntermediateField.lift_le E)).toLinearMap
      (IntermediateField.inclusion_injective (IntermediateField.lift_le E))
  let instKL' : Algebra (UnramifiedClosure F) L' :=
    (L'.restrictScalars (UnramifiedClosure F)).toSubalgebra.algebra
  let : Module (UnramifiedClosure F) L' := Algebra.toModule
  let : SMul (UnramifiedClosure F) L' := instKL'.toSMul
  have : IsScalarTower (UnramifiedClosure F) E' L' :=
    IsScalarTower.of_algebraMap_eq' rfl
  have : FiniteDimensional (UnramifiedClosure F) L' :=
    inferInstanceAs (FiniteDimensional (UnramifiedClosure F) L)
  have : FiniteDimensional E' L' :=
    Module.Finite.right (UnramifiedClosure F) E' L'
  let e : E ≃ₐ[UnramifiedClosure F] E' := IntermediateField.liftAlgEquiv E
  have ha' : intermediateValuation F E'
      (Units.map e.toAlgHom.toMonoidHom a : E') = 1 := by
    exact ha
  obtain ⟨b, hb, hnorm⟩ :=
    nestedIntermediate_unit_norm_surjective F E' L'
      (Units.map e.toAlgHom.toMonoidHom a) ha'
  refine ⟨b, hb, Units.ext ?_⟩
  apply e.injective
  let : Algebra E L' :=
    ((algebraMap E' L').comp e.toRingEquiv.toRingHom).toAlgebra
  have hmap : (algebraMap E' L').comp e.toRingEquiv.toRingHom = algebraMap E L' := by
    ext x
    rfl
  change e (Algebra.norm E (b : L')) = e (a : E)
  exact (Algebra.norm_eq_of_ringEquiv e.toRingEquiv hmap (b : L')).trans
    (congrArg (fun z : E'ˣ => (z : E')) hnorm)

/-- A chosen bounded unit with the prescribed relative norm. -/
def intermediateUnitNormLift (a : Eˣ)
    (ha : intermediateValuation F L (algebraMap E L (a : E)) = 1) : Lˣ :=
  Classical.choose (intermediate_unit_norm_surjective F L E a ha)

theorem intermediateUnitNormLift_valuation (a : Eˣ)
    (ha : intermediateValuation F L (algebraMap E L (a : E)) = 1) :
    intermediateValuation F L (intermediateUnitNormLift F L E a ha : L) = 1 :=
  (Classical.choose_spec (intermediate_unit_norm_surjective F L E a ha)).1

theorem intermediateUnitNormLift_norm (a : Eˣ)
    (ha : intermediateValuation F L (algebraMap E L (a : E)) = 1) :
    Units.map (Algebra.norm E) (intermediateUnitNormLift F L E a ha) = a :=
  (Classical.choose_spec (intermediate_unit_norm_surjective F L E a ha)).2

end Langlands.Geometry.Building
