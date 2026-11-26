import Langlands.Galois.Local.SeparableUnramifiedNormedCompletion
import Langlands.Global.FiniteCompletionLocalField

/-! # The completed unramified extension at a finite place -/

noncomputable section

namespace Langlands.Global.FiniteCompletion

open Langlands.LocalGalois Langlands.LocalGalois.Separable
open Langlands.LocalGalois.Separable.UnramifiedCompletion

universe u

variable {F : Type u} [Field F] [NumberField F] (v : FinitePlace F)

/-- The norm on the base completion used in the spectral extension to the inertia
fixed field. -/
@[instance_reducible]
def unramifiedBaseNormedField : NontriviallyNormedField (FiniteCompletion F v) :=
  letI := valuativeRel v
  letI := isNonarchimedeanLocalField v
  localNormedField (FiniteCompletion F v)

theorem unramifiedBase_ultrametric :
    @IsUltrametricDist (FiniteCompletion F v) (unramifiedBaseNormedField v).toDist := by
  let := valuativeRel v
  let := isNonarchimedeanLocalField v
  exact localNormedField_ultrametric (FiniteCompletion F v)

theorem unramifiedBase_complete :
    @CompleteSpace (FiniteCompletion F v) (unramifiedBaseNormedField v).toUniformSpace := by
  let := valuativeRel v
  let := isNonarchimedeanLocalField v
  exact localNormedField_complete (FiniteCompletion F v)

/-- The norm induces the existing finite-place completion topology. -/
theorem unramifiedBase_topology :
    (unramifiedBaseNormedField v).toNormedField.toUniformSpace.toTopologicalSpace =
      (inferInstance : TopologicalSpace (FiniteCompletion F v)) := by
  let := valuativeRel v
  let := isNonarchimedeanLocalField v
  exact localNormedField_topology (FiniteCompletion F v)

/-- The completed maximal unramified extension of the actual completion at `v`. -/
def CompletedUnramified :=
  letI := valuativeRel v
  letI := isNonarchimedeanLocalField v
  CompletedField (FiniteCompletion F v)

instance completedUnramified_normedField : NontriviallyNormedField (CompletedUnramified v) :=
  letI := valuativeRel v
  letI := isNonarchimedeanLocalField v
  inferInstanceAs (NontriviallyNormedField (CompletedField (FiniteCompletion F v)))

instance completedUnramified_isUltrametricDist : IsUltrametricDist (CompletedUnramified v) :=
  letI := valuativeRel v
  letI := isNonarchimedeanLocalField v
  inferInstanceAs (IsUltrametricDist (CompletedField (FiniteCompletion F v)))

instance completedUnramified_completeSpace : CompleteSpace (CompletedUnramified v) :=
  letI := valuativeRel v
  letI := isNonarchimedeanLocalField v
  inferInstanceAs (CompleteSpace (CompletedField (FiniteCompletion F v)))

instance completedUnramified_localAlgebra : Algebra (FiniteCompletion F v) (CompletedUnramified v) :=
  letI := valuativeRel v
  letI := isNonarchimedeanLocalField v
  inferInstanceAs (Algebra (FiniteCompletion F v) (CompletedField (FiniteCompletion F v)))

/-- The existing base embedding is a normed algebra for the spectral base norm. -/
@[instance_reducible]
def completedUnramifiedNormedAlgebra :
    @NormedAlgebra (FiniteCompletion F v) (CompletedUnramified v)
      (unramifiedBaseNormedField v).toNormedField inferInstance :=
  letI := valuativeRel v
  letI := isNonarchimedeanLocalField v
  instCompletedFieldNormedAlgebra (FiniteCompletion F v)

/-- The normed base completion embeds isometrically in the unramified completion. -/
theorem completedUnramified_norm_algebraMap (x : FiniteCompletion F v) :
    ‖algebraMap (FiniteCompletion F v) (CompletedUnramified v) x‖ =
      @Norm.norm (FiniteCompletion F v) (unramifiedBaseNormedField v).toNorm x := by
  let := valuativeRel v
  let := isNonarchimedeanLocalField v
  exact norm_algebraMap_completedField (FiniteCompletion F v) x

/-- Embed the global field by composition through its finite-place completion. -/
instance completedUnramified_algebra : Algebra F (CompletedUnramified v) :=
  ((algebraMap (FiniteCompletion F v) (CompletedUnramified v)).comp
    (algebraMap F (FiniteCompletion F v))).toAlgebra

instance completedUnramified_scalarTower :
    IsScalarTower F (FiniteCompletion F v) (CompletedUnramified v) :=
  IsScalarTower.of_algebraMap_eq' (R := F) (S := FiniteCompletion F v)
    (A := CompletedUnramified v) rfl

/-- Arithmetic Frobenius over the given completion. -/
def completedUnramifiedArithmeticFrobenius :
    CompletedUnramified v ≃ₐ[FiniteCompletion F v] CompletedUnramified v :=
  letI := valuativeRel v
  letI := isNonarchimedeanLocalField v
  completedFieldArithmeticFrobenius (FiniteCompletion F v)

/-- The Krull Galois group of the maximal unramified algebraic extension of the
actual finite-place completion. -/
abbrev UnramifiedGaloisGroup :=
  letI := valuativeRel v
  letI := isNonarchimedeanLocalField v
  Gal(inertiaFixedField (FiniteCompletion F v)/FiniteCompletion F v)

/-- The unramified Galois group acts by algebra automorphisms on the completed
coefficient field. -/
def completedUnramifiedGaloisAction : UnramifiedGaloisGroup v →*
    (CompletedUnramified v ≃ₐ[FiniteCompletion F v] CompletedUnramified v) :=
  letI := valuativeRel v
  letI := isNonarchimedeanLocalField v
  completedFieldGaloisAction (FiniteCompletion F v)

/-- Each coefficient automorphism preserves the norm of the completed field. -/
theorem completedUnramifiedGaloisAction_norm (σ : UnramifiedGaloisGroup v)
    (x : CompletedUnramified v) : ‖completedUnramifiedGaloisAction v σ x‖ = ‖x‖ := by
  let := valuativeRel v
  let := isNonarchimedeanLocalField v
  exact (completedFieldAut_isometry (FiniteCompletion F v) σ).norm_map_of_map_zero
    (map_zero (completedUnramifiedGaloisAction v σ)) x

/-- The arithmetic Frobenius on the completed coefficient field preserves its norm. -/
theorem completedUnramifiedArithmeticFrobenius_norm (x : CompletedUnramified v) :
    ‖completedUnramifiedArithmeticFrobenius v x‖ = ‖x‖ := by
  let := valuativeRel v
  let := isNonarchimedeanLocalField v
  exact completedUnramifiedGaloisAction_norm v
    (exists_fixedField_arithmeticFrobenius (FiniteCompletion F v)).choose x

end Langlands.Global.FiniteCompletion
