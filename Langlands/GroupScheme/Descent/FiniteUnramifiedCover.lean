import Langlands.GroupScheme.Descent.FiniteUnramifiedComponents
import Langlands.GroupScheme.Descent.FiniteUnramifiedGroupModel
import Langlands.GroupScheme.Descent.ValuationIntegerCover

/-! # Actual fpqc covers for unramified integer coefficients -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.LocalGalois Langlands.LocalGalois.Separable
open scoped ValuativeRel

namespace Langlands.GroupScheme.Descent.FiniteUnramified

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]

local instance coverNormedField : NontriviallyNormedField F := localNormedField F
local instance coverUltrametric : IsUltrametricDist F := localNormedField_ultrametric F
local instance coverComplete : CompleteSpace F := localNormedField_complete F

local instance coverIntegerAlgebra : Algebra ↥𝒪[F] (fixedFieldIntegers F) :=
  Valuation.HasExtension.instAlgebraInteger
    (vR := ValuativeRel.valuation F) (vA := fixedFieldValuation F)

/-- The finite-stage spectral integer map is fpqc; no unramifiedness is needed. -/
theorem integerMap_fpqc (E : IntermediateField F (SeparableClosure F)) :
    Surjective (integerMap F E) ∧ Flat (integerMap F E) ∧
      QuasiCompact (integerMap F E) :=
  valuationInteger_fpqc (NormedField.valuation (K := F)) (spectralValuation F E)

/-- The actual maximal-unramified integer inclusion is fpqc. -/
theorem fixedFieldIntegerMap_fpqc :
    Surjective (Spec.map (CommRingCat.ofHom (integerToFixedField F))) ∧
      Flat (Spec.map (CommRingCat.ofHom (integerToFixedField F))) ∧
      QuasiCompact (Spec.map (CommRingCat.ofHom (integerToFixedField F))) :=
  valuationInteger_fpqc (ValuativeRel.valuation F) (fixedFieldValuation F)

/-- The actual singleton cover of the base spectrum by maximal-unramified integers. -/
def fixedFieldIntegerCover : (Spec (CommRingCat.of ↥𝒪[F])).Cover Scheme.fpqcPrecoverage :=
  valuationIntegerCover (ValuativeRel.valuation F) (fixedFieldValuation F)

@[simp]
theorem fixedFieldIntegerCover_f (i : (fixedFieldIntegerCover F).I₀) :
    (fixedFieldIntegerCover F).f i =
      Spec.map (CommRingCat.ofHom (integerToFixedField F)) := rfl

/-- Every intermediate coefficient algebra is flat over the base valuation ring. -/
theorem integerSubalgebra_flat (T : Subalgebra ↥𝒪[F] (fixedFieldIntegers F)) :
    Module.Flat ↥𝒪[F] T := by
  let : Module.IsTorsionFree F (inertiaFixedField F) :=
    DivisionSemiring.to_moduleIsTorsionFree
  let : Module.IsTorsionFree ↥𝒪[F] (fixedFieldIntegers F) :=
    Valuation.HasExtension.instIsTorsionFreeInteger
      (vR := ValuativeRel.valuation F) (vA := fixedFieldValuation F)
  rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout,
    ← Submodule.isTorsionFree_iff_torsion_eq_bot]
  exact Subalgebra.instIsTorsionFree T

/-- Every intermediate coefficient spectrum still covers the base spectrum. -/
theorem integerSubalgebra_surjective
    (T : Subalgebra ↥𝒪[F] (fixedFieldIntegers F)) :
    Surjective (Spec.algebraMap ↥𝒪[F] T) := by
  let a := Spec.algebraMap T (fixedFieldIntegers F)
  let b := Spec.algebraMap ↥𝒪[F] T
  have hab : a ≫ b = Spec.map (CommRingCat.ofHom (integerToFixedField F)) := by
    dsimp [a, b, Spec.algebraMap]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl
  let : Surjective (a ≫ b) := hab ▸ (fixedFieldIntegerMap_fpqc F).1
  exact Surjective.of_comp a b

/-- Actual intermediate coefficient maps are fpqc, with no finiteness hypothesis. -/
theorem integerSubalgebra_fpqc (T : Subalgebra ↥𝒪[F] (fixedFieldIntegers F)) :
    Surjective (Spec.algebraMap ↥𝒪[F] T) ∧ Flat (Spec.algebraMap ↥𝒪[F] T) ∧
      QuasiCompact (Spec.algebraMap ↥𝒪[F] T) := by
  refine ⟨integerSubalgebra_surjective F T, ?_, inferInstance⟩
  apply Flat.SpecMap_iff.mpr
  change (algebraMap ↥𝒪[F] T).Flat
  rw [RingHom.flat_algebraMap_iff]
  exact integerSubalgebra_flat F T

/-- The fpqc cover for any actual finite-stage coefficient subring. -/
def integerCoefficientsCover (E : IntermediateField F (SeparableClosure F)) :
    (Spec (CommRingCat.of ↥𝒪[F])).Cover Scheme.fpqcPrecoverage where
  I₀ := PUnit
  X _ := Spec (CommRingCat.of (integerCoefficients F E))
  f _ := Spec.algebraMap ↥𝒪[F] (integerCoefficients F E)
  mem₀ := by
    let := (integerSubalgebra_fpqc F (integerCoefficients F E)).1
    let := (integerSubalgebra_fpqc F (integerCoefficients F E)).2.1
    let := (integerSubalgebra_fpqc F (integerCoefficients F E)).2.2
    change Presieve.ofArrows (fun _ : PUnit => Spec (CommRingCat.of (integerCoefficients F E)))
      (fun _ => Spec.algebraMap ↥𝒪[F] (integerCoefficients F E)) ∈ _
    rw [Presieve.ofArrows_pUnit]
    exact Scheme.Hom.singleton_mem_fpqcPrecoverage _

@[simp]
theorem integerCoefficientsCover_f (E : IntermediateField F (SeparableClosure F))
    (i : (integerCoefficientsCover F E).I₀) :
    (integerCoefficientsCover F E).f i =
      Spec.algebraMap ↥𝒪[F] (integerCoefficients F E) := rfl

end Langlands.GroupScheme.Descent.FiniteUnramified
