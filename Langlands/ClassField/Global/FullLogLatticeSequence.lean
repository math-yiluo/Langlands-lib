import Langlands.ClassField.Global.FullLogLatticeRepresentations
import Langlands.ClassField.Global.LocalUnitCohomology

/-! # The short exact sequence for adjoining integer constants to the unit lattice -/

noncomputable section

open NumberField CategoryTheory
open scoped Classical

namespace Langlands.ClassField.Global

universe u v

variable (F : Type u) [Field F] (E : Type v) [Field E] [NumberField E] [Algebra F E]

/-- Include the unit component into its product with the trivial integer component. -/
def fullLogUnitProductInclusion :
    fullLogUnitLatticeRepresentation F E ⟶ fullLogUnitLatticeWithConstantsRepresentation F E :=
  Rep.ofHom
    { toLinearMap := LinearMap.inl NormalizedTwoCocycle.CoefficientScalars.{v}
        (fullLogUnitLattice E) NormalizedTwoCocycle.CoefficientScalars.{v}
      isIntertwining' g := by
        apply LinearMap.ext
        intro x
        rfl }

/-- Project the product onto its trivial integer component. -/
def fullLogUnitProductProjection :
    fullLogUnitLatticeWithConstantsRepresentation F E ⟶
      Rep.trivial NormalizedTwoCocycle.CoefficientScalars.{v} (E ≃ₐ[F] E)
        NormalizedTwoCocycle.CoefficientScalars.{v} :=
  Rep.ofHom
    { toLinearMap := LinearMap.snd NormalizedTwoCocycle.CoefficientScalars.{v}
        (fullLogUnitLattice E) NormalizedTwoCocycle.CoefficientScalars.{v}
      isIntertwining' g := by
        apply LinearMap.ext
        intro x
        rfl }

/-- Include the actual unit lattice into the augmented full lattice. -/
def fullLogUnitAugmentedInclusion :
    fullLogUnitLatticeRepresentation F E ⟶ augmentedFullLogUnitLatticeRepresentation F E :=
  fullLogUnitProductInclusion F E ≫ (fullLogIntegralSplitRepresentationIso F E).inv

/-- The integral constant coefficient as a morphism to the trivial lifted integers. -/
def fullLogIntegralConstantProjection :
    augmentedFullLogUnitLatticeRepresentation F E ⟶
      Rep.trivial NormalizedTwoCocycle.CoefficientScalars.{v} (E ≃ₐ[F] E)
        NormalizedTwoCocycle.CoefficientScalars.{v} :=
  (fullLogIntegralSplitRepresentationIso F E).hom ≫ fullLogUnitProductProjection F E

@[simp] theorem fullLogUnitAugmentedInclusion_apply (x : fullLogUnitLattice E) :
    (fullLogUnitAugmentedInclusion F E).hom x = (fullLogIntegralSplitLifted E).symm (x, 0) :=
  rfl

@[simp] theorem fullLogIntegralConstantProjection_apply (x : augmentedFullLogUnitLattice E) :
    (fullLogIntegralConstantProjection F E).hom x = (fullLogIntegralSplitLifted E x).2 := rfl

/-- The sequence M₀ → M → ℤ of actual arithmetic representations. -/
def fullLogLatticeSequence :
    ShortComplex (Rep.{v} NormalizedTwoCocycle.CoefficientScalars.{v} (E ≃ₐ[F] E)) :=
  ShortComplex.mk (fullLogUnitAugmentedInclusion F E)
    (fullLogIntegralConstantProjection F E) (by
      apply Rep.hom_ext
      apply Representation.IntertwiningMap.ext
      apply LinearMap.ext
      intro x
      change (fullLogIntegralSplitLifted E ((fullLogIntegralSplitLifted E).symm (x, 0))).2 = 0
      exact congrArg Prod.snd ((fullLogIntegralSplitLifted E).apply_symm_apply (x, 0)))

/-- Adjoining the constant lattice gives a short exact sequence. -/
theorem fullLogLatticeSequence_shortExact : (fullLogLatticeSequence F E).ShortExact := by
  refine repShortExact_of_values _ ?_ ?_ ?_
  · intro a b h
    change (fullLogIntegralSplitLifted E).symm (a, 0) =
      (fullLogIntegralSplitLifted E).symm (b, 0) at h
    exact congrArg Prod.fst ((fullLogIntegralSplitLifted E).symm.injective h)
  · intro x hx
    change (fullLogIntegralSplitLifted E x).2 = 0 at hx
    refine ⟨(fullLogIntegralSplitLifted E x).1, ?_⟩
    change (fullLogIntegralSplitLifted E).symm ((fullLogIntegralSplitLifted E x).1, 0) = x
    apply (fullLogIntegralSplitLifted E).injective
    simpa only [LinearEquiv.apply_symm_apply] using
      (Prod.ext rfl hx.symm : ((fullLogIntegralSplitLifted E x).1, 0) =
        fullLogIntegralSplitLifted E x)
  · intro z
    refine ⟨(fullLogIntegralSplitLifted E).symm (0, z), ?_⟩
    change (fullLogIntegralSplitLifted E ((fullLogIntegralSplitLifted E).symm (0, z))).2 = z
    exact congrArg Prod.snd ((fullLogIntegralSplitLifted E).apply_symm_apply (0, z))

end Langlands.ClassField.Global
