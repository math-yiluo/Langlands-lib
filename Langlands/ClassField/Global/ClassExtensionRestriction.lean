import Langlands.ClassField.Global.ClassExtension
import Langlands.ClassField.Global.CocycleRestriction
import Langlands.ClassField.Global.CohomologyMaps

/-! # Base restriction of class-indexed idele-class extensions -/

noncomputable section

namespace Langlands.ClassField.Global

open NumberField Topology
open scoped NumberField

universe u

variable {K K' E : Type u} [Field K] [Field K'] [Field E] [NumberField E]
  [Algebra K K'] [Algebra K E] [Algebra K' E] [IsScalarTower K K' E]

attribute [local instance] relativeIdeleClassAction relativeGaloisTopology

namespace RelativeIdeleCocycle

/-- The explicit restriction of a normalized cocycle represents actual cohomological restriction. -/
theorem cohomologyClass_restrictBase (c : RelativeIdeleCocycle K E) :
    (restrictBase K' c).cohomologyClass =
      relativeIdeleClassRestriction K K' E 2 c.cohomologyClass := by
  symm
  apply (relativeIdeleClassRestriction_cohomologyClass_eq_iff c (restrictBase K' c)).mpr
  refine ⟨fun _ => 1, ?_⟩
  intro σ τ
  simp only [restrictBase_apply, map_one]
  exact (mul_one _).trans
    ((congrArg (fun a : IdeleClassGroup (𝓞 E) E =>
        a * c (σ.restrictScalars K, τ.restrictScalars K)) (one_mul 1)).trans
      (one_mul _)).symm

end RelativeIdeleCocycle

namespace ClassExtension

variable (K') (x : relativeIdeleClassCohomology K E 2)

/-- Restrict the actual second cohomology class along scalar restriction of automorphisms. -/
abbrev restrictedClass : relativeIdeleClassCohomology K' E 2 :=
  relativeIdeleClassRestriction K K' E 2 x

/-- The restricted chosen representative has the required restricted class. -/
theorem cohomologyClass_restrictedRepresentative :
    (RelativeIdeleCocycle.restrictBase K' (representative x)).cohomologyClass =
      restrictedClass K' x := by
  rw [RelativeIdeleCocycle.cohomologyClass_restrictBase, cohomologyClass_representative]

/-- Compare the chosen representative of the restricted class with literal cocycle restriction. -/
def restrictionEquiv :
    ClassExtension (restrictedClass K' x) ≃ₜ*
      RelativeIdeleCocycle.Extension (RelativeIdeleCocycle.restrictBase K' (representative x)) :=
  (equivOfRepresentative _ (cohomologyClass_restrictedRepresentative K' x)).symm

/-- The constructed continuous inclusion of the class extension over the larger base field. -/
def restrictionInclusion : ClassExtension (restrictedClass K' x) →ₜ* ClassExtension x where
  toMonoidHom := (RelativeIdeleCocycle.restrictionInclusion K' (representative x)).comp
    (restrictionEquiv K' x).toMulEquiv.toMonoidHom
  continuous_toFun := (RelativeIdeleCocycle.continuous_restrictionInclusion K'
    (representative x)).comp (restrictionEquiv K' x).continuous

@[simp]
theorem restrictionInclusion_inclusion (a : IdeleClassGroup (𝓞 E) E) :
    restrictionInclusion K' x (inclusion (restrictedClass K' x) a) = inclusion x a := by
  change RelativeIdeleCocycle.restrictionInclusion K' (representative x)
    ((equivOfRepresentative _ (cohomologyClass_restrictedRepresentative K' x)).symm
      (inclusion (restrictedClass K' x) a)) = inclusion x a
  rw [equivOfRepresentative_symm_inclusion,
    RelativeIdeleCocycle.restrictionInclusion_inclusion]

@[simp]
theorem projection_restrictionInclusion (t : ClassExtension (restrictedClass K' x)) :
    projection x (restrictionInclusion K' x t) =
      (projection (restrictedClass K' x) t).restrictScalars K := by
  change (RelativeIdeleCocycle.projection _
    ((equivOfRepresentative _ (cohomologyClass_restrictedRepresentative K' x)).symm t)).restrictScalars K = _
  rw [projection_equivOfRepresentative_symm]

theorem restrictionInclusion_injective : Function.Injective (restrictionInclusion K' x) :=
  (RelativeIdeleCocycle.restrictionInclusion_injective K' (representative x)).comp
    (restrictionEquiv K' x).injective

/-- The restricted class extension carries exactly the topology of an open subgroup. -/
theorem isOpenEmbedding_restrictionInclusion : IsOpenEmbedding (restrictionInclusion K' x) :=
  (RelativeIdeleCocycle.isOpenEmbedding_restrictionInclusion K' (representative x)).comp
    (restrictionEquiv K' x).toHomeomorph.isOpenEmbedding

/-- The image consists precisely of extension elements over larger-base-linear automorphisms. -/
theorem range_restrictionInclusion :
    (restrictionInclusion K' x).toMonoidHom.range =
      ((AlgEquiv.restrictScalarsHom K : (E ≃ₐ[K'] E) →* (E ≃ₐ[K] E)).range).comap
        (projection x) := by
  rw [show (restrictionInclusion K' x).toMonoidHom.range =
      (RelativeIdeleCocycle.restrictionInclusion K' (representative x)).range from ?_]
  · exact RelativeIdeleCocycle.range_restrictionInclusion K' (representative x)
  · ext t
    constructor
    · rintro ⟨s, rfl⟩
      exact ⟨restrictionEquiv K' x s, rfl⟩
    · rintro ⟨s, rfl⟩
      refine ⟨(restrictionEquiv K' x).symm s, ?_⟩
      change RelativeIdeleCocycle.restrictionInclusion K' (representative x)
        (restrictionEquiv K' x ((restrictionEquiv K' x).symm s)) = _
      rw [(restrictionEquiv K' x).apply_symm_apply]

end ClassExtension
end Langlands.ClassField.Global
