import Langlands.ClassField.Global.LocalCocycleMap

/-! # Completed-local class extensions and maps to global class extensions -/

noncomputable section

namespace Langlands.ClassField.Global

open NumberField Topology
open scoped NumberField Langlands.Global.AdelicFunctoriality.FiniteExtension
open FundamentalClass Langlands.Global.CompletionPadic
open Langlands.ClassFieldTheory.Local

universe u

variable {F E : Type u} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : Langlands.Global.FinitePlace F) (w : Langlands.Global.FinitePlace E)
  [w.asIdeal.LiesOver v.asIdeal]

attribute [local instance] completionGaloisTopology relativeGaloisTopology
  relativeIdeleClassAction

/-- The existing second cohomology of the actual completed-field unit representation. -/
abbrev CompletionH2 :=
  relativeCohomology (padicField v).Carrier (w.adicCompletion E) 2

namespace CompletionUnitCocycle

theorem cohomologyClass_surjective :
    Function.Surjective (cohomologyClass (v := v) (w := w)) :=
  NormalizedTwoCocycle.cohomologyClass_surjective

end CompletionUnitCocycle

namespace CompletionClassExtension

variable (x : CompletionH2 v w)

/-- Choose a normalized representative of the given actual local second cohomology class. -/
def representative : CompletionUnitCocycle v w :=
  (CompletionUnitCocycle.cohomologyClass_surjective v w x).choose

theorem cohomologyClass_representative : (representative v w x).cohomologyClass = x :=
  (CompletionUnitCocycle.cohomologyClass_surjective v w x).choose_spec

end CompletionClassExtension

/-- The actual product-coordinate extension for the chosen representative of the local class. -/
abbrev CompletionClassExtension (x : CompletionH2 v w) : Type u :=
  CompletionUnitCocycle.Extension (CompletionClassExtension.representative v w x)

namespace CompletionClassExtension

variable (x : CompletionH2 v w)

instance isTopologicalGroup : IsTopologicalGroup (CompletionClassExtension v w x) :=
  CompletionUnitCocycle.extensionIsTopologicalGroup _

/-- The actual completed-field unit inclusion. -/
abbrev inclusion : (w.adicCompletion E)ˣ →* CompletionClassExtension v w x :=
  CompletionUnitCocycle.inclusion (representative v w x)

/-- The projection to the completed-field automorphism group. -/
abbrev projection : CompletionClassExtension v w x →* CompletionGalois v w :=
  CompletionUnitCocycle.projection (representative v w x)

/-- The distinguished set-theoretic section of the chosen representative. -/
abbrev sectionMap : CompletionGalois v w → CompletionClassExtension v w x :=
  CompletionUnitCocycle.sectionMap (representative v w x)

theorem inclusion_injective : Function.Injective (inclusion v w x) :=
  CompletionUnitCocycle.inclusion_injective _

theorem projection_surjective : Function.Surjective (projection v w x) :=
  CompletionUnitCocycle.projection_surjective _

theorem exact : (inclusion v w x).range = (projection v w x).ker :=
  CompletionUnitCocycle.exact _

theorem continuous_inclusion : Continuous (inclusion v w x) :=
  CompletionUnitCocycle.continuous_inclusion _

theorem continuous_projection : Continuous (projection v w x) :=
  CompletionUnitCocycle.continuous_projection _

theorem continuous_sectionMap : Continuous (sectionMap v w x) :=
  NormalizedTwoCocycle.Extension.continuous_sectionMap _

/-- The unit inclusion with its proved continuity. -/
def continuousInclusion : (w.adicCompletion E)ˣ →ₜ* CompletionClassExtension v w x where
  toMonoidHom := inclusion v w x
  continuous_toFun := continuous_inclusion v w x

/-- The quotient projection with its proved continuity. -/
def continuousProjection : CompletionClassExtension v w x →ₜ* CompletionGalois v w where
  toMonoidHom := projection v w x
  continuous_toFun := continuous_projection v w x

theorem isOpenQuotientMap_projection : IsOpenQuotientMap (projection v w x) :=
  ⟨projection_surjective v w x, continuous_projection v w x,
    isOpenMap_snd.comp
      (NormalizedTwoCocycle.Extension.homeomorphProd (representative v w x)).isOpenMap⟩

theorem isOpenEmbedding_inclusion : IsOpenEmbedding (inclusion v w x) where
  toIsEmbedding :=
    (NormalizedTwoCocycle.Extension.homeomorphProd (representative v w x)).symm.isEmbedding.comp
      (isEmbedding_prodMkLeft (1 : CompletionGalois v w))
  isOpen_range := by
    have h : Set.range (inclusion v w x) = (projection v w x) ⁻¹' {1} := by
      ext t
      change t ∈ (inclusion v w x).range ↔ t ∈ (projection v w x).ker
      rw [exact v w x]
    rw [h]
    exact (isOpen_discrete {1}).preimage (continuous_projection v w x)

theorem factorSet (σ τ : CompletionGalois v w) :
    sectionMap v w x σ * sectionMap v w x τ * (sectionMap v w x (σ * τ))⁻¹ =
      inclusion v w x (representative v w x (σ, τ)) :=
  CompletionUnitCocycle.factorSet _ σ τ

theorem conjugation (t : CompletionClassExtension v w x) (a : (w.adicCompletion E)ˣ) :
    t * inclusion v w x a * t⁻¹ = inclusion v w x (projection v w x t • a) :=
  NormalizedTwoCocycle.Extension.conjugate_inl _ t a

section Representative

variable {x} (z : CompletionUnitCocycle v w) (hz : z.cohomologyClass = x)

/-- Change from any supplied representative to the chosen representative, over both ends. -/
abbrev equivOfRepresentative :
    CompletionUnitCocycle.Extension z ≃ₜ* CompletionClassExtension v w x :=
  NormalizedTwoCocycle.continuousEquivOfCohomologyClassEq
    (hz.trans (cohomologyClass_representative v w x).symm)

theorem equivOfRepresentative_inclusion (a : (w.adicCompletion E)ˣ) :
    equivOfRepresentative v w z hz (CompletionUnitCocycle.inclusion z a) =
      inclusion v w x a :=
  NormalizedTwoCocycle.continuousEquivOfCohomologyClassEq_inl _ a

theorem projection_equivOfRepresentative (t : CompletionUnitCocycle.Extension z) :
    projection v w x (equivOfRepresentative v w z hz t) =
      CompletionUnitCocycle.projection z t := rfl

theorem equivOfRepresentative_symm_inclusion (a : (w.adicCompletion E)ˣ) :
    (equivOfRepresentative v w z hz).symm (inclusion v w x a) =
      CompletionUnitCocycle.inclusion z a :=
  NormalizedTwoCocycle.continuousEquivOfCohomologyClassEq_symm_inl _ a

theorem projection_equivOfRepresentative_symm (t : CompletionClassExtension v w x) :
    CompletionUnitCocycle.projection z ((equivOfRepresentative v w z hz).symm t) =
      projection v w x t := rfl

end Representative

section Global

variable [Normal F E] (y : relativeIdeleClassCohomology F E 2)

/-- Continuous homomorphisms between the constructed local and global class extensions. -/
abbrev GlobalHom := CompletionClassExtension v w x →ₜ* ClassExtension y

/-- Equality of the local image and restricted global class in the existing cohomology. -/
def GlobalCompatible : Prop :=
  localIdeleClassMap v w 2 x = decompositionRestriction v w 2 y

variable (h : GlobalCompatible v w x y)

include h in
theorem exists_globalCochain :
    ∃ b, LocalCocycleMap.Compatible v w
      (representative v w x) (ClassExtension.representative y) b := by
  apply (LocalCocycleMap.exists_compatible_iff v w
    (representative v w x) (ClassExtension.representative y)).mpr
  rw [cohomologyClass_representative, ClassExtension.cohomologyClass_representative]
  exact h

/-- Choose a cochain from the explicit cohomological compatibility hypothesis. -/
def globalCochain : CompletionGalois v w → IdeleClassGroup (𝓞 E) E :=
  (exists_globalCochain v w x y h).choose

theorem globalCochain_spec :
    LocalCocycleMap.Compatible v w (representative v w x)
      (ClassExtension.representative y) (globalCochain v w x y h) :=
  (exists_globalCochain v w x y h).choose_spec

/-- The actual continuous homomorphism obtained from compatible local and global H2 classes. -/
def toGlobal : GlobalHom v w x y :=
  LocalCocycleMap.toExtension v w (representative v w x) (ClassExtension.representative y)
    (globalCochain v w x y h) (globalCochain_spec v w x y h)

theorem toGlobal_left (t : CompletionClassExtension v w x) :
    (toGlobal v w x y h t).left =
      IdeleClassGroup.ofAdicCompletion (𝓞 E) E w t.left * globalCochain v w x y h t.right :=
  rfl

theorem toGlobal_right (t : CompletionClassExtension v w x) :
    (toGlobal v w x y h t).right = decompositionHom v w t.right := rfl

theorem toGlobal_inclusion (a : (w.adicCompletion E)ˣ) :
    toGlobal v w x y h (inclusion v w x a) =
      ClassExtension.inclusion y (IdeleClassGroup.ofAdicCompletion (𝓞 E) E w a) :=
  LocalCocycleMap.toExtension_inclusion v w _ _ _ _ a

theorem projection_toGlobal (t : CompletionClassExtension v w x) :
    ClassExtension.projection y (toGlobal v w x y h t) =
      decompositionHom v w (projection v w x t) := rfl

theorem toGlobal_sectionMap (σ : CompletionGalois v w) :
    toGlobal v w x y h (sectionMap v w x σ) =
      ClassExtension.inclusion y (globalCochain v w x y h σ) *
        ClassExtension.sectionMap y (decompositionHom v w σ) :=
  LocalCocycleMap.toExtension_sectionMap v w _ _ _ _ σ

end Global

end CompletionClassExtension
end Langlands.ClassField.Global
