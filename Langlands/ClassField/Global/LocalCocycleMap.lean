import Langlands.ClassField.Global.CohomologyMaps
import Langlands.ClassField.Global.ClassExtension
import Langlands.Global.Adelic

/-! # Maps from completed-local cocycle extensions to idele-class extensions -/

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

/-- The actual automorphism group of the finite completed extension. -/
abbrev CompletionGalois := w.adicCompletion E ≃ₐ[v.adicCompletion F] w.adicCompletion E

/-- The finite completed automorphism group is given its discrete topology. -/
@[instance_reducible]
def completionGaloisTopology : TopologicalSpace (CompletionGalois v w) := ⊥

attribute [local instance] completionGaloisTopology relativeGaloisTopology
  relativeIdeleClassAction

instance completionGaloisDiscreteTopology : DiscreteTopology (CompletionGalois v w) := ⟨rfl⟩

instance completionUnitsContinuousSMul :
    ContinuousSMul (CompletionGalois v w) (w.adicCompletion E)ˣ where
  continuous_smul := continuous_prod_of_discrete_left.mpr fun σ =>
    (continuous_localAut v w σ).units_map σ.toMonoidHom

/-- Normalized cocycles for the actual completed field unit action. -/
abbrev CompletionUnitCocycle :=
  NormalizedTwoCocycle (CompletionGalois v w) (w.adicCompletion E)ˣ

namespace CompletionUnitCocycle

variable {v w} (z : CompletionUnitCocycle v w)

/-- The product-coordinate extension of the completed automorphism group by local units. -/
abbrev Extension := NormalizedTwoCocycle.Extension z

instance extensionIsTopologicalGroup : IsTopologicalGroup (Extension z) :=
  NormalizedTwoCocycle.Extension.topologicalGroup z continuous_of_discreteTopology

/-- Inclusion of the actual completed field units. -/
abbrev inclusion : (w.adicCompletion E)ˣ →* Extension z :=
  NormalizedTwoCocycle.Extension.inl z

/-- Projection to the actual completed automorphism group. -/
abbrev projection : Extension z →* CompletionGalois v w :=
  NormalizedTwoCocycle.Extension.projection z

/-- The distinguished set-theoretic section. -/
abbrev sectionMap : CompletionGalois v w → Extension z :=
  NormalizedTwoCocycle.Extension.sectionMap z

theorem inclusion_injective : Function.Injective (inclusion z) :=
  NormalizedTwoCocycle.Extension.inl_injective z

theorem projection_surjective : Function.Surjective (projection z) :=
  NormalizedTwoCocycle.Extension.projection_surjective z

theorem exact : (inclusion z).range = (projection z).ker :=
  NormalizedTwoCocycle.Extension.range_inl_eq_ker_projection z

theorem continuous_inclusion : Continuous (inclusion z) :=
  NormalizedTwoCocycle.Extension.continuous_inl z

theorem continuous_projection : Continuous (projection z) :=
  NormalizedTwoCocycle.Extension.continuous_projection z

theorem factorSet (σ τ : CompletionGalois v w) :
    sectionMap z σ * sectionMap z τ * (sectionMap z (σ * τ))⁻¹ =
      inclusion z (z (σ, τ)) :=
  NormalizedTwoCocycle.Extension.sectionMap_factorSet z σ τ

/-- The same normalized cocycle in the existing local cohomology complex. -/
abbrev toCocycle₂ :
    groupCohomology.cocycles₂ (unitsRepresentation (padicField v).Carrier
      (w.adicCompletion E)) :=
  NormalizedTwoCocycle.toCocycle₂ z

/-- Its class in the existing local second cohomology, without fundamental-class selection. -/
abbrev cohomologyClass :=
  groupCohomology.H2π _ (toCocycle₂ z)

end CompletionUnitCocycle

namespace LocalCocycleMap

variable [Normal F E]
variable (z : CompletionUnitCocycle v w) (y : RelativeIdeleCocycle F E)

/-- Continuous homomorphisms between these two actual cocycle extensions. -/
abbrev ExtensionHom :=
  CompletionUnitCocycle.Extension z →ₜ* RelativeIdeleCocycle.Extension y

/-- The explicit compatibility equation, with the actual local coefficient map. -/
def Compatible (b : CompletionGalois v w → IdeleClassGroup (𝓞 E) E) : Prop :=
  ∀ σ τ, IdeleClassGroup.ofAdicCompletion (𝓞 E) E w (z (σ, τ)) * b (σ * τ) =
    b σ * relativeIdeleClassAut F E (decompositionHom v w σ) (b τ) *
      y (decompositionHom v w σ, decompositionHom v w τ)

variable (b : CompletionGalois v w → IdeleClassGroup (𝓞 E) E)
  (hb : Compatible v w z y b)

/-- Specialize the generic cochain construction using proved arithmetic equivariance. -/
def mapData : NormalizedTwoCocycle.MapData z y
    (IdeleClassGroup.ofAdicCompletion (𝓞 E) E w) (decompositionHom v w) where
  cochain := b
  equivariant σ a :=
    (relativeIdeleClassAut_decompositionHom_ofAdicCompletion v w σ a).symm
  compatible := hb

/-- The constructed continuous homomorphism `(a,σ) ↦ (i_w(a)b(σ),ρ(σ))`. -/
def toExtension : ExtensionHom v w z y where
  toMonoidHom := (mapData v w z y b hb).toMonoidHom
  continuous_toFun := (mapData v w z y b hb).continuous
    (Langlands.Global.finiteClassInclusion E w).continuous
    continuous_of_discreteTopology continuous_of_discreteTopology

@[simp] theorem toExtension_left (t : CompletionUnitCocycle.Extension z) :
    (toExtension v w z y b hb t).left =
      IdeleClassGroup.ofAdicCompletion (𝓞 E) E w t.left * b t.right := rfl

@[simp] theorem toExtension_right (t : CompletionUnitCocycle.Extension z) :
    (toExtension v w z y b hb t).right = decompositionHom v w t.right := rfl

@[simp] theorem toExtension_inclusion (a : (w.adicCompletion E)ˣ) :
    toExtension v w z y b hb (CompletionUnitCocycle.inclusion z a) =
      RelativeIdeleCocycle.inclusion y (IdeleClassGroup.ofAdicCompletion (𝓞 E) E w a) :=
  (mapData v w z y b hb).toMonoidHom_inl a

theorem projection_toExtension (t : CompletionUnitCocycle.Extension z) :
    RelativeIdeleCocycle.projection y (toExtension v w z y b hb t) =
      decompositionHom v w (CompletionUnitCocycle.projection z t) := rfl

theorem toExtension_sectionMap (σ : CompletionGalois v w) :
    toExtension v w z y b hb (CompletionUnitCocycle.sectionMap z σ) =
      RelativeIdeleCocycle.inclusion y (b σ) *
        RelativeIdeleCocycle.sectionMap y (decompositionHom v w σ) :=
  (mapData v w z y b hb).toMonoidHom_sectionMap σ

/-- The existing cohomological compatibility is exactly existence of a usable cochain. -/
theorem exists_compatible_iff :
    (∃ b, Compatible v w z y b) ↔
      localIdeleClassMap v w 2 z.cohomologyClass =
        decompositionRestriction v w 2 y.cohomologyClass :=
  (localIdeleClassMap_eq_decompositionRestriction_iff v w z.toCocycle₂ y).symm

/-- Cohomological compatibility gives an actual continuous extension map over both ends. -/
theorem exists_toExtension
    (h : localIdeleClassMap v w 2 z.cohomologyClass =
      decompositionRestriction v w 2 y.cohomologyClass) :
    ∃ f : ExtensionHom v w z y,
      (∀ a, f (CompletionUnitCocycle.inclusion z a) =
        RelativeIdeleCocycle.inclusion y (IdeleClassGroup.ofAdicCompletion (𝓞 E) E w a)) ∧
      ∀ t, RelativeIdeleCocycle.projection y (f t) =
        decompositionHom v w (CompletionUnitCocycle.projection z t) := by
  obtain ⟨b, hb⟩ := (exists_compatible_iff v w z y).mpr h
  exact ⟨toExtension v w z y b hb, toExtension_inclusion v w z y b hb,
    projection_toExtension v w z y b hb⟩

end LocalCocycleMap
end Langlands.ClassField.Global
