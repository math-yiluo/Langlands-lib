import Langlands.CategoryTheory.Renard.UniformCompletionStatements

/-!
# Renard A.III.1: proof for the separated uniform completion

The actual completion map and extension give the canonical factorization and
its unique structured-arrow morphisms, with no source separation assumption.
-/

open CategoryTheory UniformSpace

universe u v

namespace Langlands.Renard.UniformCompletion

/-- The actual completion and its canonical map have the stated properties. -/
theorem completionMap_proof : CompletionMapStatement.{u} := by
  intro X _
  refine ⟨inferInstance, inferInstance, Completion.uniformContinuous_coe X,
    Completion.denseRange_coe, Completion.isUniformInducing_coe X, ?_⟩
  intro h
  exact @Completion.isUniformEmbedding_coe X _ h

/-- The actual extension is uniformly continuous, factors the map, and is unique. -/
theorem concreteExtension_proof : ConcreteExtensionStatement.{u, v} := by
  intro X _ Y _ _ _ f hf
  refine ⟨Completion.uniformContinuous_extension, Completion.extension_coe hf, ?_⟩
  intro g hg h
  exact (Completion.extension_unique hf hg (fun x => (h x).symm)).symm

/-- The supplied bundled extension is exactly the unique categorical factor. -/
theorem categoricalExtension_proof : CategoricalExtensionStatement.{u} := by
  intro X Y f
  let : T0Space ((forget₂ CpltSepUniformSpace UniformSpaceCat).obj Y) :=
    CpltSepUniformSpace.t0Space Y
  let : CompleteSpace ((forget₂ CpltSepUniformSpace UniformSpaceCat).obj Y) :=
    CpltSepUniformSpace.completeSpace Y
  constructor
  · apply UniformSpaceCat.hom_ext
    funext x
    exact Completion.extension_coe f.hom.property x
  · intro g hg
    apply InducedCategory.hom_ext
    apply UniformSpaceCat.hom_ext
    apply (Completion.extension_unique f.hom.property g.hom.hom.property ?_).symm
    intro x
    exact (congrArg (fun k => k x) hg).symm

/-- Unique extensions make the chosen canonical structured arrow initial. -/
theorem rightUniversal_proof : RightUniversalStatement.{u} := by
  intro X
  refine ⟨Limits.IsInitial.ofUniqueHom
    (fun c => StructuredArrow.homMk (UniformSpaceCat.extensionHom c.hom)
      (categoricalExtension_proof X c.right c.hom).1) ?_⟩
  intro c m
  apply StructuredArrow.hom_ext
  exact (categoricalExtension_proof X c.right c.hom).2 m.right (StructuredArrow.w m)

/-- Renard A.III.1: the full separated uniform-completion aggregate. -/
theorem uniformCompletionStatements_proof : UniformCompletionStatements.{u, v} :=
  ⟨completionMap_proof, concreteExtension_proof,
    categoricalExtension_proof, rightUniversal_proof⟩

end Langlands.Renard.UniformCompletion
