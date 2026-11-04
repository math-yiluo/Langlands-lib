import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic
import Mathlib.Topology.Category.UniformSpace

/-!
# Renard A.III.1: the separated uniform completion

These statements concern the actual Hausdorff completion, uniformly continuous
maps, and complete separated targets. They make the conventions for the uniform
generalization of example 2 explicit. The printed continuous-map vector-space
example requires a separate comparison. No proofs are supplied here.
-/

open CategoryTheory UniformSpace

universe u v

namespace Langlands.Renard.UniformCompletion

/-- The canonical completion map is dense and uniformly inducing, and is an
embedding when its source is separated. -/
def CompletionMapStatement : Prop :=
  ∀ (X : Type u) [UniformSpace X],
    CompleteSpace (Completion X) ∧
    T0Space (Completion X) ∧
    UniformContinuous ((↑) : X → Completion X) ∧
    DenseRange ((↑) : X → Completion X) ∧
    IsUniformInducing ((↑) : X → Completion X) ∧
    (T0Space X → IsUniformEmbedding ((↑) : X → Completion X))

/-- The actual extension of each uniformly continuous map into a complete
separated target is uniformly continuous, factors the map, and is unique. -/
def ConcreteExtensionStatement : Prop :=
  ∀ (X : Type u) [UniformSpace X] (Y : Type v) [UniformSpace Y]
    [CompleteSpace Y] [T0Space Y] (f : X → Y),
    UniformContinuous f →
    UniformContinuous (Completion.extension f) ∧
    (∀ x : X, Completion.extension f (x : Completion X) = f x) ∧
    ∀ (g : Completion X → Y), UniformContinuous g →
      (∀ x : X, g (x : Completion X) = f x) →
      g = Completion.extension f

/-- Mathlib's actual categorical extension is the unique factor through the
canonical completion morphism. -/
def CategoricalExtensionStatement : Prop :=
  ∀ (X : UniformSpaceCat.{u}) (Y : CpltSepUniformSpace.{u})
    (f : X ⟶ (forget₂ CpltSepUniformSpace UniformSpaceCat).obj Y),
    UniformSpaceCat.completionHom X ≫
      (forget₂ CpltSepUniformSpace UniformSpaceCat).map
        (UniformSpaceCat.extensionHom f) = f ∧
    ∀ (g : UniformSpaceCat.completionFunctor.obj X ⟶ Y),
      UniformSpaceCat.completionHom X ≫
        (forget₂ CpltSepUniformSpace UniformSpaceCat).map g = f →
      g = UniformSpaceCat.extensionHom f

/-- The supplied canonical completion morphism is a right universal arrow for
the actual forgetful functor from complete separated uniform spaces. -/
def RightUniversalStatement : Prop :=
  ∀ X : UniformSpaceCat.{u},
    Nonempty (StructuredArrow.IsUniversal
      (StructuredArrow.mk
        (T := forget₂ CpltSepUniformSpace UniformSpaceCat)
        (UniformSpaceCat.completionHom X)))

/-- Canonical map properties, independent-universe concrete extension, its
categorical factorization, and the right universal arrow, in that order. -/
def UniformCompletionStatements : Prop :=
  CompletionMapStatement.{u} ∧
  ConcreteExtensionStatement.{u, v} ∧
  CategoricalExtensionStatement.{u} ∧
  RightUniversalStatement.{u}

end Langlands.Renard.UniformCompletion
