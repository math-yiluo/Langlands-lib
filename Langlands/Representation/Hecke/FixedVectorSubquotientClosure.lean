import Langlands.Representation.Hecke.IdempotentGenerationBridge
import Langlands.Representation.Category.Abelian
import Langlands.Representation.Classification.SupercuspidalSupport

/-! # From actual subquotient generation to categorical subobject closure -/

open CategoryTheory

universe u v

namespace Langlands.Hecke

variable {G : Type u} [Group G] [TopologicalSpace G]

/-- The pointwise subquotient closure of generation by the fixed vectors of `K`. -/
def fixedVectorSubquotientClosure (K : OpenSubgroup G) : Prop :=
  ∀ V : SmoothRep.{0, u, v} ℂ G, fixedVectorGeneratedProperty K V →
    ∀ D : SmoothRep.{0, u, v} ℂ G, SmoothRep.IsSubquotient D V →
      fixedVectorGeneratedProperty K D

/-- Actual subquotient closure implies closure under categorical monomorphisms. -/
theorem fixedVectorGenerated_closedUnderSubobjects_of_subquotients (K : OpenSubgroup G)
    (h : fixedVectorSubquotientClosure.{u, v} K) :
    (fixedVectorGeneratedProperty.{u, v} K).IsClosedUnderSubobjects where
  prop_of_mono {X Y} f _ hY :=
    h Y hY X (SmoothRep.IsSubrepresentation.isSubquotient
      ⟨f, (SmoothRep.mono_iff_injective f).mp inferInstance⟩)

end Langlands.Hecke
