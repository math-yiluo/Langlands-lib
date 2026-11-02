import Langlands.Representation.Category.Abelian
import Mathlib.CategoryTheory.Preadditive.LeftExact

/-! # Exact inclusion of smooth representations -/

noncomputable section

namespace Langlands.SmoothRep

open CategoryTheory CategoryTheory.Limits

universe uR uG uV

variable (R : Type uR) [CommRing R] (G : Type uG) [Group G] [TopologicalSpace G]

/-- Kernels of smooth representations are the ambient algebraic kernels, so
the inclusion preserves finite limits. -/
instance toRep_preservesFiniteLimits :
    PreservesFiniteLimits (toRep : SmoothRep.{uR, uG, uV} R G ⥤ Rep.{uV} R G) := by
  have : ∀ {A B : SmoothRep.{uR, uG, uV} R G} (f : A ⟶ B),
      PreservesLimit (parallelPair f 0) (toRep (R := R) (G := G)) :=
    fun f => (smoothRepProperty R G).preservesKernels_ι f
  exact Functor.preservesFiniteLimits_of_preservesKernels _

/-- Cokernels of smooth representations are the ambient algebraic cokernels,
so the inclusion preserves finite colimits. -/
instance toRep_preservesFiniteColimits :
    PreservesFiniteColimits (toRep : SmoothRep.{uR, uG, uV} R G ⥤ Rep.{uV} R G) := by
  have : ∀ {A B : SmoothRep.{uR, uG, uV} R G} (f : A ⟶ B),
      PreservesColimit (parallelPair f 0) (toRep (R := R) (G := G)) :=
    fun f => (smoothRepProperty R G).preservesCokernels_ι f
  exact Functor.preservesFiniteColimits_of_preservesCokernels _

end Langlands.SmoothRep
