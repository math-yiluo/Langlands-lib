import Langlands.Shimura.Coefficients.EtaleTorsorPullback
import Langlands.Geometry.EtaleDerivedSections
import Mathlib.CategoryTheory.Limits.MorphismProperty
import Mathlib.CategoryTheory.Linear.FunctorCategory
import Mathlib.CategoryTheory.Sites.Pullback

/-! # Direct image on small etale sites for arbitrary scheme morphisms -/

noncomputable section

universe u uA vA

namespace Langlands.Geometry.EtaleDirectImage

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Langlands.Shimura.Coefficients

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {X Z : Scheme.{u}} (f : Z ⟶ X)

/-- Geometric base change on small-etale objects preserves finite limits. -/
instance objectPullback_preservesFiniteLimits :
    PreservesFiniteLimits (etaleObjectPullback f) :=
  inferInstanceAs (PreservesFiniteLimits (MorphismProperty.Over.pullback (@Etale) ⊤ f))

/-- Geometric base change preserves small-etale covering sieves. -/
theorem objectPullback_coverPreserving :
    CoverPreserving X.smallEtaleTopology Z.smallEtaleTopology
      (etaleObjectPullback f) where
  cover_preserve {U S} hS := by
    change (S.functorPushforward (etaleObjectPullback f)) ∈
      (MorphismProperty.Over.forget (@Etale) ⊤ Z).restrictedTopology
        (Z.overGrothendieckTopology (@Etale)) _
    rw [Functor.mem_restrictedTopology_iff, ← Sieve.functorPushforward_comp]
    change S.functorPushforward
      (MorphismProperty.Over.forget (@Etale) ⊤ X ⋙ CategoryTheory.Over.pullback f) ∈ _
    rw [Sieve.functorPushforward_comp]
    exact (GrothendieckTopology.coverPreserving_overPullback
      Scheme.etaleTopology f).cover_preserve
        ((Functor.coverPreserving_restrictedTopology
          (MorphismProperty.Over.forget (@Etale) ⊤ X)
          (X.overGrothendieckTopology (@Etale))).cover_preserve hS)

/-- Arbitrary scheme base change is continuous on the small-etale sites. -/
instance objectPullback_isContinuous :
    (etaleObjectPullback f).IsContinuous X.smallEtaleTopology Z.smallEtaleTopology := by
  have : RepresentablyFlat (etaleObjectPullback f) :=
    flat_of_preservesFiniteLimits _
  exact Functor.isContinuous_iff_coverPreserving.2
    (objectPullback_coverPreserving f)

variable (A : Type uA) [Category.{vA} A]

/-- Direct image evaluates a sheaf over Z on the actual geometric base change
of every small-etale object over X. -/
def directImage : Sheaf Z.smallEtaleTopology A ⥤ Sheaf X.smallEtaleTopology A :=
  (etaleObjectPullback f).sheafPushforwardContinuous A
    X.smallEtaleTopology Z.smallEtaleTopology

@[simp] theorem directImage_obj_obj (F : Sheaf Z.smallEtaleTopology A)
    (U : X.Etaleᵒᵖ) :
    ((directImage f A).obj F).obj.obj U =
      F.obj.obj ((etaleObjectPullback f).op.obj U) := rfl

/-- Direct image retains the original coefficient morphism on each
geometrically pulled-back test object. -/
@[simp] theorem directImage_map_app {F F' : Sheaf Z.smallEtaleTopology A}
    (a : F ⟶ F') (U : X.Etaleᵒᵖ) :
    ((directImage f A).map a).hom.app U =
      a.hom.app ((etaleObjectPullback f).op.obj U) := rfl

section Linear

variable (R : Type u) [CommRing R]

instance directImage_additive : (directImage f (ModuleCat.{u} R)).Additive where
  map_add := by
    intros
    apply Sheaf.hom_ext
    rfl

instance directImage_linear : (directImage f (ModuleCat.{u} R)).Linear R where
  map_smul a r := by
    apply Sheaf.hom_ext
    rfl

end Linear

end Langlands.Geometry.EtaleDirectImage
