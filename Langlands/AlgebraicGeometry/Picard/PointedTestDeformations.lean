import Langlands.AlgebraicGeometry.Picard.Groupoid
import Langlands.CategoryTheory.Sites.PseudofunctorPointedDeformations

/-! # Actual Picard deformations on arbitrary pointed tests -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Bicategory AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AlgebraicGeometry.Picard.PicardGroupoid

namespace PointedTestDeformations

open Langlands.CategoryTheory

variable {S X : Scheme.{u}} (f : X ⟶ S) {T₀ : Over S}
  (M : LineBundle ((relativeSpace f).obj T₀))

/-- Actual bundles on a pointed test, with a specified reduction isomorphism from `M`. -/
abbrev Deformations (T : Under T₀) :=
  PseudofunctorPointedDeformations.Deformations (relative f) (Core.mk M) T

/-- Every compatible arrow is an actual bundle isomorphism. -/
instance deformationsGroupoid (T : Under T₀) : Groupoid (Deformations f M T) :=
  Groupoid.ofIsIso (fun h ↦ isIso_of_reflects_iso h
    (StructuredArrow.proj (Core.mk M) ((relative f).map T.hom.op.toLoc).toFunctor))

/-- The actual chosen reduction isomorphism of a deformation. -/
def reductionIso {T : Under T₀} (A : Deformations f M T) :
    M ≅ (LineBundle.pullback ((relativeSpace f).map T.hom)).obj A.right.of :=
  A.hom.iso

/-- Construct a pointed deformation from a bundle and its specified reduction. -/
def mk (T : Under T₀) (L : LineBundle ((relativeSpace f).obj T.right))
    (e : M ≅ (LineBundle.pullback ((relativeSpace f).map T.hom)).obj L) :
    Deformations f M T :=
  StructuredArrow.mk (CoreHom.mk e)

/-- A pointed arrow respects the specified reduction isomorphisms. -/
lemma hom_compatibility {T : Under T₀} {A B : Deformations f M T} (a : A ⟶ B) :
    reductionIso f M A ≪≫
      (LineBundle.pullback ((relativeSpace f).map T.hom)).mapIso a.right.iso =
        reductionIso f M B :=
  congrArg CoreHom.iso (StructuredArrow.w a)

/-- Construct a pointed arrow from an actual compatible bundle isomorphism. -/
def homMk {T : Under T₀} {A B : Deformations f M T} (e : A.right.of ≅ B.right.of)
    (h : reductionIso f M A ≪≫
      (LineBundle.pullback ((relativeSpace f).map T.hom)).mapIso e = reductionIso f M B) :
    A ⟶ B :=
  StructuredArrow.homMk (CoreHom.mk e) (by apply CoreHom.ext; exact h)

/-- Ordinary pullback of a pointed deformation along a map of pointed tests. -/
abbrev restrict {T U : Under T₀} (q : T ⟶ U) :
    Deformations f M U ⥤ Deformations f M T :=
  PseudofunctorPointedDeformations.restrict (relative f) (Core.mk M) q

/-- The underlying bundle is the ordinary relative pullback. -/
lemma restrict_obj_bundle {T U : Under T₀} (q : T ⟶ U) (A : Deformations f M U) :
    ((restrict f M q).obj A).right.of =
      (LineBundle.pullback ((relativeSpace f).map q.right)).obj A.right.of := rfl

/-- Direct reduction compared with reduction after ordinary relative pullback. -/
def reductionComparison {T U : Under T₀} (q : T ⟶ U)
    (L : PicardGroupoid ((relativeSpace f).obj U.right)) :
    (LineBundle.pullback ((relativeSpace f).map U.hom)).obj L.of ≅
      (LineBundle.pullback ((relativeSpace f).map T.hom)).obj
        ((LineBundle.pullback ((relativeSpace f).map q.right)).obj L.of) :=
  ((PseudofunctorPointedDeformations.restrictionComparison (relative f) q).app
    L).hom.iso

/-- Pullback retains the specified reduction, composed with the ordinary comparison. -/
lemma restrict_obj_reductionIso {T U : Under T₀} (q : T ⟶ U)
    (A : Deformations f M U) :
    reductionIso f M ((restrict f M q).obj A) =
      reductionIso f M A ≪≫ reductionComparison f q A.right :=
  congrArg CoreHom.iso
    (PseudofunctorPointedDeformations.restrict_obj_hom (relative f) (Core.mk M) q A)

/-- Restriction of arrows is ordinary pullback of actual bundle isomorphisms. -/
lemma restrict_map_iso {T U : Under T₀} (q : T ⟶ U)
    {A B : Deformations f M U} (a : A ⟶ B) :
    ((restrict f M q).map a).right.iso =
      (LineBundle.pullback ((relativeSpace f).map q.right)).mapIso a.right.iso := rfl

/-- The identity comparison retains the pointed reduction. -/
abbrev restrictIdIso (T : Under T₀) :
    restrict f M (𝟙 T) ≅ 𝟭 (Deformations f M T) :=
  PseudofunctorPointedDeformations.restrictIdIso (relative f) (Core.mk M) T

/-- The composition comparison retains the pointed reduction. -/
abbrev restrictCompIso {T U V : Under T₀} (q : T ⟶ U) (r : U ⟶ V) :
    restrict f M (q ≫ r) ≅ restrict f M r ⋙ restrict f M q :=
  PseudofunctorPointedDeformations.restrictCompIso (relative f) (Core.mk M) q r

/-- The actual pointed Picard deformation pseudofunctor on all pointed scheme tests. -/
abbrev pseudofunctor : LocallyDiscrete (Under T₀)ᵒᵖ ⥤ᵖ Cat :=
  PseudofunctorPointedDeformations.pseudofunctor (relative f) (Core.mk M)

end PointedTestDeformations

end Langlands.AlgebraicGeometry.Picard.PicardGroupoid
