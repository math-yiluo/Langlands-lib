import Langlands.AlgebraicGeometry.Picard.RelativeAutomorphisms
import Langlands.CategoryTheory.Sites.PseudofunctorParallelIsomorphisms

/-! # Smooth schemes of parallel Picard isomorphisms -/

universe u

open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard.PicardGroupoid

open Langlands.CategoryTheory.PseudofunctorPointFiber

variable {S X : Scheme.{u}} (f : X ⟶ S) {U T : Over S}
  (L : LineBundle ((relativeSpace f).obj U)) (a b : T ⟶ U)

/-- All actual isomorphisms between the two fixed endpoint pullbacks, with
all tests over their common scheme base. -/
def parallelIsomorphismPresheaf : AlgebraicSpace.Presheaf T.left :=
  (T.iteratedSliceBackward.op ⋙ parallelIsoPresheaf (relative f) (Core.mk L) a b) ⋙
    uliftFunctor.{u + 1}

variable (e : ((relative f).map a.op.toLoc).toFunctor.obj (Core.mk L) ≅
  ((relative f).map b.op.toLoc).toFunctor.obj (Core.mk L))

/-- A fixed actual arrow identifies the full relative automorphism presheaf
of its source family with all parallel actual arrows. -/
def parallelAutomorphismComparison :
    relativeSliceAutomorphismPresheaf f T
        (((relative f).map a.op.toLoc).toFunctor.obj (Core.mk L)).of ≅
      parallelIsomorphismPresheaf f L a b := by
  letI (V : Over S) : IsGroupoid ((relative f).obj (.mk (op V))) := by
    change IsGroupoid (Core (LineBundle ((relativeSpace f).obj V)))
    infer_instance
  exact isoWhiskerRight (isoWhiskerLeft T.iteratedSliceBackward.op
    (((relative f).overMapCompPresheafHomIso (Core.mk L) (Core.mk L) a).symm ≪≫
      isoWhiskerLeft (Over.map a).op (presheafHomAutomorphismIso (relative f) (Core.mk L)) ≪≫
        automorphismParallelIso (relative f) (Core.mk L) a b e)) uliftFunctor.{u + 1}

include e in
/-- Given an actual arrow, smooth relative automorphism representatives give
a smooth scheme representing every parallel arrow on the complete test slice. -/
lemma exists_parallelIsomorphismScheme (h : HasSmoothRelativeAutomorphismSchemes f) :
    ∃ P : Over T.left,
      Nonempty ((AlgebraicSpace.schemeYoneda T.left).obj P ≅
        parallelIsomorphismPresheaf f L a b) ∧ Smooth P.hom := by
  obtain ⟨P, ⟨eP⟩, hP⟩ := h T
    (((relative f).map a.op.toLoc).toFunctor.obj (Core.mk L)).of
  exact ⟨P, ⟨eP ≪≫ parallelAutomorphismComparison f L a b e⟩, hP⟩

end Langlands.AlgebraicGeometry.Picard.PicardGroupoid
