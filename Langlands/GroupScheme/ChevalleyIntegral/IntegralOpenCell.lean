import Langlands.GroupScheme.ChevalleyIntegral.IntegralCellProduct

/-! # The open ordered cell of the integral Chevalley closure -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.ChevalleyIntegral

open SplitExistence.ChevalleyData

variable {J X Y : Type u} [AddCommGroup X] [AddCommGroup Y]
  {P : RootDatum J X Y} {b : P.Base}
  (D : SplitExistence.ChevalleyData P b)
  (R K : Type u) [CommRing R] [IsDedekindDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K] (C : D.ChevGroup K)

/-- The scheme-theoretic intersection of the closure with the ambient matrix cell. -/
def cellIntersection : Over (Spec (CommRingCat.of R)) :=
  Over.mk (pullback.fst (modelInclusion D R K C).hom.hom.left
    (D.ambientCellMap (CommRingCat.of R)).left ≫ (genericModel D R K C).group.X.hom)

/-- The open projection of the cell intersection to the closure. -/
def cellIntersectionFst : cellIntersection D R K C ⟶ (genericModel D R K C).group.X :=
  Over.homMk (pullback.fst _ _) rfl

/-- The projection of the intersection to the ambient matrix cell. -/
def cellIntersectionSnd : cellIntersection D R K C ⟶ D.ambientCellSpace (CommRingCat.of R) :=
  Over.homMk (pullback.snd _ _) (by
    rw [← (D.ambientCellMap (CommRingCat.of R)).w, ← Category.assoc,
      ← pullback.condition, Category.assoc, (modelInclusion D R K C).hom.hom.w]
    rfl)

@[reassoc]
theorem cellIntersection_condition :
    cellIntersectionFst D R K C ≫ (modelInclusion D R K C).hom.hom =
      cellIntersectionSnd D R K C ≫ D.ambientCellMap (CommRingCat.of R) :=
  Over.OverMorphism.ext pullback.condition

instance cellIntersectionFst_open :
    IsOpenImmersion (cellIntersectionFst D R K C).left := by
  have := D.isOpenImmersion_ambientCellMap (CommRingCat.of R)
  change IsOpenImmersion (pullback.fst _ (D.ambientCellMap (CommRingCat.of R)).left)
  infer_instance

variable [Fintype J] [DecidableEq J]

/-- The ordered parameter product mapped to the ambient-cell intersection. -/
def orderedCellToIntersection :
    D.orderedCellSpace (CommRingCat.of R) D.neg.posList D.posList ⟶
      cellIntersection D R K C :=
  Over.homMk (pullback.lift
    (orderedCellProduct D R K C D.neg.posList D.posList).left
    (D.fullOrderedCellToAmbient (CommRingCat.of R)).left
    (by
      change (orderedCellProduct D R K C D.neg.posList D.posList ≫
        (modelInclusion D R K C).hom.hom).left =
          (D.fullOrderedCellToAmbient (CommRingCat.of R) ≫
            D.ambientCellMap (CommRingCat.of R)).left
      rw [orderedCellProduct_comp, D.fullOrderedCellToAmbient_comp]))
    (by
      change _ ≫ (pullback.fst _ _ ≫ (genericModel D R K C).group.X.hom) = _
      rw [← Category.assoc, pullback.lift_fst]
      exact (orderedCellProduct D R K C D.neg.posList D.posList).w)

@[reassoc (attr := simp)]
theorem orderedCellToIntersection_fst :
    orderedCellToIntersection D R K C ≫ cellIntersectionFst D R K C =
      orderedCellProduct D R K C D.neg.posList D.posList :=
  Over.OverMorphism.ext (pullback.lift_fst _ _ _)

@[reassoc (attr := simp)]
theorem orderedCellToIntersection_snd :
    orderedCellToIntersection D R K C ≫ cellIntersectionSnd D R K C =
      D.fullOrderedCellToAmbient (CommRingCat.of R) :=
  Over.OverMorphism.ext (pullback.lift_snd _ _ _)

variable [P.IsReduced] [Module.Finite ℤ X]

/-- Recover all ordered parameters on the ambient-cell intersection. -/
def intersectionToOrderedCell :
    cellIntersection D R K C ⟶
      D.orderedCellSpace (CommRingCat.of R) D.neg.posList D.posList :=
  closureCellFactor D R K C (cellIntersectionFst D R K C)
    (cellIntersectionSnd D R K C) (cellIntersection_condition D R K C)

@[reassoc (attr := simp)]
theorem intersectionToOrderedCell_comp :
    intersectionToOrderedCell D R K C ≫ D.fullOrderedCellToAmbient (CommRingCat.of R) =
      cellIntersectionSnd D R K C :=
  closureCellFactor_comp D R K C _ _ _

private theorem mono_of_closed_over {S : Scheme.{u}} {A B : Over S}
    (f : A ⟶ B) [IsClosedImmersion f.left] : Mono f := by
  have : Mono f.left := SurjectiveOnStalks.mono_of_injective
    (IsClosedImmersion.isClosedEmbedding f.left).injective
  exact Over.mono_of_mono_left _

/-- The full ordered parameter scheme is the actual open-cell intersection. -/
def integralCellIso :
    D.orderedCellSpace (CommRingCat.of R) D.neg.posList D.posList ≅
      cellIntersection D R K C where
  hom := orderedCellToIntersection D R K C
  inv := intersectionToOrderedCell D R K C
  hom_inv_id := by
    have : Mono (D.fullOrderedCellToAmbient (CommRingCat.of R)) := mono_of_closed_over _
    apply (cancel_mono (D.fullOrderedCellToAmbient (CommRingCat.of R))).mp
    simp only [Category.assoc, intersectionToOrderedCell_comp,
      orderedCellToIntersection_snd, Category.id_comp]
  inv_hom_id := by
    have : Mono (cellIntersectionFst D R K C) := Over.mono_of_mono_left _
    have : IsClosedImmersion (modelInclusion D R K C).hom.hom.left :=
      modelInclusion_closed D R K C
    have : Mono (modelInclusion D R K C).hom.hom := mono_of_closed_over _
    apply (cancel_mono (cellIntersectionFst D R K C)).mp
    rw [Category.assoc, orderedCellToIntersection_fst, Category.id_comp]
    apply (cancel_mono (modelInclusion D R K C).hom.hom).mp
    rw [Category.assoc, orderedCellProduct_comp,
      ← D.fullOrderedCellToAmbient_comp, ← Category.assoc,
      intersectionToOrderedCell_comp, ← cellIntersection_condition]

/-- The full negative-root, torus and positive-root product is open in the closure. -/
theorem isOpenImmersion_orderedCellProduct :
    IsOpenImmersion (orderedCellProduct D R K C D.neg.posList D.posList).left := by
  have : IsIso (orderedCellToIntersection D R K C).left :=
    (Over.forget _).map_isIso (integralCellIso D R K C).hom
  rw [← orderedCellToIntersection_fst, Over.comp_left]
  infer_instance

end Langlands.GroupScheme.ChevalleyIntegral
