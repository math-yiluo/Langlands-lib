import Langlands.GroupScheme.ChevalleyIntegral.GenericCellDescent
import Langlands.GroupScheme.ChevalleyIntegral.TorusClosure
import Langlands.GroupScheme.ChevalleyIntegral.RootClosure

/-! # The ordered cell in the generic Chevalley closure -/

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

private theorem matrixRestrict_genericMap
    {W : Over (Spec (CommRingCat.of R))}
    (f : W ⟶ (genericModel D R K C).group.X) :
    D.matrixRestrict (Spec.algebraMap R K) _
      (((Over.pullback (Spec.algebraMap R K)).map f ≫
        (genericModel D R K C).genericIso.hom.hom.hom) ≫ C.i.hom.hom) =
      genericSchemeProjection (K := K) W ≫ f ≫ (modelInclusion D R K C).hom.hom := by
  let a := Spec.algebraMap R K
  have hh := congrArg (fun h => h.hom.hom) (modelInclusion_generic D R K C)
  change (Over.pullback a).map (modelInclusion D R K C).hom.hom ≫
      (GeneralLinear.baseChangeIso (Fin D.n) a).hom.hom.hom =
    (genericModel D R K C).genericIso.hom.hom.hom ≫ C.i.hom.hom at hh
  rw [Category.assoc, ← hh]
  simp only [SplitExistence.ChevalleyData.matrixRestrict, Category.assoc,
    ← Grp.comp_hom_hom]
  change baseChangePointsEquiv a (D.GLR (CommRingCat.of R)) ((Over.pullback a).obj W)
      ((Over.pullback a).map f ≫
        (Over.pullback a).map (modelInclusion D R K C).hom.hom ≫
          ((GeneralLinear.baseChangeIso (Fin D.n) a).hom ≫
            (GeneralLinear.baseChangeIso (Fin D.n) a).inv).hom.hom) =
    genericSchemeProjection (K := K) W ≫ f ≫ (modelInclusion D R K C).hom.hom
  simp only [Iso.hom_inv_id, Grp.id_hom_hom]
  apply Over.OverMorphism.ext
  change (((Over.pullback a).map f).left ≫
      ((Over.pullback a).map (modelInclusion D R K C).hom.hom).left) ≫
        pullback.fst _ a =
    pullback.fst W.hom a ≫ f.left ≫ (modelInclusion D R K C).hom.hom.left
  simp [Over.pullback_map_left, Category.assoc]

variable [Fintype J] [DecidableEq J] [P.IsReduced] [Module.Finite ℤ X]

/-- A flat scheme mapping compatibly to the closure and ambient cell factors
through the full integral ordered parameter product. -/
theorem exists_closureCellFactor
    {W : Over (Spec (CommRingCat.of R))}
    (f : W ⟶ (genericModel D R K C).group.X) [Flat f.left]
    (g : W ⟶ D.ambientCellSpace (CommRingCat.of R))
    (hg : f ≫ (modelInclusion D R K C).hom.hom =
      g ≫ D.ambientCellMap (CommRingCat.of R)) :
    ∃ q : W ⟶ D.orderedCellSpace (CommRingCat.of R) D.neg.posList D.posList,
      q ≫ D.fullOrderedCellToAmbient (CommRingCat.of R) = g := by
  have : Flat W.hom := by
    rw [← f.w]
    infer_instance
  let a := Spec.algebraMap R K
  have : Flat ((Over.pullback a).map f).left :=
    MorphismProperty.overPullbackMap (P := @Flat) a f inferInstance
  have : IsIso (genericModel D R K C).genericIso.hom.hom.hom.left :=
    (Over.forget _).map_isIso (genericModel D R K C).genericIso.hom.hom.hom
  let fk := (Over.pullback a).map f ≫ (genericModel D R K C).genericIso.hom.hom.hom
  have : Flat fk.left := by
    dsimp only [fk, Over.comp_left]
    infer_instance
  apply D.exists_orderedCellFactor_of_generic C fk g
  rw [matrixRestrict_genericMap D R K C f, hg]

/-- The chosen full parameter factorization of a flat ambient-cell intersection. -/
def closureCellFactor
    {W : Over (Spec (CommRingCat.of R))}
    (f : W ⟶ (genericModel D R K C).group.X) [Flat f.left]
    (g : W ⟶ D.ambientCellSpace (CommRingCat.of R))
    (hg : f ≫ (modelInclusion D R K C).hom.hom =
      g ≫ D.ambientCellMap (CommRingCat.of R)) :
    W ⟶ D.orderedCellSpace (CommRingCat.of R) D.neg.posList D.posList :=
  (exists_closureCellFactor D R K C f g hg).choose

@[reassoc (attr := simp)]
theorem closureCellFactor_comp
    {W : Over (Spec (CommRingCat.of R))}
    (f : W ⟶ (genericModel D R K C).group.X) [Flat f.left]
    (g : W ⟶ D.ambientCellSpace (CommRingCat.of R))
    (hg : f ≫ (modelInclusion D R K C).hom.hom =
      g ≫ D.ambientCellMap (CommRingCat.of R)) :
    closureCellFactor D R K C f g hg ≫
      D.fullOrderedCellToAmbient (CommRingCat.of R) = g :=
  (exists_closureCellFactor D R K C f g hg).choose_spec

end Langlands.GroupScheme.ChevalleyIntegral
