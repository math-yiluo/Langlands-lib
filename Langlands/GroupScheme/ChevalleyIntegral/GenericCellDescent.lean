import Langlands.GroupScheme.ChevalleyIntegral.FieldCellIntersection
import Langlands.GroupScheme.ChevalleyIntegral.AmbientChangeBase
import Langlands.GroupScheme.ChevalleyIntegral.GenericClosure
import Langlands.GroupScheme.GenericSubgroupClosureFactorization

/-! # Descent of the generic ordered cell -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.ChevalleyIntegral

variable {R K : Type u} [CommRing R] [Field K]
  [Algebra R K] [IsFractionRing R K]

/-- The projection from the generic fibre of any scheme over the domain. -/
def genericSchemeProjection (W : Over (Spec (CommRingCat.of R))) :
    (Over.map (Spec.algebraMap R K)).obj
      ((Over.pullback (Spec.algebraMap R K)).obj W) ⟶ W :=
  (Over.mapPullbackAdj (Spec.algebraMap R K)).counit.app W

instance genericSchemeProjection_schematic
    (W : Over (Spec (CommRingCat.of R))) [Flat W.hom] :
    IsSchemeTheoreticallyDominant (genericSchemeProjection (K := K) W).left := by
  change IsSchemeTheoreticallyDominant (pullback.fst W.hom (Spec.algebraMap R K))
  infer_instance

end Langlands.GroupScheme.ChevalleyIntegral

namespace Langlands.GroupScheme.SplitExistence.ChevalleyData

open ChevalleyIntegral

variable {J X Y : Type u} [AddCommGroup X] [AddCommGroup Y]
  {P : RootDatum J X Y} {b : P.Base} (D : ChevalleyData P b)
  [Fintype J] [DecidableEq J]
  {R K : Type u} [CommRing R] [Field K]
  [Algebra R K] [IsFractionRing R K]

/-- Generic field factorization descends to a flat scheme over the domain. -/
theorem exists_orderedCellFactor_of_generic [P.IsReduced] [Module.Finite ℤ X]
    (C : D.ChevGroup K) {W : Over (Spec (CommRingCat.of R))} [Flat W.hom]
    (f : (Over.pullback (Spec.algebraMap R K)).obj W ⟶ C.H.X) [Flat f.left]
    (g : W ⟶ D.ambientCellSpace (CommRingCat.of R))
    (hg : D.matrixRestrict (Spec.algebraMap R K) _ (f ≫ C.i.hom.hom) =
      genericSchemeProjection (K := K) W ≫ g ≫ D.ambientCellMap (CommRingCat.of R)) :
    ∃ a : W ⟶ D.orderedCellSpace (CommRingCat.of R) D.neg.posList D.posList,
      a ≫ D.fullOrderedCellToAmbient (CommRingCat.of R) = g := by
  let a := Spec.algebraMap R K
  let T := (Over.pullback a).obj W
  let x := genericSchemeProjection (K := K) W ≫ g
  let y := D.ambientCellExtend a T x
  have hy : f ≫ C.i.hom.hom = y ≫ D.ambientCellMap (CommRingCat.of K) := by
    apply (GeneralLinear.pointsEquiv (Fin D.n) (CommRingCat.of K) T).injective
    have he := congrArg
      (GeneralLinear.pointsEquiv (Fin D.n) (CommRingCat.of R) ((Over.map a).obj T))
      (hg.trans (D.ambientCellExtend_comp a T x).symm)
    change GeneralLinear.pointsEquiv (Fin D.n) (CommRingCat.of R) ((Over.map a).obj T)
      (D.matrixRestrict a T (f ≫ C.i.hom.hom)) = _ at he
    simp only [D.pointsEquiv_matrixRestrict] at he
    exact he
  obtain ⟨z, hz⟩ := C.exists_orderedCellFactor f y hy
  let w := (Over.map a).map z ≫ D.orderedCellRestrict a D.neg.posList D.posList
  have hw : w ≫ D.fullOrderedCellToAmbient (CommRingCat.of R) = x := by
    have := D.isOpenImmersion_ambientCellMap (CommRingCat.of R)
    have : Mono (D.ambientCellMap (CommRingCat.of R)) := Over.mono_of_mono_left _
    apply (cancel_mono (D.ambientCellMap (CommRingCat.of R))).mp
    rw [Category.assoc, D.fullOrderedCellToAmbient_comp]
    dsimp only [w]
    rw [Category.assoc, D.orderedCellRestrict_comp, ← D.matrixRestrict_comp,
      ← D.fullOrderedCellToAmbient_comp, ← Category.assoc, hz]
    exact D.ambientCellExtend_comp a T x
  exact exists_over_factor_of_schematic_precomp
    (D.fullOrderedCellToAmbient (CommRingCat.of R))
    (genericSchemeProjection (K := K) W) g w hw.symm

/-- The integral ordered parameters recovered from a compatible generic flat map. -/
def genericOrderedCellFactor [P.IsReduced] [Module.Finite ℤ X]
    (C : D.ChevGroup K) {W : Over (Spec (CommRingCat.of R))} [Flat W.hom]
    (f : (Over.pullback (Spec.algebraMap R K)).obj W ⟶ C.H.X) [Flat f.left]
    (g : W ⟶ D.ambientCellSpace (CommRingCat.of R))
    (hg : D.matrixRestrict (Spec.algebraMap R K) _ (f ≫ C.i.hom.hom) =
      genericSchemeProjection (K := K) W ≫ g ≫ D.ambientCellMap (CommRingCat.of R)) :
    W ⟶ D.orderedCellSpace (CommRingCat.of R) D.neg.posList D.posList :=
  (D.exists_orderedCellFactor_of_generic C f g hg).choose

@[reassoc (attr := simp)]
theorem genericOrderedCellFactor_comp [P.IsReduced] [Module.Finite ℤ X]
    (C : D.ChevGroup K) {W : Over (Spec (CommRingCat.of R))} [Flat W.hom]
    (f : (Over.pullback (Spec.algebraMap R K)).obj W ⟶ C.H.X) [Flat f.left]
    (g : W ⟶ D.ambientCellSpace (CommRingCat.of R))
    (hg : D.matrixRestrict (Spec.algebraMap R K) _ (f ≫ C.i.hom.hom) =
      genericSchemeProjection (K := K) W ≫ g ≫ D.ambientCellMap (CommRingCat.of R)) :
    D.genericOrderedCellFactor C f g hg ≫
      D.fullOrderedCellToAmbient (CommRingCat.of R) = g :=
  (D.exists_orderedCellFactor_of_generic C f g hg).choose_spec

end Langlands.GroupScheme.SplitExistence.ChevalleyData
