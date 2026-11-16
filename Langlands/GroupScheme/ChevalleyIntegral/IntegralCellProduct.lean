import Langlands.GroupScheme.ChevalleyIntegral.ClosureCell
import Langlands.GroupScheme.Rational.SteinbergRootProduct

/-! # Ordered products in the integral Chevalley closure -/

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

/-- Multiply the root maps with the supplied scheme-valued scalar coordinates. -/
def rootProduct (T : Over (Spec (CommRingCat.of R))) (l : List J)
    (c : J → Γ(T.left, ⊤)) :
    T ⟶ (genericModel D R K C).group.X :=
  (l.map fun j => VectorGroup.scalarPoint (CommRingCat.of R) T (c j) ≫
    rootOver D R K C j).prod

omit [IsDedekindDomain R] in
private theorem gaCoordOver_scalarPoint (T : Over (Spec (CommRingCat.of R)))
    (c : Γ(T.left, ⊤)) :
    Multiplicative.toAdd (gaCoordOver (CommRingCat.of R) T
      (VectorGroup.scalarPoint (CommRingCat.of R) T c)) = c :=
  VectorGroup.coordinates_scalarPoint _ T c 0

/-- The root product has the expected matrix on every test scheme. -/
theorem pointsEquiv_rootProduct (T : Over (Spec (CommRingCat.of R))) (l : List J)
    (c : J → Γ(T.left, ⊤)) :
    GeneralLinear.pointsEquiv (Fin D.n) (CommRingCat.of R) T
      (rootProduct D R K C T l c ≫ (modelInclusion D R K C).hom.hom) =
        D.opmGL l c := by
  induction l with
  | nil =>
    change GeneralLinear.pointsEquiv (Fin D.n) (CommRingCat.of R) T
      ((1 : T ⟶ (genericModel D R K C).group.X) ≫
        (modelInclusion D R K C).hom.hom) = 1
    rw [MonObj.one_comp]
    exact map_one _
  | cons j l ih =>
    simp only [rootProduct, List.map_cons, List.prod_cons] at ih ⊢
    rw [MonObj.mul_comp, map_mul, Category.assoc, rootOver_comp,
      D.pointsEquiv_rootToGLOver, gaCoordOver_scalarPoint, ih]
    rfl

variable [DecidableEq J]

/-- The universal ordered root product mapped to the integral closure. -/
def orderedRootProduct (l : List J) :
    D.orderedRootSpace (CommRingCat.of R) l ⟶ (genericModel D R K C).group.X :=
  rootProduct D R K C _ l
    (fun j => if hj : j ∈ l then
      D.orderedRootPointsEquiv (CommRingCat.of R) l _ (𝟙 _) ⟨j, hj⟩ else 0)

@[reassoc (attr := simp)]
theorem orderedRootProduct_comp (l : List J) :
    orderedRootProduct D R K C l ≫ (modelInclusion D R K C).hom.hom =
      D.orderedRootMapOver (CommRingCat.of R) l := by
  apply (GeneralLinear.pointsEquiv (Fin D.n) (CommRingCat.of R) _).injective
  rw [orderedRootProduct, pointsEquiv_rootProduct]
  simpa only [Category.id_comp] using
    (D.pointsEquiv_orderedRootMapOver (CommRingCat.of R) l _ (𝟙 _)).symm

/-- The negative-root, torus and positive-root products in the integral closure. -/
def orderedCellProduct (lm lp : List J) :
    D.orderedCellSpace (CommRingCat.of R) lm lp ⟶
      (genericModel D R K C).group.X :=
  (fst _ _ ≫ orderedRootProduct D R K C lm) *
    ((snd _ _ ≫ fst _ _ ≫ torusOver D R K C) *
      (snd _ _ ≫ snd _ _ ≫ orderedRootProduct D R K C lp))

@[reassoc (attr := simp)]
theorem orderedCellProduct_comp (lm lp : List J) :
    orderedCellProduct D R K C lm lp ≫ (modelInclusion D R K C).hom.hom =
      D.orderedCellMap (CommRingCat.of R) lm lp := by
  simp only [orderedCellProduct, MonObj.mul_comp, Category.assoc,
    orderedRootProduct_comp, torusOver_comp, orderedCellMap]
  rfl

end Langlands.GroupScheme.ChevalleyIntegral
