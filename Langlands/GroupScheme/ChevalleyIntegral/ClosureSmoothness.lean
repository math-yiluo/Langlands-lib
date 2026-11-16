import Langlands.GroupScheme.ChevalleyIntegral.IntegralOpenCell
import Langlands.GroupScheme.Lie.SmoothOpenChart
import Langlands.GroupScheme.SmoothProducts
import Mathlib.AlgebraicGeometry.Morphisms.SmoothFiber

/-! # Smoothness of the fixed integral Chevalley closure -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SplitExistence.ChevalleyData

variable {J X Y : Type u} [AddCommGroup X] [AddCommGroup Y]
  {P : RootDatum J X Y} {b : P.Base} (D : ChevalleyData P b)
  (R : CommRingCat.{u}) [Fintype J]

/-- The finite ordered root parameter scheme is smooth over its base ring. -/
theorem smooth_orderedRootSpace (l : List J) :
    Smooth (D.orderedRootSpace R l).hom := by
  classical
  let : Algebra.Smooth R (MvPolynomial {j : J // j ∈ l} R) :=
    ⟨inferInstance, inferInstance⟩
  change Smooth (Spec.map (CommRingCat.ofHom
    (algebraMap R (MvPolynomial {j : J // j ∈ l} R))))
  rw [HasRingHomProperty.Spec_iff (P := @Smooth)]
  change (algebraMap R (MvPolynomial {j : J // j ∈ l} R)).Smooth
  rw [RingHom.smooth_algebraMap]
  infer_instance

/-- The root parameters and full character torus form a smooth parameter scheme. -/
theorem smooth_orderedCellSpace [Module.Finite ℤ X] (lm lp : List J) :
    Smooth (D.orderedCellSpace R lm lp).hom := by
  have := isTorsionFree_weight P
  let B := Module.Free.chooseBasis ℤ X
  have hT : Smooth (TR (X := X) R).toGrp.X.hom :=
    (Diagonalizable.isSplitTorus R B.equivFun.toAddEquiv).smooth
  exact smooth_tensor _ _ (D.neg.smooth_orderedRootSpace R lm)
    (smooth_tensor _ _ hT (D.smooth_orderedRootSpace R lp))

end Langlands.GroupScheme.SplitExistence.ChevalleyData

namespace Langlands.GroupScheme.ChevalleyIntegral

open SplitExistence.ChevalleyData

variable {J X Y : Type u} [AddCommGroup X] [AddCommGroup Y]
  {P : RootDatum J X Y} {b : P.Base}
  (D : SplitExistence.ChevalleyData P b)
  (R : Type u) [CommRing R] (k : Type u) [Field k]
  (v : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R))

/-- Ordered root and torus parameters over a field-valued point of the base. -/
def fieldOrderedCellSpace (lm lp : List J) : Over (Spec (CommRingCat.of k)) :=
  (Over.pullback v).obj (D.orderedCellSpace (CommRingCat.of R) lm lp)

/-- Zero root coordinates and the torus identity give a point in every field chart. -/
theorem fieldOrderedCellSpace_nonempty (lm lp : List J) :
    Nonempty (fieldOrderedCellSpace D R k v lm lp).left := by
  let T : Over (Spec (CommRingCat.of R)) := Over.mk v
  let qm : T ⟶ D.neg.orderedRootSpace (CommRingCat.of R) lm :=
    (D.neg.orderedRootPointsEquiv (CommRingCat.of R) lm T).symm (fun _ => 0)
  let qt : T ⟶ (TR (X := X) (CommRingCat.of R)).toGrp.X := 1
  let qp : T ⟶ D.orderedRootSpace (CommRingCat.of R) lp :=
    (D.orderedRootPointsEquiv (CommRingCat.of R) lp T).symm (fun _ => 0)
  let q : T ⟶ D.orderedCellSpace (CommRingCat.of R) lm lp :=
    lift qm (lift qt qp)
  let s : Spec (CommRingCat.of k) ⟶
      (fieldOrderedCellSpace D R k v lm lp).left :=
    pullback.lift q.left (𝟙 _)
      (by simpa only [T, Over.mk_left, Over.mk_hom, Category.id_comp] using q.w)
  exact ⟨s ⟨⊥, inferInstance⟩⟩

/-- Smoothness of the parameter scheme persists over every field-valued point. -/
theorem fieldOrderedCellSpace_smooth [Fintype J] [Module.Finite ℤ X] (lm lp : List J) :
    Smooth (fieldOrderedCellSpace D R k v lm lp).hom := by
  have := D.smooth_orderedCellSpace (CommRingCat.of R) lm lp
  exact inferInstanceAs (Smooth
    (pullback.snd (D.orderedCellSpace (CommRingCat.of R) lm lp).hom v))

variable (K : Type u) [IsDedekindDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K] (C : D.ChevGroup K)
  [Fintype J] [DecidableEq J] [P.IsReduced] [Module.Finite ℤ X]

/-- Every field fibre of the fixed closure has a nonempty smooth open chart. -/
theorem genericModel_hasNonemptySmoothOpenChart :
    HasNonemptySmoothOpenChart ((GroupScheme.baseChange v).obj
      (genericModel D R K C).group) := by
  let U := fieldOrderedCellSpace D R k v D.neg.posList D.posList
  let j : U ⟶ ((GroupScheme.baseChange v).obj (genericModel D R K C).group).X :=
    (Over.pullback v).map (orderedCellProduct D R K C D.neg.posList D.posList)
  refine ⟨U, j, fieldOrderedCellSpace_smooth D R k v _ _,
    fieldOrderedCellSpace_nonempty D R k v _ _, ?_⟩
  exact MorphismProperty.overPullbackMap (P := @IsOpenImmersion) v _
    (isOpenImmersion_orderedCellProduct D R K C)

/-- The fixed schematic closure is smooth over the Dedekind base. -/
theorem genericModel_isSmooth : (genericModel D R K C).IsSmooth := by
  apply Smooth.of_smooth_fiberToSpecResidueField
  intro y
  let v := (Spec (CommRingCat.of R)).fromSpecResidueField y
  let H := (GroupScheme.baseChange v).obj (genericModel D R K C).group
  have : LocallyOfFiniteType H.X.hom :=
    inferInstanceAs (LocallyOfFiniteType
      (pullback.snd (genericModel D R K C).group.X.hom v))
  exact (genericModel_hasNonemptySmoothOpenChart D R
    ((Spec (CommRingCat.of R)).residueField y) v K C).smooth

omit [IsDedekindDomain R] in
/-- In particular, the single chosen model over the lifted integers is smooth. -/
theorem integerModel_isSmooth : (integerModel D).IsSmooth :=
  genericModel_isSmooth D (ULift.{u} ℤ) (FractionRing (ULift.{u} ℤ)) (integerGenericGroup D)

end Langlands.GroupScheme.ChevalleyIntegral
