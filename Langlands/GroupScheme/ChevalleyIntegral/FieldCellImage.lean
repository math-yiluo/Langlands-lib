import Langlands.GroupScheme.ChevalleyIntegral.IntegralCellProduct
import Langlands.GroupScheme.ChevalleyIntegral.FieldEmbedding

/-! # Ordered integral cells in the field Chevalley subgroups -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.ChevalleyIntegral

private theorem exists_point_factor_of_baseChange
    {S S' : Scheme.{u}} (a : S' ⟶ S)
    {A M : GroupScheme S} (f : A ⟶ M)
    {B H : GroupScheme S'} (e : (baseChange a).obj A ≅ B)
    (v : B ⟶ H) (j : H ⟶ (baseChange a).obj M)
    (hv : v ≫ j = e.inv ≫ (baseChange a).map f)
    (T : Over S') (x : (Over.map a).obj T ⟶ A.X) :
    ∃ y : T ⟶ H.X,
      y ≫ j.hom.hom = (baseChangePointsEquiv a M T).symm (x ≫ f.hom.hom) := by
  refine ⟨(baseChangePointsEquiv a A T).symm x ≫ (e.hom ≫ v).hom.hom, ?_⟩
  rw [Category.assoc, ← Grp.comp_hom_hom, Category.assoc e.hom, hv,
    Iso.hom_inv_id_assoc]
  apply (baseChangePointsEquiv a M T).injective
  rw [baseChangePointsEquiv_comp, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]

open SplitExistence.ChevalleyData

variable {J X Y : Type u} [AddCommGroup X] [AddCommGroup Y]
  {P : RootDatum J X Y} {b : P.Base}
  (D : SplitExistence.ChevalleyData P b)
  (R K : Type u) [CommRing R] [IsDedekindDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K] (C : D.ChevGroup K)
  (k : Type u) [Field k] (ρ : CommRingCat.of R ⟶ CommRingCat.of k)
  (H : D.ChevGroup k)

private theorem rootProduct_comp_mem_fieldEmbedding
    (T : Over (Spec (CommRingCat.of k))) (W : Over (Spec (CommRingCat.of R)))
    (x : (Over.map (Spec.map ρ)).obj T ⟶ W)
    (l : List J) (c : J → Γ(W.left, ⊤)) :
    (baseChangePointsEquiv (Spec.map ρ) (genericModel D R K C).group T).symm
        (x ≫ rootProduct D R K C W l c) ∈
      (SubgroupFunctor.range (fieldEmbedding D R K C k ρ H)).carrier T := by
  let F := (SubgroupFunctor.range (fieldEmbedding D R K C k ρ H)).carrier T
  induction l with
  | nil =>
    simpa only [rootProduct, List.map_nil, List.prod_nil, MonObj.comp_one, map_one]
      using F.one_mem
  | cons j l ih =>
    change (baseChangePointsEquiv (Spec.map ρ) (genericModel D R K C).group T).symm
      (x ≫ ((VectorGroup.scalarPoint (CommRingCat.of R) W (c j) ≫ rootOver D R K C j) *
        rootProduct D R K C W l c)) ∈ F
    rw [MonObj.comp_mul, map_mul]
    apply F.mul_mem _ ih
    apply SubgroupFunctor.mem_range.mpr
    exact exists_point_factor_of_baseChange (Spec.map ρ) (root D R K C j)
      (VectorGroup.baseChangeIso (n := 1) ρ) (H.u j) (fieldEmbedding D R K C k ρ H)
      (root_fieldEmbedding D R K C k ρ H j) T
      (x ≫ VectorGroup.scalarPoint (CommRingCat.of R) W (c j))

variable [DecidableEq J]

private theorem orderedRootProduct_comp_mem_fieldEmbedding
    (T : Over (Spec (CommRingCat.of k))) (l : List J)
    (x : (Over.map (Spec.map ρ)).obj T ⟶ D.orderedRootSpace (CommRingCat.of R) l) :
    (baseChangePointsEquiv (Spec.map ρ) (genericModel D R K C).group T).symm
        (x ≫ orderedRootProduct D R K C l) ∈
      (SubgroupFunctor.range (fieldEmbedding D R K C k ρ H)).carrier T :=
  rootProduct_comp_mem_fieldEmbedding D R K C k ρ H T _ x l _

/-- Every ordered integral cell point on a field test scheme lies in the supplied
field Chevalley subgroup, after the canonical pullback point comparison. -/
theorem orderedCellProduct_comp_mem_fieldEmbedding
    (T : Over (Spec (CommRingCat.of k))) (lm lp : List J)
    (x : (Over.map (Spec.map ρ)).obj T ⟶
      D.orderedCellSpace (CommRingCat.of R) lm lp) :
    (baseChangePointsEquiv (Spec.map ρ) (genericModel D R K C).group T).symm
        (x ≫ orderedCellProduct D R K C lm lp) ∈
      (SubgroupFunctor.range (fieldEmbedding D R K C k ρ H)).carrier T := by
  let F := (SubgroupFunctor.range (fieldEmbedding D R K C k ρ H)).carrier T
  simp only [orderedCellProduct, MonObj.comp_mul, map_mul]
  apply F.mul_mem
  · exact orderedRootProduct_comp_mem_fieldEmbedding D R K C k ρ H T lm (x ≫ fst _ _)
  · apply F.mul_mem
    · apply SubgroupFunctor.mem_range.mpr
      exact exists_point_factor_of_baseChange (Spec.map ρ) (torus D R K C)
        (Diagonalizable.baseChangeIso (Spec.map ρ) X) H.t (fieldEmbedding D R K C k ρ H)
        (torus_fieldEmbedding D R K C k ρ H) T (x ≫ snd _ _ ≫ fst _ _)
    · exact orderedRootProduct_comp_mem_fieldEmbedding D R K C k ρ H T lp
        (x ≫ snd _ _ ≫ snd _ _)

/-- The base change of the integral ordered product factors through every supplied
field Chevalley embedding, as a morphism of schemes over the field. -/
theorem exists_fieldOrderedCellFactor (lm lp : List J) :
    ∃ q : (Over.pullback (Spec.map ρ)).obj
        (D.orderedCellSpace (CommRingCat.of R) lm lp) ⟶ H.H.X,
      q ≫ (fieldEmbedding D R K C k ρ H).hom.hom =
        (Over.pullback (Spec.map ρ)).map (orderedCellProduct D R K C lm lp) := by
  let W := D.orderedCellSpace (CommRingCat.of R) lm lp
  let T := (Over.pullback (Spec.map ρ)).obj W
  let p : (Over.map (Spec.map ρ)).obj T ⟶ W :=
    (Over.mapPullbackAdj (Spec.map ρ)).counit.app W
  have hp :
      baseChangePointsEquiv (Spec.map ρ) (genericModel D R K C).group T
        ((Over.pullback (Spec.map ρ)).map (orderedCellProduct D R K C lm lp)) =
      p ≫ orderedCellProduct D R K C lm lp := by
    apply Over.OverMorphism.ext
    change ((Over.pullback (Spec.map ρ)).map
        (orderedCellProduct D R K C lm lp)).left ≫ pullback.fst _ (Spec.map ρ) =
      pullback.fst W.hom (Spec.map ρ) ≫ (orderedCellProduct D R K C lm lp).left
    simp only [Over.pullback_map_left, pullback.lift_fst]
    rfl
  apply SubgroupFunctor.mem_range.mp
  have h := orderedCellProduct_comp_mem_fieldEmbedding D R K C k ρ H T lm lp p
  rwa [← hp, MulEquiv.symm_apply_apply] at h

/-- The actual field-valued ordered-cell factor, on the base-changed integral
parameter scheme. -/
def fieldOrderedCellFactor (lm lp : List J) :
    (Over.pullback (Spec.map ρ)).obj
      (D.orderedCellSpace (CommRingCat.of R) lm lp) ⟶ H.H.X :=
  (exists_fieldOrderedCellFactor D R K C k ρ H lm lp).choose

@[reassoc (attr := simp)]
theorem fieldOrderedCellFactor_comp (lm lp : List J) :
    fieldOrderedCellFactor D R K C k ρ H lm lp ≫
        (fieldEmbedding D R K C k ρ H).hom.hom =
      (Over.pullback (Spec.map ρ)).map (orderedCellProduct D R K C lm lp) :=
  (exists_fieldOrderedCellFactor D R K C k ρ H lm lp).choose_spec

end Langlands.GroupScheme.ChevalleyIntegral
