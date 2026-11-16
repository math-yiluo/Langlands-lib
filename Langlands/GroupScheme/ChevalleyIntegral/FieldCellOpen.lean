import Langlands.GroupScheme.ChevalleyIntegral.FieldCellImage
import Langlands.GroupScheme.ChevalleyIntegral.IntegralOpenCell
import Langlands.GroupScheme.ChevalleyIntegral.NeutralExistence

/-! # Nonempty opens in the full field fibres of the Chevalley closure -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.ChevalleyIntegral

open SplitExistence.ChevalleyData

variable {J X Y : Type u} [AddCommGroup X] [AddCommGroup Y]
  {P : RootDatum J X Y} {b : P.Base}
  (D : SplitExistence.ChevalleyData P b)
  (R K : Type u) [CommRing R] [IsDedekindDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K] (C : D.ChevGroup K)
  (k : Type u) [Field k] (ρ : CommRingCat.of R ⟶ CommRingCat.of k)
  [DecidableEq J]

omit [IsDedekindDomain R] [DecidableEq J] in
private theorem nonempty_fieldOrderedCellSpace (lm lp : List J) :
    Nonempty (((Over.pullback (Spec.map ρ)).obj
      (D.orderedCellSpace (CommRingCat.of R) lm lp)).left) := by
  let T : Over (Spec (CommRingCat.of R)) := Over.mk (Spec.map ρ)
  let qm : T ⟶ D.neg.orderedRootSpace (CommRingCat.of R) lm :=
    (D.neg.orderedRootPointsEquiv (CommRingCat.of R) lm T).symm (fun _ => 0)
  let qt : T ⟶ (TR (X := X) (CommRingCat.of R)).toGrp.X := 1
  let qp : T ⟶ D.orderedRootSpace (CommRingCat.of R) lp :=
    (D.orderedRootPointsEquiv (CommRingCat.of R) lp T).symm (fun _ => 0)
  let q : T ⟶ D.orderedCellSpace (CommRingCat.of R) lm lp :=
    lift qm (lift qt qp)
  let s : Spec (CommRingCat.of k) ⟶
      ((Over.pullback (Spec.map ρ)).obj
        (D.orderedCellSpace (CommRingCat.of R) lm lp)).left :=
    pullback.lift q.left (𝟙 _)
      (by simpa only [T, Over.mk_left, Over.mk_hom, Category.id_comp] using q.w)
  exact ⟨s ⟨⊥, inferInstance⟩⟩

variable [Fintype J] [P.IsReduced] [Module.Finite ℤ X]

/-- The full ordered integral product remains an open immersion over any field. -/
theorem isOpenImmersion_fieldOrderedCellProduct :
    IsOpenImmersion ((Over.pullback (Spec.map ρ)).map
      (orderedCellProduct D R K C D.neg.posList D.posList)).left :=
  MorphismProperty.overPullbackMap (P := @IsOpenImmersion) (Spec.map ρ) _
    (isOpenImmersion_orderedCellProduct D R K C)

/-- The open image of the full ordered cell in the full base-changed closure. -/
def fullFieldCellOpen : (fieldModel D R K C k ρ).X.left.Opens := by
  letI := isOpenImmersion_fieldOrderedCellProduct D R K C k ρ
  exact ((Over.pullback (Spec.map ρ)).map
    (orderedCellProduct D R K C D.neg.posList D.posList)).left.opensRange

theorem fullFieldCellOpen_nonempty : (fullFieldCellOpen D R K C k ρ).1.Nonempty := by
  obtain ⟨x⟩ := nonempty_fieldOrderedCellSpace D R k ρ D.neg.posList D.posList
  exact ⟨_, ⟨x, rfl⟩⟩

/-- This open of the full fibre is contained in every supplied field Chevalley image. -/
theorem fullFieldCellOpen_subset (H : D.ChevGroup k) :
    (fullFieldCellOpen D R K C k ρ).1 ⊆
      Set.range (fieldEmbedding D R K C k ρ H).hom.hom.left := by
  intro x hx
  obtain ⟨z, rfl⟩ := hx
  refine ⟨(fieldOrderedCellFactor D R K C k ρ H D.neg.posList D.posList).left z, ?_⟩
  exact congrArg (fun f => f.left z)
    (fieldOrderedCellFactor_comp D R K C k ρ H D.neg.posList D.posList)

/-- Every field-valued base point has the nonempty full-fibre open-image property. -/
theorem exists_fullFieldOpen :
    ∃ (H : D.ChevGroup k) (U : (fieldModel D R K C k ρ).X.left.Opens),
      U.1.Nonempty ∧ U.1 ⊆ Set.range (fieldEmbedding D R K C k ρ H).hom.hom.left := by
  obtain ⟨H⟩ := D.nonempty_chevGroup k
  exact ⟨H, fullFieldCellOpen D R K C k ρ,
    fullFieldCellOpen_nonempty D R K C k ρ, fullFieldCellOpen_subset D R K C k ρ H⟩

/-- The remaining geometric input for integral existence is smoothness of the
fixed integer closures. -/
theorem integralExistence_of_smoothClosure
    (h : ∀ (I J : Type u) [Fintype I] [DecidableEq I] [Finite J]
      (P : RootDatum J (I → ℤ) (I → ℤ)) [P.IsReduced] (b : P.Base)
      (D : SplitExistence.ChevalleyData P b), (integerModel D).IsSmooth) :
    ChevalleyIntegralExistenceStatement.{u} := by
  apply integralExistence_of_smoothClosure_fullFieldOpen
  intro I J _ _ _ P _ b D
  classical
  let : Fintype J := Fintype.ofFinite J
  refine ⟨h I J P b D, ?_⟩
  intro k _ _
  exact exists_fullFieldOpen D (ULift.{u} ℤ) (FractionRing (ULift.{u} ℤ))
    (integerGenericGroup D) k (CommRingCat.ofHom (algebraMap (ULift.{u} ℤ) k))

end Langlands.GroupScheme.ChevalleyIntegral
