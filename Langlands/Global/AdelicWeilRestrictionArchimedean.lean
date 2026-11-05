import Langlands.Global.AdelicFunctoriality.Norm
import Langlands.Global.PositiveRealIdeles
import Langlands.Global.AdelicGroupPoints
import Langlands.GroupScheme.AffineWeilRestriction

/-! # Actual real points of a number-field Weil restriction -/

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField
open scoped TensorProduct NumberField.LiesOver CategoryTheory.MonObj

namespace Langlands.Global.AdelicWeilRestriction

open Langlands.GroupScheme
open AdelicFunctoriality

variable (F : Type) [Field F] [NumberField F]

/-- Every infinite place of `F` lies over the unique infinite place of `ℚ`. -/
theorem liesOver_ratInfinitePlace (v : InfinitePlace F) : v.LiesOver Rat.infinitePlace :=
  ⟨congrArg Subtype.val (Subsingleton.elim (v.comap (algebraMap ℚ F)) Rat.infinitePlace)⟩

attribute [local instance] liesOver_ratInfinitePlace

/-- The actual real completion of `ℚ`, as a `ℚ`-algebra isomorphism from `ℝ`. -/
def realRatCompletion : ℝ ≃ₐ[ℚ] Rat.infinitePlace.Completion :=
  (InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace).symm.toRatAlgEquiv

theorem continuous_realRatCompletion : Continuous (realRatCompletion) :=
  (InfinitePlace.Completion.isometryEquivRealOfIsReal Rat.isReal_infinitePlace).symm.continuous

/-- The completion map from the rational real completion is the actual real embedding. -/
theorem completionMap_realRatCompletion (v : InfinitePlace F) (r : ℝ) :
    NumberField.LiesOver.completionMap (w := v) (realRatCompletion r) =
      PositiveRealIdeles.realEmbedding F v r := by
  have h := (Rat.denseRange_cast (𝕜 := ℝ)).equalizer
    (g := fun r : ℝ => NumberField.LiesOver.completionMap (w := v) (realRatCompletion r))
    (NumberField.LiesOver.continuous_completionMap.comp continuous_realRatCompletion)
    (PositiveRealIdeles.continuous_realEmbedding F v)
    (funext fun q => by simp only [Function.comp_apply, map_ratCast])
  exact congrFun h r

/-- Reindex the product over places above the rational place by all infinite places. -/
def aboveRatProductEquiv :
    ((q : InfinitePlacesAbove F Rat.infinitePlace) → q.1.Completion) ≃+*
      InfiniteAdeles F where
  toFun a v := a ⟨v, liesOver_ratInfinitePlace F v⟩
  invFun a q := a q.1
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

/-- The canonical ring isomorphism, through the completed tensor decomposition. -/
def realTensorRingEquiv : F ⊗[ℚ] ℝ ≃+* InfiniteAdeles F :=
  (((Algebra.TensorProduct.comm ℚ F ℝ).trans
      (Algebra.TensorProduct.congr realRatCompletion AlgEquiv.refl)).toRingEquiv.trans
    (infiniteTensorEquiv (L := F) Rat.infinitePlace).toRingEquiv).trans
    (aboveRatProductEquiv F)

theorem realTensorRingEquiv_tmul (x : F) (r : ℝ) (v : InfinitePlace F) :
    realTensorRingEquiv F (x ⊗ₜ[ℚ] r) v =
      algebraMap F v.Completion x * PositiveRealIdeles.realEmbedding F v r := by
  change infiniteTensorMap (L := F) Rat.infinitePlace
      (Algebra.TensorProduct.congr realRatCompletion AlgEquiv.refl
        (Algebra.TensorProduct.comm ℚ F ℝ (x ⊗ₜ[ℚ] r)))
      ⟨v, liesOver_ratInfinitePlace F v⟩ = _
  rw [Algebra.TensorProduct.comm_tmul, Algebra.TensorProduct.congr_apply,
    Algebra.TensorProduct.map_tmul, infiniteTensorMap_tmul]
  rw [mul_comm]
  exact congrArg _ (completionMap_realRatCompletion F v r)

/-- The canonical algebra isomorphism `F ⊗[ℚ] ℝ ≃ₐ[F] InfiniteAdeles F`. -/
def realTensorEquiv : F ⊗[ℚ] ℝ ≃ₐ[F] InfiniteAdeles F :=
  AlgEquiv.ofRingEquiv (f := realTensorRingEquiv F) fun x => by
    funext v
    rw [Algebra.TensorProduct.algebraMap_apply, realTensorRingEquiv_tmul, map_one, mul_one]
    rfl

/-- At each place, a pure tensor goes to the product of the two canonical images. -/
@[simp] theorem realTensorEquiv_tmul (x : F) (r : ℝ) (v : InfinitePlace F) :
    realTensorEquiv F (x ⊗ₜ[ℚ] r) v =
      algebraMap F v.Completion x * PositiveRealIdeles.realEmbedding F v r :=
  realTensorRingEquiv_tmul F x r v

variable (G : GroupScheme (Spec (CommRingCat.of F)))
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]

/-- The actual real points of the restricted group recover the original infinite adelic points. -/
def realPointsEquiv :
    (AffineWeil.groupScheme ℚ F G).affinePoints (CommAlgCat.of (CommRingCat.of ℚ) ℝ) ≃*
      InfiniteAdelicGroupPoints F G :=
  (AffineWeil.pointsEquiv ℚ F G ℝ).trans
    (G.affinePointFunctor.mapIso (CommAlgCat.isoMk (realTensorEquiv F))).groupIsoToMulEquiv

/-- The comparison is the tensor-valued point map followed by the coefficient isomorphism. -/
theorem realPointsEquiv_apply
    (p : (AffineWeil.groupScheme ℚ F G).affinePoints (CommAlgCat.of (CommRingCat.of ℚ) ℝ)) :
    realPointsEquiv F G p = G.affinePointMap
      (CommAlgCat.ofHom (realTensorEquiv F).toAlgHom) (AffineWeil.pointsEquiv ℚ F G ℝ p) := rfl

end Langlands.Global.AdelicWeilRestriction
