import Langlands.Global.AdelicGLInverseTranspose
import Langlands.Global.AdelicGroupProduct
import Langlands.Global.AdelicLocalInclusion
import Langlands.Global.FiniteAdelicGL.LocalFactor
import Langlands.TraceFormula.GeneralLinearBaseChangeLocal

/-! # The local insertion in the two adelic general-linear models -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory AlgebraicGeometry NumberField
open scoped CategoryTheory.MonObj

namespace Langlands.Global.GeneralLinearGroupPoints

open AdelicGroupPoints TraceFormula

local instance localInsertionIsAffine (K : Type u) [Field K] (n : ℕ) :
    IsAffine (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of K)).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme (Fin n) (CommRingCat.of K)

variable (K : Type u) [Field K] [NumberField K] (n : ℕ)

local notation "G" => GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of K)

private theorem matrix_map_adelicHomeomorph (a : AdelicGroupPoints K G) (w : Place K) :
    Matrix.GeneralLinearGroup.map (adeleProjection K w).toRingHom (adelicHomeomorph K n a) =
      localGLHomeomorph K n w (atPlace K G w a) :=
  (GroupScheme.GeneralLinear.affinePointsEquiv_naturality
    (n := Fin n) (R := CommRingCat.of K) (CommAlgCat.ofHom (adeleProjection K w)) a).symm

/-- Inserting a finite local point and passing to adelic matrix coordinates
agrees with insertion of the corresponding local matrix. -/
def GeneralLinearLocalInclusionComparisonStatement : Prop :=
  ∀ (v : FinitePlace K) (y : PlaceGroupPoints K G (.inr v)),
    adelicHomeomorph K n (ofPlace K G (.inr v) y) =
      AdelicGL.ofFinite K n (FiniteAdelicGL.localInclusion K n v (localGLHomeomorph K n (.inr v) y))

set_option maxHeartbeats 3000000 in
theorem adelicHomeomorph_ofPlace : GeneralLinearLocalInclusionComparisonStatement K n := by
  intro v y
  let a := ofPlace K G (.inr v) y
  apply AdelicGL.ext_infinite_finite
  · rw [AdelicGL.infinite_ofFinite]
    apply Units.ext
    apply Matrix.ext
    intro i j
    funext w
    have h := matrix_map_adelicHomeomorph K n a (.inl w)
    change _ = localGLHomeomorph K n (.inl w) (atPlace K G (.inl w) (ofPlace K G (.inr v) y)) at h
    rw [atPlace_ofPlace_of_ne K G _ _ (by simp), map_one] at h
    have he := congrArg (fun g : GeneralLinear n w.Completion => g.val i j) h
    change ((adelicHomeomorph K n a).val i j).1 w = (1 : Matrix (Fin n) (Fin n) w.Completion) i j at he
    change ((adelicHomeomorph K n a).val i j).1 w =
      ((1 : Matrix (Fin n) (Fin n) (InfiniteAdeleRing K)) i j) w
    rw [he]
    by_cases hij : i = j <;> simp only [Matrix.one_apply, hij, ite_true, ite_false] <;> rfl
  · rw [AdelicGL.finite_ofFinite]
    apply FiniteAdelicGL.ext_localProjection
    intro w
    have h : FiniteAdelicGL.localProjection K n w (AdelicGL.finite K n (adelicHomeomorph K n a)) =
        localGLHomeomorph K n (.inr w) (atPlace K G (.inr w) (ofPlace K G (.inr v) y)) := by
      have hz := matrix_map_adelicHomeomorph K n a (.inr w)
      apply Units.ext
      apply Matrix.ext
      intro i j
      exact congrArg (fun g : FiniteLocalGL K n w => g.val i j) hz
    rcases eq_or_ne w v with rfl | hw
    · rw [FiniteAdelicGL.localProjection_localInclusion]
      simpa only [atPlace_ofPlace_same] using h
    · rw [FiniteAdelicGL.localProjection_localInclusion_of_ne K n v w hw]
      simpa only [atPlace_ofPlace_of_ne K G _ _ (show (.inr w : Place K) ≠ .inr v from
        fun hh => hw (Sum.inr.inj hh)), map_one] using h

end Langlands.Global.GeneralLinearGroupPoints
