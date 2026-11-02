import Langlands.GroupScheme.Torus.WeilRestrictionBaseChange
import Langlands.GroupScheme.Torus.WeilRestrictionSplit
import Langlands.GroupScheme.Torus.Lattice

/-! # The commutative Weil-restricted multiplicative group -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme.WeilGm

variable (A : CommRingCat.{u}) (B : Type u) [CommRing B] [Algebra A B]
  [Module.Finite A B] [Module.Projective A B]

/-- The Weil-restricted multiplicative group is commutative on every test scheme. -/
instance isCommMonObj : IsCommMonObj (groupScheme A B).X :=
  (isCommMonObj_iff_isMulCommutative _).2 fun T =>
    { is_comm := ⟨fun x y => (pointsEquiv A B T).injective
        (by rw [map_mul, map_mul, mul_comm])⟩ }

/-- The published Weil restriction, equipped with its commutativity certificate. -/
abbrev commGroupScheme : CommGroupScheme (Spec A) where
  toGrp := groupScheme A B

/-- Its all-test point model, with the commutative group scheme as codomain. -/
def commPointsEquiv (T : Over (Spec A)) :
    (T ⟶ (commGroupScheme A B).X) ≃* (B ⊗[A] ((algΓ A).obj T).unop)ˣ :=
  pointsEquiv A B T

theorem commPointsEquiv_naturality {T T' : Over (Spec A)} (a : T' ⟶ T)
    (x : T ⟶ (commGroupScheme A B).X) :
    commPointsEquiv A B T' (a ≫ x) =
      Units.map (Algebra.TensorProduct.lTensor (S := B) B ((algΓ A).map a).unop.hom :
        B ⊗[A] _ →* B ⊗[A] _) (commPointsEquiv A B T x) :=
  pointsEquiv_naturality A B a x

section Congr

variable {A B} {B' : Type u} [CommRing B'] [Algebra A B']
  [Module.Finite A B'] [Module.Projective A B']

/-- Transport along an algebra equivalence, in the commutative category. -/
def commCongrIso (e : B ≃ₐ[A] B') : commGroupScheme A B ≅ commGroupScheme A B' where
  hom := Additive.ofMul (congrIso e).hom
  inv := Additive.ofMul (congrIso e).inv
  hom_inv_id := congrArg Additive.ofMul (congrIso e).hom_inv_id
  inv_hom_id := congrArg Additive.ofMul (congrIso e).inv_hom_id

theorem commCongrIso_hom_points (e : B ≃ₐ[A] B') (T : Over (Spec A))
    (x : T ⟶ (commGroupScheme A B).X) :
    commPointsEquiv A B' T (x ≫ (CommGroupScheme.groupHom (commCongrIso e).hom).hom.hom) =
      tensorUnitsEquiv e _ (commPointsEquiv A B T x) :=
  congrIso_hom_points e T x

end Congr

section BaseChange

variable (A' : CommRingCat.{u}) [Algebra A A']

/-- The published base-change comparison, in the commutative category. -/
def commAlgebraBaseChangeIso :
    (CommGroupScheme.baseChange (baseMap A A')).obj (commGroupScheme A B) ≅
      commGroupScheme A' (A' ⊗[A] B) where
  hom := Additive.ofMul (algebraBaseChangeIso A A' B).hom
  inv := Additive.ofMul (algebraBaseChangeIso A A' B).inv
  hom_inv_id := congrArg Additive.ofMul (algebraBaseChangeIso A A' B).hom_inv_id
  inv_hom_id := congrArg Additive.ofMul (algebraBaseChangeIso A A' B).inv_hom_id

theorem commAlgebraBaseChangeIso_hom_points (T : Over (Spec A'))
    (x : T ⟶ ((CommGroupScheme.baseChange (baseMap A A')).obj
      (commGroupScheme A B)).X) :
    commPointsEquiv A' (A' ⊗[A] B) T
        (x ≫ (CommGroupScheme.groupHom (commAlgebraBaseChangeIso A B A').hom).hom.hom) =
      basePointsEquiv A A' B T x :=
  algebraBaseChangeIso_hom_points A A' B T x

end BaseChange

section Split

variable (I : Type u) [Finite I]

/-- The published splitting for a finite product algebra, in the commutative category. -/
def commSplitIso :
    commGroupScheme A (I → A) ≅ splitTorus.commGroupScheme (Spec A) I where
  hom := Additive.ofMul (splitIso A I).hom
  inv := Additive.ofMul (splitIso A I).inv
  hom_inv_id := congrArg Additive.ofMul (splitIso A I).hom_inv_id
  inv_hom_id := congrArg Additive.ofMul (splitIso A I).inv_hom_id

theorem commSplitIso_hom_points (T : Over (Spec A))
    (x : T ⟶ (commGroupScheme A (I → A)).X) :
    splitTorus.pointsEquiv I T
        (x ≫ (CommGroupScheme.groupHom (commSplitIso A I).hom).hom.hom) =
      splitPointsEquiv A I T x :=
  splitIso_hom_points A I T x

end Split

end Langlands.GroupScheme.WeilGm
