import Langlands.GroupScheme.Torus.AffineDiagonalizableTranslation
import Langlands.GroupScheme.CorepresentedAffineComparison
import Langlands.GroupScheme.Torus.KernelDiagonalizable

/-! # Global units and the affine translation grading -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false

namespace AffineCoordinates

variable {R : CommRingCat.{u}} (H : GroupScheme (Spec R)) [IsAffine H.X.left]

/-- Transport global units to the chosen affine coordinate algebra. -/
def coordinateUnit : Γ(H.X.left, ⊤)ˣ →* (algebra H)ˣ :=
  (Units.map (Scheme.ΓSpecIso (CommRingCat.of (algebra H))).hom.hom.toMonoidHom).comp
    (Units.map (coordinateSchemeIso H).hom.left.appTop.hom.toMonoidHom)

/-- Affine coordinate evaluation agrees with pullback along the actual scheme point. -/
theorem coordinateUnit_apply {C : CommAlgCat.{u} R} (x : algebra H ⟶ C)
    (r : Γ(H.X.left, ⊤)ˣ) :
    (Scheme.ΓSpecIso (CommRingCat.of C)).hom ((pointEquiv H C x).left.appTop r) =
      x.hom (coordinateUnit H r) := by
  let e : Spec (CommRingCat.of (algebra H)) ⟶ H.X.left := (coordinateSchemeIso H).hom.left
  let φ := CommRingCat.ofHom x.hom.toRingHom
  have he : (Spec.map φ ≫ e).appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of C)).hom =
      (e.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (algebra H))).hom) ≫ φ := by
    rw [Scheme.Hom.comp_appTop, Category.assoc, Scheme.ΓSpecIso_naturality, ← Category.assoc]
  exact ConcreteCategory.congr_hom he r.val

end AffineCoordinates

namespace CharacterAction

open Langlands.CommutativeAlgebra.StronglyGraded

variable {R : CommRingCat.{u}} {H : GroupScheme (Spec R)} [IsAffine H.X.left]
variable {M : Type u} [AddCommGroup M]

/-- A global unit that transforms by evaluation at `m` under left translation has
degree `m` in the induced affine translation grading. -/
theorem coordinateUnit_mem_component
    (i : (Diagonalizable.groupScheme R M).toGrp ⟶ H) (m : M)
    (r : Γ(H.X.left, ⊤)ˣ)
    (hr : ∀ (T : Over (Spec R)) (n : T ⟶ (Diagonalizable.groupScheme R M).X)
      (a : T ⟶ H.X),
      Units.map ((n ≫ i.hom.hom) * a).left.appTop.hom.toMonoidHom r =
        Diagonalizable.characterPointsEquiv R M T n (.ofAdd m) *
          Units.map a.left.appTop.hom.toMonoidHom r) :
    (AffineCoordinates.coordinateUnit H r).val ∈
      component (c := (coaction (ofTranslation i)).hom.toRingHom) m := by
  rw [mem_component]
  let B := AffineCoordinates.algebra H
  let C := CharacterAction.algebra (M := M) B
  let T := (algSpec R).obj (op C)
  let t := universal (M := M) B
  let a : T ⟶ H.X := AffineCoordinates.pointEquiv H C (constant B)
  let b : T ⟶ H.X := (characterPoint t ≫ i.hom.hom) * a
  let v := AffineCoordinates.coordinateUnit H r
  have hsingle : (Scheme.ΓSpecIso (CommRingCat.of C)).hom
      (Diagonalizable.characterPointsEquiv R M T (characterPoint t) (.ofAdd m)).val =
        (AddMonoidAlgebra.single m 1 : C) := by
    have h := Corepresented.pointsEquiv_eq_affinePointsEquiv
      (Diagonalizable.functor R M) (Diagonalizable.grpCorepresentation R M) C
      (characterPoint t)
    change Diagonalizable.characterPointsEquiv R M T (characterPoint t) =
      (Diagonalizable.functor R M).map (Corepresented.affineSectionsIso C).inv
        (Corepresented.affinePointsEquiv (Diagonalizable.functor R M)
          (Diagonalizable.grpCorepresentation R M) C (characterPoint t)) at h
    rw [h, MulEquiv.apply_symm_apply]
    change (Scheme.ΓSpecIso (CommRingCat.of C)).hom
      ((Corepresented.affineSectionsIso C).inv.hom.toRingHom (t (.ofAdd m)).val) = _
    rw [Corepresented.affineSectionsIso_inv_ringHom]
    exact ConcreteCategory.congr_hom (Scheme.ΓSpecIso (CommRingCat.of C)).inv_hom_id
      (t (.ofAdd m)).val
  have hb : AffineCoordinates.pointEquiv H C (coaction (ofTranslation i)) = b := by
    rw [coaction, pointEquiv_ofTranslation_act]
  have hu₁ : (Scheme.ΓSpecIso (CommRingCat.of C)).hom (b.left.appTop r.val) =
      (coaction (ofTranslation i)).hom v.val :=
    hb ▸ AffineCoordinates.coordinateUnit_apply H (coaction (ofTranslation i)) r
  have hu₂ : (Scheme.ΓSpecIso (CommRingCat.of C)).hom (a.left.appTop r.val) =
      (constant B).hom v.val := AffineCoordinates.coordinateUnit_apply H (constant B) r
  have h := congrArg (fun z : Γ(T.left, ⊤)ˣ => (Scheme.ΓSpecIso (CommRingCat.of C)).hom z.val)
    (hr T (characterPoint t) a)
  change (Scheme.ΓSpecIso (CommRingCat.of C)).hom (b.left.appTop r.val) =
    (Scheme.ΓSpecIso (CommRingCat.of C)).hom
      ((Diagonalizable.characterPointsEquiv R M T (characterPoint t) (.ofAdd m)).val *
        a.left.appTop r.val) at h
  rw [map_mul, hsingle, hu₁, hu₂, constant_apply, AddMonoidAlgebra.single_mul_single,
    add_zero, one_mul] at h
  exact h

end CharacterAction

end Langlands.GroupScheme
