/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.RestrictedAffineSingleMaps

/-! # Explicit maps for restricted degree-zero complexes

Source: Stacks Project, Tags 09Z1 and 0EZM.
-/

@[expose] public section

universe v
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale

private theorem mapped_iso_inv_leg {A B C : Type*}
    [Category A] [Category B] [Category C] (P : A ⥤ B) (J : B ⥤ C)
    {X Y X' : A} {Z W : B} {V : C}
    (e : X ≅ Y) (b : Z ≅ P.obj Y) (a : Z ≅ W) (s : V ≅ J.obj W)
    (f : X ⟶ X') :
    (J.mapIso (P.mapIso e ≪≫ b.symm ≪≫ a) ≪≫ s.symm).inv ≫ J.map (P.map f) =
      s.hom ≫ J.map (a.inv ≫ b.hom ≫ P.map (e.inv ≫ f)) := by
  simp only [Iso.trans_inv, Iso.symm_inv, Functor.mapIso_inv,
    Functor.map_comp, Category.assoc]

/-- The explicit cone comparison carries the restricted colimit leg to the
canonical restricted coefficient map.
Source: Stacks Project, Tags 09Z1 and 0EZM.
(blueprint: lem-sbc-restricted-affine-single-cone-leg).

Proof: Expand the inverse of the explicit cone isomorphism and the mapped cocone leg.
The inverse factors are the single comparison, the inverse composition comparison for
q and r_i, the composition comparison for r and c_i, and the restricted eH inverse.
Combine the latter with the restricted colimit injection by functoriality.
These are exactly the defining factors of rawAffineRestrictedCoefficient. -/
theorem restrictedAffineSingleConeIso_inv_leg {S : Scheme.{v}}
    {I : Type v} [Preorder I]
    (D : Iᵒᵖ ⥤ Over S)
    (c : Cone D)
    (F : ∀ i : I, Sheaf (D.obj (op i)).left.smallEtaleTopology AddCommGrpCat.{v + 1})
    (H : I ⥤ Sheaf c.pt.left.smallEtaleTopology AddCommGrpCat.{v + 1})
    (eH : ∀ i : I, H.obj i ≅
      (((c.π.app (op i)).left)^*[AddCommGrpCat.{v + 1}]).obj (F i))
    [HasColimit H] (U : S.Etale) (i : Iᵒᵖ) :
      (restrictedAffineSingleConeIso D c F H eH U i).inv ≫
        (restrictedAffineL D c H U).ι.app (op i) =
        ((upperStar AddCommGrpCat.{v + 1}
          ((restrictedAffineCone D c U).π.app i)).mapCochainComplexSingleFunctor 0).hom.app
            ((upperStar AddCommGrpCat.{v + 1} (pullback.snd U.hom (D.obj i).hom)).obj
              (F i.unop)) ≫
        (CochainComplex.singleFunctor _ 0).map
          (rawAffineRestrictedCoefficient (c.π.app i).left (D.obj i).hom c.pt.hom
            (Over.w (c.π.app i)) (F i.unop) (colimit H)
            ((eH i.unop).inv ≫ colimit.ι H i.unop) U) := by
  let q := (restrictedAffineCone D c U).π.app i
  let r := pullback.snd U.hom (D.obj i).hom
  let r' := pullback.snd U.hom c.pt.hom
  have hw : q ≫ r = r' ≫ (c.π.app i).left := by
    simp [q, r, r', restrictedAffineCone, rawAffineRestrictedMap]
  let P := upperStar AddCommGrpCat.{v + 1} r'
  let J := CochainComplex.singleFunctor
    (Sheaf (pullback U.hom c.pt.hom).smallEtaleTopology AddCommGrpCat.{v + 1}) 0
  let a := (upperStarComp AddCommGrpCat.{v + 1} q r).app (F i.unop)
  let b := (upperStarComp AddCommGrpCat.{v + 1} r' (c.π.app i).left
    (q ≫ r) hw).app (F i.unop)
  let s := ((upperStar AddCommGrpCat.{v + 1} q).mapCochainComplexSingleFunctor 0).app
    ((upperStar AddCommGrpCat.{v + 1} r).obj (F i.unop))
  exact mapped_iso_inv_leg P J (eH i.unop) b a s (colimit.ι H i.unop)

end AlgebraicGeometry.Etale
