/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.RestrictedAffineCoefficientConstruction

/-! # Explicit maps for restricted degree-zero complexes

Source: Stacks Project, Tags 09Z1 and 0EZM.
-/

@[expose] public section

universe v
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale

/-- Restrict the given coefficient transition and apply the degree-zero single functor.
Source: Stacks Project, Tag 09Z1, restriction to an affine etale object.
(blueprint: def-sbc-restricted-affine-single-maps). -/
@[implicit_reducible]
noncomputable def restrictedAffineSingleTransition {S : Scheme.{v}} {I : Type v}
    [Preorder I] (D : Iᵒᵖ ⥤ Over S)
    (F : ∀ i : I, Sheaf (D.obj (op i)).left.smallEtaleTopology AddCommGrpCat.{v + 1})
    (φ : ∀ {i j : I} (f : i ⟶ j),
      (((D.map f.op).left)^*[AddCommGrpCat.{v + 1}]).obj (F i) ⟶ F j)
    (U : S.Etale) {i j : Iᵒᵖ} (f : j ⟶ i) :
    ((upperStar AddCommGrpCat.{v + 1}
        ((restrictedAffineDiagram D U).map f)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (restrictedAffineK D F U i) ⟶
        restrictedAffineK D F U j :=
  ((upperStar AddCommGrpCat.{v + 1}
        ((restrictedAffineDiagram D U).map f)).mapCochainComplexSingleFunctor 0).hom.app
      ((upperStar AddCommGrpCat.{v + 1} (pullback.snd U.hom (D.obj i).hom)).obj
        (F i.unop)) ≫
    (CochainComplex.singleFunctor _ 0).map
      (rawAffineRestrictedCoefficient (D.map f).left (D.obj i).hom (D.obj j).hom
        (Over.w (D.map f)) (F i.unop) (F j.unop) (φ f.unop) U)

/-- The cone comparison, built from the given `eH`, two inverse-image composition
isomorphisms, and the single-complex comparison. No witness is chosen.
Source: Stacks Project, Tags 09Z1 and 0EZM, restriction of a cone coefficient system.
(blueprint: def-sbc-restricted-affine-single-maps). -/
noncomputable def restrictedAffineSingleConeIso {S : Scheme.{v}} {I : Type v}
    [Preorder I] (D : Iᵒᵖ ⥤ Over S) (c : Cone D)
    (F : ∀ i : I, Sheaf (D.obj (op i)).left.smallEtaleTopology AddCommGrpCat.{v + 1})
    (H : I ⥤ Sheaf c.pt.left.smallEtaleTopology AddCommGrpCat.{v + 1})
    (eH : ∀ i : I, H.obj i ≅
      (((c.π.app (op i)).left)^*[AddCommGrpCat.{v + 1}]).obj (F i))
    (U : S.Etale) (i : Iᵒᵖ) :
    (restrictedAffineG D c H U).obj (op i) ≅
      ((upperStar AddCommGrpCat.{v + 1}
        ((restrictedAffineCone D c U).π.app i)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj (restrictedAffineK D F U i) := by
  let q := (restrictedAffineCone D c U).π.app i
  let r := pullback.snd U.hom (D.obj i).hom
  let r' := pullback.snd U.hom c.pt.hom
  have hw : q ≫ r = r' ≫ (c.π.app i).left := by
    simp [q, r, r', restrictedAffineCone, rawAffineRestrictedMap]
  exact (CochainComplex.singleFunctor _ 0).mapIso
    ((upperStar AddCommGrpCat.{v + 1} r').mapIso (eH i.unop) ≪≫
      ((upperStarComp AddCommGrpCat.{v + 1} r' (c.π.app i).left (q ≫ r) hw).app
        (F i.unop)).symm ≪≫
      (upperStarComp AddCommGrpCat.{v + 1} q r).app (F i.unop)) ≪≫
    (((upperStar AddCommGrpCat.{v + 1} q).mapCochainComplexSingleFunctor 0).app
      ((upperStar AddCommGrpCat.{v + 1} r).obj (F i.unop))).symm

end AlgebraicGeometry.Etale
