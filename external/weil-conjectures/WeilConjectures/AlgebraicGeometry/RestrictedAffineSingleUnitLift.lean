/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.RestrictedAffineSingleMaps

/-! # Lifting restricted coefficient units to single complexes

Source: Stacks Project, Tags 09Z1, 0EZM and 03CB;
Mathlib.Algebra.Homology.Additive and Mathlib.Algebra.Homology.Single.
-/

@[expose] public section

universe v
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale

attribute [local irreducible] upperStar upperStarId

private theorem single_unit {C : Type*} [Category C] [HasZeroMorphisms C]
    [HasZeroObject C] (E : C ⥤ C) [E.PreservesZeroMorphisms] (e : E ≅ 𝟭 C)
    (G : C) :
    (HomologicalComplex.singleMapHomologicalComplex E (ComplexShape.up ℤ) 0).hom.app G ≫
        (HomologicalComplex.single C (ComplexShape.up ℤ) 0).map (e.hom.app G) =
      (NatIso.mapHomologicalComplex e (ComplexShape.up ℤ)).hom.app
        ((HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj G) := by
  apply HomologicalComplex.to_single_hom_ext (j := (0 : ℤ))
  simp only [HomologicalComplex.comp_f,
    HomologicalComplex.singleMapHomologicalComplex_hom_app_self,
    HomologicalComplex.single_map_f_self, Category.assoc,
    Iso.inv_hom_id_assoc, NatIso.mapHomologicalComplex_hom_app_f]
  rw [← cancel_mono (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 G).hom]
  simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id, Functor.id_map, Functor.id_obj]
    using e.hom.naturality
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 G).hom

private theorem single_coefficient_unit_heq {X : Scheme.{v}} (q : X ⟶ X)
    (hq : q = 𝟙 X) (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{v + 1})
    (γ : (upperStar AddCommGrpCat.{v + 1} q).obj G ⟶ G)
    (hγ : HEq γ ((upperStarId AddCommGrpCat.{v + 1} X).hom.app G)) :
    HEq (((upperStar AddCommGrpCat.{v + 1} q).mapCochainComplexSingleFunctor 0).hom.app G ≫
      (CochainComplex.singleFunctor _ 0).map γ)
      ((NatIso.mapHomologicalComplex (upperStarId AddCommGrpCat.{v + 1} X)
        (ComplexShape.up ℤ)).hom.app ((CochainComplex.singleFunctor _ 0).obj G)) := by
  cases hq
  rw [eq_of_heq hγ]
  exact heq_of_eq (single_unit _ (upperStarId AddCommGrpCat.{v + 1} X) G)

private theorem complex_transport_heq {C : Type*} [Category C] [HasZeroMorphisms C]
    {L M : C ⥤ C} [L.PreservesZeroMorphisms] [M.PreservesZeroMorphisms]
    (e : L = M) (G : CochainComplex C ℤ) {Z : CochainComplex C ℤ}
    (f : (M.mapHomologicalComplex (ComplexShape.up ℤ)).obj G ⟶ Z) :
    HEq ((NatIso.mapHomologicalComplex (eqToIso e) (ComplexShape.up ℤ)).hom.app G ≫ f)
      f := by
  cases e
  apply heq_of_eq
  change (𝟙 _) ≫ f = f
  exact Category.id_comp f

/-- The restricted transition is the transported complex unit,
provided its restricted sheaf coefficient is already the sheaf unit.
Source: Stacks Project, Tags 09Z1, 0EZM and 03CB;
Mathlib.Algebra.Homology.Additive, `singleMapHomologicalComplex_hom_app_self`, and
Mathlib.Algebra.Homology.Single, `single_map_f_self`.
(blueprint: lem-sbc-restricted-affine-single-unit-lift).

Proof: Write X for the fibre product, r for its second projection, R = r^* F_i,
q for the restricted diagram's identity transition, and gamma for the raw restricted
coefficient. The diagram's map_id proves q = id_X. Substitute this equality in the
heterogeneous coefficient hypothesis to obtain the ordinary unit equation; transporting
back gives gamma = (eqToIso (congrArg upperStar map_id)).hom.app R followed by
upperStarId.hom.app R. This step uses only equality elimination and identity composition.
Evaluate the single comparison at zero with singleMapHomologicalComplex_hom_app_self,
and the image of gamma with single_map_f_self. The evaluation isomorphisms around the
intermediate object q^* R cancel. The remaining expression is q^* of the evaluation
isomorphism for R, followed by gamma and its inverse evaluation isomorphism. Naturality
of the transported unit with respect to that evaluation isomorphism identifies this
with its component on the zero object of the single complex. The component formula for
NatIso.mapHomologicalComplex identifies this last expression with the displayed right
side. Apply HomologicalComplex.hom_ext. The calculation above proves its zero component;
in every other degree the target is zero by isZero_single_obj_X, so its morphisms agree.
This assumes the restricted coefficient unit and does not prove its restriction identity.
Zero sheaves and empty schemes require no exceptions; an empty I supplies no index i. -/
theorem restrictedAffineSingleUnit_lift {S : Scheme.{v}}
    {I : Type v} [Preorder I]
    (D : Iᵒᵖ ⥤ Over S)
    (F : ∀ i : I, Sheaf (D.obj (op i)).left.smallEtaleTopology AddCommGrpCat.{v + 1})
    (φ : ∀ {i j : I} (f : i ⟶ j),
      (((D.map f.op).left)^*[AddCommGrpCat.{v + 1}]).obj (F i) ⟶ F j)
    (U : S.Etale) (i : Iᵒᵖ)
    (hunit : HEq
      (rawAffineRestrictedCoefficient (D.map (𝟙 i)).left (D.obj i).hom (D.obj i).hom
        (Over.w (D.map (𝟙 i))) (F i.unop) (F i.unop) (φ (𝟙 i).unop) U)
      ((upperStarId AddCommGrpCat.{v + 1} (pullback U.hom (D.obj i).hom)).hom.app
        ((upperStar AddCommGrpCat.{v + 1} (pullback.snd U.hom (D.obj i).hom)).obj
          (F i.unop)))) :
    restrictedAffineSingleTransition D F φ U (𝟙 i) =
      (NatIso.mapHomologicalComplex
        (eqToIso (congrArg (upperStar AddCommGrpCat.{v + 1})
          ((restrictedAffineDiagram D U).map_id i)))
        (ComplexShape.up ℤ)).hom.app (restrictedAffineK D F U i) ≫
      (NatIso.mapHomologicalComplex
        (upperStarId AddCommGrpCat.{v + 1} ((restrictedAffineDiagram D U).obj i))
        (ComplexShape.up ℤ)).hom.app (restrictedAffineK D F U i) := by
  let q := (restrictedAffineDiagram D U).map (𝟙 i)
  let R := (upperStar AddCommGrpCat.{v + 1} (pullback.snd U.hom (D.obj i).hom)).obj
    (F i.unop)
  have hs := single_coefficient_unit_heq q ((restrictedAffineDiagram D U).map_id i)
    R _ hunit
  have ht := complex_transport_heq
    (congrArg (upperStar AddCommGrpCat.{v + 1}) ((restrictedAffineDiagram D U).map_id i))
    (restrictedAffineK D F U i)
    ((NatIso.mapHomologicalComplex
      (upperStarId AddCommGrpCat.{v + 1} ((restrictedAffineDiagram D U).obj i))
      (ComplexShape.up ℤ)).hom.app (restrictedAffineK D F U i))
  exact eq_of_heq (hs.trans ht.symm)

end AlgebraicGeometry.Etale
