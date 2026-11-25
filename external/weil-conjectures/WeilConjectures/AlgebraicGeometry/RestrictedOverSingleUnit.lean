/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.RestrictedOverSingleData

/-! # Unit law for restricted fixed-coefficient single complexes

Source: Stacks Project, Tags 09Z1 and 0EZM, restriction of fixed coefficients.
(blueprint: lem-sbc-restricted-over-single-unit).
-/

@[expose] public section

universe u
open CategoryTheory Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale

attribute [local irreducible] upperStar upperStarComp upperStarId

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

private theorem coefficient_identity {X Y : Scheme.{u}} (r : X ⟶ Y)
    (t : X ⟶ Y) (ht : t = r) (h : t = 𝟙 X ≫ r) (h' : t = r ≫ 𝟙 Y)
    (G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    (upperStarComp AddCommGrpCat.{u + 1} (𝟙 X) r t h).inv.app G ≫
      (upperStarComp AddCommGrpCat.{u + 1} r (𝟙 Y) t h').hom.app G ≫
        (upperStar AddCommGrpCat.{u + 1} r).map
          ((upperStarId AddCommGrpCat.{u + 1} Y).hom.app G) =
      (upperStarId AddCommGrpCat.{u + 1} X).hom.app
        ((upperStar AddCommGrpCat.{u + 1} r).obj G) := by
  subst t
  rw [upperStarComp_id_left, upperStarComp_id_right]
  simp only [Iso.trans_inv, Iso.trans_hom, Iso.symm_inv, Iso.symm_hom,
    Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_hom, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.rightUnitor_hom_app,
    Functor.leftUnitor_inv_app, Functor.id_obj, Functor.comp_obj,
    Category.id_comp, ← CategoryTheory.Functor.map_comp, Iso.inv_hom_id_app,
    Category.comp_id]
  erw [CategoryTheory.Functor.map_id]
  exact Category.comp_id _

private theorem square_unit_heq {X Y : Scheme.{u}} (r : X ⟶ Y)
    (a : Y ⟶ Y) (q : X ⟶ X) (ha : a = 𝟙 Y) (hq : q = 𝟙 X)
    (h : q ≫ r = r ≫ a) (G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})
    (φ : (upperStar AddCommGrpCat.{u + 1} a).obj G ⟶ G)
    (hφ : HEq φ ((upperStarId AddCommGrpCat.{u + 1} Y).hom.app G)) :
    HEq ((upperStarComp AddCommGrpCat.{u + 1} q r).inv.app G ≫
      (upperStarComp AddCommGrpCat.{u + 1} r a (q ≫ r) h).hom.app G ≫
        (upperStar AddCommGrpCat.{u + 1} r).map φ)
      ((upperStarId AddCommGrpCat.{u + 1} X).hom.app
        ((upperStar AddCommGrpCat.{u + 1} r).obj G)) := by
  cases ha
  cases hq
  rw [eq_of_heq hφ]
  exact heq_of_eq (coefficient_identity r (𝟙 X ≫ r) (Category.id_comp r) rfl h G)

private theorem single_coefficient_unit_heq {X : Scheme.{u}} (q : X ⟶ X)
    (hq : q = 𝟙 X) (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (γ : (upperStar AddCommGrpCat.{u + 1} q).obj G ⟶ G)
    (hγ : HEq γ ((upperStarId AddCommGrpCat.{u + 1} X).hom.app G)) :
    HEq (((upperStar AddCommGrpCat.{u + 1} q).mapCochainComplexSingleFunctor 0).hom.app G ≫
      (CochainComplex.singleFunctor _ 0).map γ)
      ((NatIso.mapHomologicalComplex (upperStarId AddCommGrpCat.{u + 1} X)
        (ComplexShape.up ℤ)).hom.app ((CochainComplex.singleFunctor _ 0).obj G)) := by
  cases hq
  rw [eq_of_heq hγ]
  exact heq_of_eq (single_unit _ (upperStarId AddCommGrpCat.{u + 1} X) G)

private theorem unit_inv_heq {X Y : Scheme.{u}} (a : X ⟶ X) (ha : a = 𝟙 X)
    (r : X ⟶ Y) (h : r = a ≫ r)
    (G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    HEq ((upperStarComp AddCommGrpCat.{u + 1} a r r h).inv.app G)
      ((upperStarId AddCommGrpCat.{u + 1} X).hom.app
        ((upperStar AddCommGrpCat.{u + 1} r).obj G)) := by
  cases ha
  rw [upperStarComp_id_left]
  apply heq_of_eq
  simp only [Iso.trans_inv, Iso.symm_inv, Functor.isoWhiskerLeft_inv,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.rightUnitor_hom_app]
  exact Category.comp_id _

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

private theorem dependent_hom_heq {C : Type*} [Category C] {A : C}
    {β : (A ⟶ A) → Type*} (g : ∀ a, β a) (a : A ⟶ A) (h : a = 𝟙 A) :
    HEq (g a) (g (𝟙 A)) := by
  cases h
  rfl

private theorem restricted_identity_heq {W S : Scheme.{u}} (k : W ⟶ S)
    (F : Sheaf W.smallEtaleTopology AddCommGrpCat.{u + 1}) (A : Over W) (U : S.Etale) :
    HEq (restrictedOverSingleIso k F (𝟙 A) U).hom
      ((NatIso.mapHomologicalComplex
        (upperStarId AddCommGrpCat.{u + 1} (pullback U.hom (A.hom ≫ k)))
        (ComplexShape.up ℤ)).hom.app (restrictedOverSingle k F A U)) := by
  simp only [restrictedOverSingleIso, asIso_hom]
  let w : (Over.Hom.left (𝟙 A)) ≫ (A.hom ≫ k) = A.hom ≫ k := by simp
  let q := rawAffineRestrictedMap (Over.Hom.left (𝟙 A)) (A.hom ≫ k) (A.hom ≫ k) w U
  let r := pullback.snd U.hom (A.hom ≫ k)
  let R := (upperStar AddCommGrpCat.{u + 1} A.hom).obj F
  have hq : q = 𝟙 _ := by
    apply pullback.hom_ext <;> simp [q, rawAffineRestrictedMap, pullback.map]
  have hw : q ≫ r = r ≫ (Over.Hom.left (𝟙 A)) := by
    simp only [q, r, rawAffineRestrictedMap, pullback.map, pullback.lift_snd]
  let φ := (upperStarComp AddCommGrpCat.{u + 1} (Over.Hom.left (𝟙 A)) A.hom A.hom
    (Over.w (𝟙 A)).symm).inv.app F
  have hφ : HEq φ ((upperStarId AddCommGrpCat.{u + 1} A.left).hom.app R) :=
    unit_inv_heq (Over.Hom.left (𝟙 A)) rfl A.hom _ F
  have hγ := square_unit_heq r (Over.Hom.left (𝟙 A)) q rfl hq hw R φ hφ
  have hs := single_coefficient_unit_heq q hq
    ((upperStar AddCommGrpCat.{u + 1} r).obj R) _ hγ
  exact hs

/-- Unit law for a fixed-coefficient restricted single complex at one diagram object.
Source: Stacks Project, Tags 09Z1 and 0EZM, canonical fixed-coefficient comparisons.
(blueprint: lem-sbc-restricted-over-single-unit).

Proof: Substitute D₀.map_id. The induced pullback map is identity by its two projection
identities. Expand restrictedOverSingleIso.hom and rawAffineRestrictedCoefficient.
The two inverse-image composition unit laws reduce the three sheaf comparisons to
upperStarId. The natural comparison of singleFunctor with inverse image respects
this unit: in degree zero it is the identity comparison; every other degree is zero.
Consequently its hom is the displayed mapHomologicalComplex unit, transported along
the restricted diagram map_id equality. Proof irrelevance makes the choice of equality proof
immaterial. This argument also applies to the zero sheaf, the empty scheme and identity
structure maps. -/
theorem restrictedOverSingle_unit {W S : Scheme.{u}} (k : W ⟶ S)
    (F : Sheaf W.smallEtaleTopology AddCommGrpCat.{u + 1})
    {I : Type u} [Category.{u} I] (D₀ : I ⥤ Over W) (U : S.Etale) (i : I) :
    (restrictedOverSingleIso k F (D₀.map (𝟙 i)) U).hom =
      (NatIso.mapHomologicalComplex
        (eqToIso (congrArg (upperStar AddCommGrpCat.{u + 1})
          ((restrictedOverDiagram k D₀ U).map_id i)))
        (ComplexShape.up ℤ)).hom.app (restrictedOverSingle k F (D₀.obj i) U) ≫
      (NatIso.mapHomologicalComplex
        (upperStarId AddCommGrpCat.{u + 1} ((restrictedOverDiagram k D₀ U).obj i))
        (ComplexShape.up ℤ)).hom.app (restrictedOverSingle k F (D₀.obj i) U) := by
  have hs := dependent_hom_heq
    (fun f : D₀.obj i ⟶ D₀.obj i ↦ (restrictedOverSingleIso k F f U).hom)
    (D₀.map (𝟙 i)) (D₀.map_id i)
  have hi := restricted_identity_heq k F (D₀.obj i) U
  have ht := complex_transport_heq
    (congrArg (upperStar AddCommGrpCat.{u + 1}) ((restrictedOverDiagram k D₀ U).map_id i))
    (restrictedOverSingle k F (D₀.obj i) U)
    ((NatIso.mapHomologicalComplex (upperStarId AddCommGrpCat.{u + 1}
      ((restrictedOverDiagram k D₀ U).obj i)) (ComplexShape.up ℤ)).hom.app
        (restrictedOverSingle k F (D₀.obj i) U))
  exact eq_of_heq (hs.trans (hi.trans ht.symm))

end AlgebraicGeometry.Etale
