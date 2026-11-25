/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.Etale.Derived.GlobalSections
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
import WeilConjectures.AlgebraicGeometry.DerivedUnitLerayId
import WeilConjectures.AlgebraicGeometry.DerivedUnitLerayComp

/-! # Identity and composition of pullback on derived étale cohomology

Source: Stacks Project, Tags 015J, 015K and 0EZM.
(blueprint: lem-weil-pbc-derived-cohomology-pullback-laws).
-/

@[expose] public section

universe uNatural

open CategoryTheory CategoryTheory.Limits

set_option backward.isDefEq.respectTransparency false in
private lemma idFactors {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    (K : CochainComplex C ℤ) :
    (Functor.mapDerivedCategoryIdIso C).hom.app (DerivedCategory.Q.obj K) =
    (𝟭 C).mapDerivedCategoryFactors.hom.app K ≫
      DerivedCategory.Q.map ((Functor.mapHomologicalComplexIdIso C
        (ComplexShape.up ℤ)).hom.app K) := by
  have h := congr_app (congrArg Iso.hom (Functor.mapDerivedCategoryIdIso_factorsh C))
    ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj K)
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.rightUnitor_hom_app, Functor.leftUnitor_hom_app] at h
  dsimp only [Functor.id_obj, Functor.comp_obj] at h
  simp only [Category.comp_id] at h
  apply (cancel_mono ((DerivedCategory.quotientCompQhIso C).inv.app K)).1
  change (Functor.mapDerivedCategoryIdIso C).hom.app _ ≫
    (𝟭 (DerivedCategory C)).map ((DerivedCategory.quotientCompQhIso C).inv.app K) = _
  rw [← (Functor.mapDerivedCategoryIdIso C).hom.naturality]
  dsimp only [Functor.comp_obj]
  rw [h]
  rw [Functor.mapDerivedCategoryFactorsh_hom_app]
  rw [Functor.mapHomotopyCategoryIdIso_hom_app]
  simp only [Functor.mapHomotopyCategoryFactors, Quotient.lift.isLift_inv]
  dsimp only [Functor.comp_obj, Functor.id_obj]
  simp only [Category.assoc]
  rw [← Functor.map_comp_assoc, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id, Category.id_comp]
  simp only [CategoryTheory.Functor.map_id, Category.id_comp]
  rw [← DerivedCategory.quotientCompQhIso_inv_naturality]


private lemma compFactors {C D E : Type*}
    [Category C] [Abelian C] [HasDerivedCategory C]
    [Category D] [Abelian D] [HasDerivedCategory D]
    [Category E] [Abelian E] [HasDerivedCategory E]
    (F : C ⥤ D) (G : D ⥤ E) (H : C ⥤ E)
    [F.Additive] [G.Additive] [H.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (e : H ≅ F ⋙ G) (K : CochainComplex C ℤ) :
    (Functor.mapDerivedCategoryNatIso e ≪≫
      (Functor.mapDerivedCategoryCompIso F G).symm).hom.app (DerivedCategory.Q.obj K) ≫
      G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app K) ≫
      G.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj K) =
    H.mapDerivedCategoryFactors.hom.app K ≫
      DerivedCategory.Q.map ((Functor.mapHomologicalComplexCompIso e.symm
        (.up ℤ)).inv.app K) := by
  have hc := Functor.mapDerivedCategoryCompIso_fac F G K
  have hn := Functor.mapDerivedCategoryNatIso_fac e K
  have hid : DerivedCategory.Q.map
      ((Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ G)) (.up ℤ)).hom.app K) =
      𝟙 _ := by
    change DerivedCategory.Q.map (𝟙 _) = 𝟙 _
    exact CategoryTheory.Functor.map_id _ _
  rw [hid] at hc
  dsimp only [Functor.comp_obj] at hc
  simp only [Category.comp_id] at hc
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Category.assoc]
  rw [hc, hn]
  rfl

namespace AlgebraicGeometry.Etale

private lemma unitLeray_naturality {X Y : Scheme.{uNatural}} (f : Y ⟶ X)
    {K L : DerivedCategory (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1})}
    (a : K ⟶ L) :
    (rightDerivedGlobalSections AddCommGrpCat.{uNatural + 1} X).map a ≫
      ((rightDerivedGlobalSections AddCommGrpCat.{uNatural + 1} X).map
        ((mapDerivedUpperStarLowerStarAdjunction AddCommGrpCat.{uNatural + 1} f).unit.app L) ≫
      (rightDerivedLowerStarCompRightDerivedGlobalSectionsIso
        AddCommGrpCat.{uNatural + 1} f).hom.app
          ((upperStar AddCommGrpCat.{uNatural + 1} f).mapDerivedCategory.obj L)) =
    ((rightDerivedGlobalSections AddCommGrpCat.{uNatural + 1} X).map
        ((mapDerivedUpperStarLowerStarAdjunction AddCommGrpCat.{uNatural + 1} f).unit.app K) ≫
      (rightDerivedLowerStarCompRightDerivedGlobalSectionsIso
        AddCommGrpCat.{uNatural + 1} f).hom.app
          ((upperStar AddCommGrpCat.{uNatural + 1} f).mapDerivedCategory.obj K)) ≫
      (rightDerivedGlobalSections AddCommGrpCat.{uNatural + 1} Y).map
        ((upperStar AddCommGrpCat.{uNatural + 1} f).mapDerivedCategory.map a) := by
  let τ := Functor.whiskerRight
    (mapDerivedUpperStarLowerStarAdjunction AddCommGrpCat.{uNatural + 1} f).unit
    (rightDerivedGlobalSections AddCommGrpCat.{uNatural + 1} X) ≫
    Functor.whiskerLeft (upperStar AddCommGrpCat.{uNatural + 1} f).mapDerivedCategory
      (rightDerivedLowerStarCompRightDerivedGlobalSectionsIso
        AddCommGrpCat.{uNatural + 1} f).hom
  exact τ.naturality a

-- Elaborating the dependent presentation families and compatibility equations.
/-- Identity and composition of pullback on derived étale cohomology.
Source: Stacks Project, Tags 015J, 015K and 0EZM.
(blueprint: lem-weil-pbc-derived-cohomology-pullback-laws).

Proof: Rewrite every P using hP. For the identity scheme map, the inverse-image
identity isomorphism identifies the adjunction unit with the identity after
the direct-image identity isomorphism. The Leray comparison for that direct
image is the same identity comparison. The complex identity map in the
statement is the inverse-image identity comparison, so all comparisons cancel.
For composable maps, naturality moves the second unit past the first lifted
complex morphism. The composite-unit equation for inverse images identifies
the two units with the unit of g ≫ f, transported through upperStarComp.
The derived direct-image composition is its conjugate under the adjunctions;
the Leray comparison is compatible with that composition by the uniqueness
of right-derived comparisons. The two complex comparison maps combine to
the displayed map of the composite pair, by naturality of
mapDerivedCategoryFactors and the composition comparison. Apply RΓ and
homologyFunctor, using preservation of composition, to obtain the equation.
These arguments apply to all cochain complexes; bounded-below complexes are
only the inputs needed in this statement. -/
theorem derivedEtaleCohomology_pullback_laws
    (P : ∀ {X Y : Scheme.{uNatural}} (f : Y ⟶ X)
      (K : CochainComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1}) ℤ)
      (L : CochainComplex (Sheaf Y.smallEtaleTopology AddCommGrpCat.{uNatural + 1}) ℤ)
      (_ : ((upperStar AddCommGrpCat.{uNatural + 1} f).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K ⟶ L) (n : ℤ),
      (cohomology AddCommGrpCat.{uNatural + 1} X n).obj (DerivedCategory.Q.obj K) ⟶
        (cohomology AddCommGrpCat.{uNatural + 1} Y n).obj (DerivedCategory.Q.obj L))
    (hP : ∀ {X Y : Scheme.{uNatural}} (f : Y ⟶ X)
      (K : CochainComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1}) ℤ)
      (L : CochainComplex (Sheaf Y.smallEtaleTopology AddCommGrpCat.{uNatural + 1}) ℤ)
      (v : ((upperStar AddCommGrpCat.{uNatural + 1} f).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K ⟶ L) (n : ℤ),
      P f K L v n = (DerivedCategory.homologyFunctor AddCommGrpCat.{uNatural + 1} n).map
        ((rightDerivedGlobalSections AddCommGrpCat.{uNatural + 1} X).map
            ((mapDerivedUpperStarLowerStarAdjunction AddCommGrpCat.{uNatural + 1} f).unit.app
              (DerivedCategory.Q.obj K)) ≫
          (rightDerivedLowerStarCompRightDerivedGlobalSectionsIso
            AddCommGrpCat.{uNatural + 1} f).hom.app
              ((upperStar AddCommGrpCat.{uNatural + 1} f).mapDerivedCategory.obj
                (DerivedCategory.Q.obj K)) ≫
          (rightDerivedGlobalSections AddCommGrpCat.{uNatural + 1} Y).map
            ((upperStar AddCommGrpCat.{uNatural + 1} f).mapDerivedCategoryFactors.hom.app K ≫
              DerivedCategory.Q.map v))) :
    (∀ (X : Scheme.{uNatural})
        (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1})),
        ∀ n : ℤ, P (𝟙 X) K.obj K.obj
            ((NatIso.mapHomologicalComplex (upperStarId AddCommGrpCat.{uNatural + 1} X)
              (ComplexShape.up ℤ) ≪≫ Functor.mapHomologicalComplexIdIso
                (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1})
                  (ComplexShape.up ℤ)).hom.app K.obj) n = 𝟙 _) ∧
      (∀ {X Y Z : Scheme.{uNatural}} (f : Y ⟶ X) (g : Z ⟶ Y)
        (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1}))
        (L : CochainComplex.Plus (Sheaf Y.smallEtaleTopology AddCommGrpCat.{uNatural + 1}))
        (N : CochainComplex.Plus (Sheaf Z.smallEtaleTopology AddCommGrpCat.{uNatural + 1}))
        (v : ((upperStar AddCommGrpCat.{uNatural + 1} f).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K.obj ⟶ L.obj)
        (w : ((upperStar AddCommGrpCat.{uNatural + 1} g).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj L.obj ⟶ N.obj),
        ∀ n : ℤ, P (g ≫ f) K.obj N.obj
            ((Functor.mapHomologicalComplexCompIso
              (upperStarComp AddCommGrpCat.{uNatural + 1} g f).symm
                (ComplexShape.up ℤ)).inv.app K.obj ≫
              ((upperStar AddCommGrpCat.{uNatural + 1} g).mapHomologicalComplex
                (ComplexShape.up ℤ)).map v ≫ w) n =
            P f K.obj L.obj v n ≫
              P g L.obj N.obj w n) := by
  constructor
  · intro X K n
    rw [hP]
    have hf := Functor.mapDerivedCategoryNatIso_fac
      (upperStarId AddCommGrpCat.{uNatural + 1} X) K.obj
    have hi := idFactors K.obj
    have h := derivedUnitLeray_id X (DerivedCategory.Q.obj K.obj)
    simp only [Iso.trans_hom, NatTrans.comp_app] at h
    rw [hi, reassoc_of% hf] at h
    simpa only [Functor.map_comp, Iso.trans_hom, NatTrans.comp_app,
      Category.assoc, NatIso.mapHomologicalComplex, Functor.id_obj, cohomology,
      Functor.comp_obj,
      CategoryTheory.Functor.map_id] using
      congrArg (DerivedCategory.homologyFunctor AddCommGrpCat.{uNatural + 1} n).map h
  · intro X Y Z f g K L N v w n
    rw [hP, hP, hP]
    have hc := derivedUnitLeray_comp f g (DerivedCategory.Q.obj K.obj)
    have hf := compFactors (upperStar AddCommGrpCat.{uNatural + 1} f)
      (upperStar AddCommGrpCat.{uNatural + 1} g)
      (upperStar AddCommGrpCat.{uNatural + 1} (g ≫ f))
      (upperStarComp AddCommGrpCat.{uNatural + 1} g f) K.obj
    have hn := unitLeray_naturality g
      ((upperStar AddCommGrpCat.{uNatural + 1} f).mapDerivedCategoryFactors.hom.app K.obj ≫
        DerivedCategory.Q.map v)
    have hv := (upperStar AddCommGrpCat.{uNatural + 1} g).mapDerivedCategoryFactors.hom.naturality v
    simp only [Functor.comp_map, Functor.comp_obj] at hv
    have hh := congrArg (fun a ↦ a ≫
      (rightDerivedGlobalSections AddCommGrpCat.{uNatural + 1} Z).map
        ((upperStar AddCommGrpCat.{uNatural + 1} g).mapDerivedCategory.map
          ((upperStar AddCommGrpCat.{uNatural + 1} f).mapDerivedCategoryFactors.hom.app K.obj) ≫
          (upperStar AddCommGrpCat.{uNatural + 1} g).mapDerivedCategoryFactors.hom.app
            (((upperStar AddCommGrpCat.{uNatural + 1} f).mapHomologicalComplex (.up ℤ)).obj
              K.obj) ≫ DerivedCategory.Q.map
                (((upperStar AddCommGrpCat.{uNatural + 1} g).mapHomologicalComplex (.up ℤ)).map v) ≫
                  DerivedCategory.Q.map w)) hc
    simp only [Functor.map_comp, Iso.trans_hom, NatTrans.comp_app, Category.assoc] at hh
    have hfr := congrArg (rightDerivedGlobalSections AddCommGrpCat.{uNatural + 1} Z).map hf
    simp only [Functor.map_comp, Iso.trans_hom, NatTrans.comp_app, Category.assoc] at hfr
    rw [reassoc_of% hfr] at hh
    have hvr := congrArg (rightDerivedGlobalSections AddCommGrpCat.{uNatural + 1} Z).map hv
    simp only [Functor.map_comp] at hvr
    rw [← reassoc_of% hvr] at hh
    simp only [Functor.map_comp, Category.assoc] at hn
    rw [← reassoc_of% hn] at hh
    simpa only [Functor.map_comp, Category.assoc] using
      congrArg (DerivedCategory.homologyFunctor AddCommGrpCat.{uNatural + 1} n).map hh



end AlgebraicGeometry.Etale
