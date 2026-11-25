/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.Etale.Derived.GlobalSections
import WeilConjectures.AlgebraicGeometry.EtaleSectionsRestrictionSquare

/-! # Naturality of the termwise-to-derived sections comparison

Source: Stacks Project, Tag 03Q9, final injective-complex paragraph.
(blueprint: lem-weil-pbc-sections-comparison-triangle-naturality).
-/

@[expose] public section

universe v

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

namespace AlgebraicGeometry.Etale

private noncomputable def sectionsUnit (Z : Scheme.{v})
    (C : CochainComplex (Sheaf Z.smallEtaleTopology AddCommGrpCat.{v + 1}) ℤ) :=
  (DerivedCategory.quotientCompQhIso AddCommGrpCat.{v + 1}).inv.app
      (((Sheaf.Γ Z.smallEtaleTopology AddCommGrpCat.{v + 1}).mapHomologicalComplex
        (.up ℤ)).obj C) ≫
    (Sheaf.Γ Z.smallEtaleTopology AddCommGrpCat.{v + 1}).rightDerivedFunctorUnit.app
      ((HomotopyCategory.quotient _ _).obj C) ≫
    (Sheaf.Γ Z.smallEtaleTopology AddCommGrpCat.{v + 1}).rightDerivedFunctor.map
      ((DerivedCategory.quotientCompQhIso _).hom.app C)

private theorem sectionsUnit_naturality (Z : Scheme.{v})
    {C D : CochainComplex (Sheaf Z.smallEtaleTopology AddCommGrpCat.{v + 1}) ℤ}
    (f : C ⟶ D) :
    DerivedCategory.Q.map
        (((Sheaf.Γ Z.smallEtaleTopology AddCommGrpCat.{v + 1}).mapHomologicalComplex
          (.up ℤ)).map f) ≫ sectionsUnit Z D =
      sectionsUnit Z C ≫
        (Sheaf.Γ Z.smallEtaleTopology AddCommGrpCat.{v + 1}).rightDerivedFunctor.map
          (DerivedCategory.Q.map f) := by
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
  set_option backward.defeqAttrib.useBackward true in
  exact (by
    unfold sectionsUnit
    rw [DerivedCategory.quotientCompQhIso_inv_naturality_assoc]
    have hn := NatTrans.naturality
      (Sheaf.Γ Z.smallEtaleTopology AddCommGrpCat.{v + 1}).rightDerivedFunctorUnit
      ((HomotopyCategory.quotient
        (Sheaf Z.smallEtaleTopology AddCommGrpCat.{v + 1}) (.up ℤ)).map f)
    dsimp only [Functor.comp_map] at hn
    erw [reassoc_of% hn]
    simp only [Category.assoc, ← Functor.map_comp]
    rw [← DerivedCategory.quotientCompQhIso_hom_naturality]
  )

private theorem triangle_localization {X Y T : Scheme.{v}}
    (a : X ⟶ Y) (g : Y ⟶ T) (h : X ⟶ T) (hh : h = a ≫ g)
    (J : CochainComplex (Sheaf T.smallEtaleTopology AddCommGrpCat.{v + 1}) ℤ) :
    let L := upperStar AddCommGrpCat.{v + 1} a
    let G := upperStar AddCommGrpCat.{v + 1} g
    let H := upperStar AddCommGrpCat.{v + 1} h
    let C := (G.mapHomologicalComplex (.up ℤ)).obj J
    let e := upperStarComp AddCommGrpCat.{v + 1} a g h hh
    L.mapDerivedCategory.map (G.mapDerivedCategoryFactors.inv.app J) ≫
      (Functor.mapDerivedCategoryNatIso e ≪≫
        (Functor.mapDerivedCategoryCompIso G L).symm).inv.app (DerivedCategory.Q.obj J) =
      L.mapDerivedCategoryFactors.hom.app C ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex e (.up ℤ)).inv.app J) ≫
          H.mapDerivedCategoryFactors.inv.app J := by
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
  set_option backward.defeqAttrib.useBackward true in
  exact (by
    dsimp only
    let L := upperStar AddCommGrpCat.{v + 1} a
    let G := upperStar AddCommGrpCat.{v + 1} g
    let e := upperStarComp AddCommGrpCat.{v + 1} a g h hh
    have hc := Functor.mapDerivedCategoryCompIso_fac G L J
    have hn := Functor.mapDerivedCategoryNatIso_fac e J
    have hid : (Functor.mapHomologicalComplexCompIso (Iso.refl (G ⋙ L))
        (.up ℤ)).hom.app J = 𝟙 _ := by
      ext i
      rfl
    erw [hid, CategoryTheory.Functor.map_id, Category.comp_id] at hc
    have hf : (Functor.mapDerivedCategoryNatIso e ≪≫
        (Functor.mapDerivedCategoryCompIso G L).symm).hom.app (DerivedCategory.Q.obj J) ≫
        L.mapDerivedCategory.map (G.mapDerivedCategoryFactors.hom.app J) ≫
          L.mapDerivedCategoryFactors.hom.app
            ((G.mapHomologicalComplex (.up ℤ)).obj J) =
        (upperStar AddCommGrpCat.{v + 1} h).mapDerivedCategoryFactors.hom.app J ≫
          DerivedCategory.Q.map ((NatIso.mapHomologicalComplex e (.up ℤ)).hom.app J) := by
      simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Category.assoc]
      rw [hc]
      exact hn
    apply (cancel_epi (L.mapDerivedCategory.map
      (G.mapDerivedCategoryFactors.hom.app J))).1
    apply (cancel_epi ((Functor.mapDerivedCategoryNatIso e ≪≫
      (Functor.mapDerivedCategoryCompIso G L).symm).hom.app (DerivedCategory.Q.obj J))).1
    rw [← L.mapDerivedCategory.map_comp_assoc]
    simp only [G, L, e, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id,
      Category.id_comp]
    rw [reassoc_of% hf]
    simp only [← DerivedCategory.Q.map_comp_assoc, e, Iso.hom_inv_id_app,
      CategoryTheory.Functor.map_id, Category.id_comp]
    rfl
  )

/-- The sections comparison commutes with restriction along any triangle of schemes.
The local lets spell out the existing comparison maps without importing their defining
module, which uses this theorem. No injectivity or boundedness is required for this square.

Source: Stacks Project, Tag 03Q9, final paragraph, the maps from each neighbourhood
complex to the limit complex and their realization on cohomology.
(blueprint: lem-weil-pbc-sections-comparison-triangle-naturality).

Proof: first work in the homotopy category. Write F for inverse image along a,
R for direct image, G for sections on Y and H for sections on X. The derived
adjunction unit satisfies Q(eta) followed by the derived-direct-image unit equals
eta_D followed by R(F's exact-localization comparison). Naturality of the
right-derived G unit moves Q(eta) past that unit. The defining factorization of
the derived composition isomorphism, followed by the derived isomorphism RG = H,
identifies the resulting composite with Q of the underived sections restriction
followed by H's right-derived unit. Cancel F's localization comparison to get the
restriction square. Pass from the homotopy category to the derived category using
the quotientCompQhIso naturality squares. Next apply the square to g applied
termwise to J, and use naturality of H's derived unit for the chain isomorphism
from a applied to g applied to J to h applied to J. Compatibility of
mapDerivedCategoryNatIso and mapDerivedCategoryCompIso with their localization
factorizations identifies this isomorphism with the displayed derived composition
map. Finally move q.inv through the derived adjunction unit, Leray isomorphism,
and inverse-image composition isomorphism by their naturality, and apply H^n.
This proves the square without inverting any sections unit. It applies also to
nonetale a, negative n, zero complexes, and empty schemes. -/
theorem sectionsComparison_triangle_naturality {X Y T : Scheme.{v}}
    (a : X ⟶ Y) (g : Y ⟶ T) (h : X ⟶ T) (hh : h = a ≫ g)
    {K : DerivedCategory (Sheaf T.smallEtaleTopology AddCommGrpCat.{v + 1})}
    (J : CochainComplex (Sheaf T.smallEtaleTopology AddCommGrpCat.{v + 1}) ℤ)
    (q : K ≅ DerivedCategory.Q.obj J) (n : ℤ) :
  let restriction :=
    Functor.whiskerRight (upperStarLowerStarAdjunction AddCommGrpCat.{v + 1} a).unit
          (Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{v + 1}) ≫
        (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft (upperStar AddCommGrpCat.{v + 1} a)
          (lowerStarCompGlobalSectionsIso AddCommGrpCat.{v + 1} a).hom
  let toDerived (Y : Scheme.{v})
      (C : CochainComplex (Sheaf Y.smallEtaleTopology AddCommGrpCat.{v + 1}) ℤ) :=
    (DerivedCategory.homologyFunctor AddCommGrpCat.{v + 1} n).map
        ((DerivedCategory.quotientCompQhIso AddCommGrpCat.{v + 1}).inv.app
            (((Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{v + 1}).mapHomologicalComplex
              (.up ℤ)).obj C) ≫
          (Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{v + 1}).rightDerivedFunctorUnit.app
            ((HomotopyCategory.quotient _ _).obj C) ≫
          (Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{v + 1}).rightDerivedFunctor.map
            ((DerivedCategory.quotientCompQhIso _).hom.app C))
  let comparison (Y : Scheme.{v}) (g : Y ⟶ T) :=
    toDerived Y
          (((upperStar AddCommGrpCat.{v + 1} g).mapHomologicalComplex (.up ℤ)).obj J) ≫
        (cohomology AddCommGrpCat.{v + 1} Y n).map
          (((upperStar AddCommGrpCat.{v + 1} g).mapDerivedCategoryFactors.inv.app J) ≫
            (upperStar AddCommGrpCat.{v + 1} g).mapDerivedCategory.map q.inv)
  let chainRestriction :=
    (DerivedCategory.homologyFunctor AddCommGrpCat.{v + 1} n).map
        (DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex restriction (.up ℤ)).app
              (((upperStar AddCommGrpCat.{v + 1} g).mapHomologicalComplex (.up ℤ)).obj J) ≫
            ((Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{v + 1}).mapHomologicalComplex
              (.up ℤ)).map ((NatIso.mapHomologicalComplex
                (upperStarComp AddCommGrpCat.{v + 1} a g h hh) (.up ℤ)).inv.app J)))
  comparison Y g ≫
    (cohomology AddCommGrpCat.{v + 1} Y n).map
      ((mapDerivedUpperStarLowerStarAdjunction AddCommGrpCat.{v + 1} a).unit.app
        ((upperStar AddCommGrpCat.{v + 1} g).mapDerivedCategory.obj K)) ≫
    (DerivedCategory.homologyFunctor AddCommGrpCat.{v + 1} n).map
      ((rightDerivedLowerStarCompRightDerivedGlobalSectionsIso
        AddCommGrpCat.{v + 1} a).hom.app
          ((upperStar AddCommGrpCat.{v + 1} a).mapDerivedCategory.obj
            ((upperStar AddCommGrpCat.{v + 1} g).mapDerivedCategory.obj K))) ≫
    (cohomology AddCommGrpCat.{v + 1} X n).map
      ((Functor.mapDerivedCategoryNatIso
        (upperStarComp AddCommGrpCat.{v + 1} a g h hh) ≪≫
          (Functor.mapDerivedCategoryCompIso
            (upperStar AddCommGrpCat.{v + 1} g)
            (upperStar AddCommGrpCat.{v + 1} a)).symm).inv.app K) =
    chainRestriction ≫ comparison X h := by
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
  set_option backward.defeqAttrib.useBackward true in
  exact (by
    let L := upperStar AddCommGrpCat.{v + 1} a
    let G := upperStar AddCommGrpCat.{v + 1} g
    let H := upperStar AddCommGrpCat.{v + 1} h
    let RY := (Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{v + 1}).rightDerivedFunctor
    let RX := (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{v + 1}).rightDerivedFunctor
    let C := (G.mapHomologicalComplex (.up ℤ)).obj J
    let D := (L.mapHomologicalComplex (.up ℤ)).obj C
    let E := (H.mapHomologicalComplex (.up ℤ)).obj J
    let e := upperStarComp AddCommGrpCat.{v + 1} a g h hh
    let d := (Functor.mapDerivedCategoryNatIso e ≪≫
      (Functor.mapDerivedCategoryCompIso G L).symm).inv
    let u := (mapDerivedUpperStarLowerStarAdjunction AddCommGrpCat.{v + 1} a).unit
    let l := (rightDerivedLowerStarCompRightDerivedGlobalSectionsIso
      AddCommGrpCat.{v + 1} a).hom
    let v := G.mapDerivedCategoryFactors.inv.app J ≫ G.mapDerivedCategory.map q.inv
    let w := H.mapDerivedCategoryFactors.inv.app J ≫ H.mapDerivedCategory.map q.inv
    let r := Functor.whiskerRight
        (upperStarLowerStarAdjunction AddCommGrpCat.{v + 1} a).unit
        (Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{v + 1}) ≫
      (Functor.associator _ _ _).hom ≫ Functor.whiskerLeft L
        (lowerStarCompGlobalSectionsIso AddCommGrpCat.{v + 1} a).hom
    let t := (NatIso.mapHomologicalComplex e (.up ℤ)).inv.app J
    dsimp only
    simp only [cohomology, rightDerivedGlobalSections, Functor.comp_map]
    simp only [← Functor.map_comp, Category.assoc]
    congr 1
    suffices heq : sectionsUnit Y C ≫ RY.map v ≫ RY.map (u.app (G.mapDerivedCategory.obj K)) ≫
        l.app (L.mapDerivedCategory.obj (G.mapDerivedCategory.obj K)) ≫ RX.map (d.app K) =
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex r (.up ℤ)).app C ≫
        ((Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{v + 1}).mapHomologicalComplex
          (.up ℤ)).map t) ≫ sectionsUnit X E ≫ RX.map w by
      simpa only [sectionsUnit, RY, RX, C, E, G, H, v, w, r, L, u, l, d, e, t,
        Functor.map_comp, Category.assoc] using heq
    have hu := u.naturality v
    dsimp only [Functor.id_map, Functor.comp_map] at hu
    erw [← RY.map_comp_assoc, hu, RY.map_comp, Category.assoc]
    have hl := l.naturality (L.mapDerivedCategory.map v)
    dsimp only [Functor.comp_map] at hl
    simp only [Category.assoc]
    erw [reassoc_of% hl]
    have hs := sectionsComparison_restriction_square a C
    change sectionsUnit Y C ≫ RY.map (u.app (DerivedCategory.Q.obj C)) ≫
        l.app (L.mapDerivedCategory.obj (DerivedCategory.Q.obj C)) =
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex r (.up ℤ)).app C) ≫
        sectionsUnit X D ≫ RX.map (L.mapDerivedCategoryFactors.inv.app C) at hs
    simp only [sectionsUnit, Category.assoc] at hs
    erw [reassoc_of% hs]
    simp only [Category.assoc, DerivedCategory.Q.map_comp]
    have hv : L.mapDerivedCategoryFactors.inv.app C ≫
        L.mapDerivedCategory.map v ≫ d.app K = DerivedCategory.Q.map t ≫ w := by
      dsimp only [v, w]
      simp only [Functor.map_comp, Category.assoc]
      have hd := d.naturality q.inv
      dsimp only [Functor.comp_map] at hd
      erw [hd]
      have ht := triangle_localization a g h hh J
      change L.mapDerivedCategory.map (G.mapDerivedCategoryFactors.inv.app J) ≫
        d.app (DerivedCategory.Q.obj J) =
        L.mapDerivedCategoryFactors.hom.app C ≫ DerivedCategory.Q.map t ≫
          H.mapDerivedCategoryFactors.inv.app J at ht
      rw [reassoc_of% ht]
      simp only [Iso.inv_hom_id_app_assoc]
      rfl
    have hnat := sectionsUnit_naturality X t
    suffices heq : sectionsUnit X D ≫
        RX.map (L.mapDerivedCategoryFactors.inv.app C ≫ L.mapDerivedCategory.map v ≫
          d.app K) = DerivedCategory.Q.map
            (((Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{v + 1}).mapHomologicalComplex
              (.up ℤ)).map t) ≫ sectionsUnit X E ≫ RX.map w by
      simpa only [sectionsUnit, RX, rightDerivedGlobalSections, Functor.map_comp,
        Category.assoc] using congrArg
          (fun z => DerivedCategory.Q.map
            ((NatTrans.mapHomologicalComplex r (.up ℤ)).app C) ≫ z) heq
    rw [hv, RX.map_comp]
    convert (congrArg (fun z => z ≫ RX.map w) hnat).symm using 1 <;>
      simp only [Category.assoc] <;> rfl
  )

end AlgebraicGeometry.Etale
