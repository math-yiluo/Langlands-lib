/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.Etale.Derived.GlobalSections

/-! # Transport of canonical pullback maps to complex representatives

Source: Stacks Project, Tags 0GIT and 0EZM, termwise pullback argument.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

/-- Termwise inverse image of a cochain complex. 
(blueprint: lem-weil-pbc-etale-complex-pullback-transport)
-/
noncomputable abbrev presentationPullback {X Y : Scheme.{u}} (f : X ⟶ Y)
    (C : CochainComplex (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) ℤ) :=
  ((upperStar AddCommGrpCat.{u + 1} f).mapHomologicalComplex (ComplexShape.up ℤ)).obj C

/-- The identity comparison, with its source and target explicit so that clients do not
unfold inverse-image functors when checking the type of the identity law.
(blueprint: lem-weil-pbc-etale-complex-pullback-transport) -/
noncomputable def presentationIdentityMap {I : Type u} [SmallCategory I]
    (D : I ⥤ Scheme.{u}) (i : I)
    (C : CochainComplex (Sheaf (D.obj i).smallEtaleTopology AddCommGrpCat.{u + 1}) ℤ) :
    presentationPullback (D.map (𝟙 i)) C ⟶ C :=
  (NatIso.mapHomologicalComplex
    (eqToIso (congrArg (upperStar AddCommGrpCat.{u + 1}) (D.map_id i)))
    (ComplexShape.up ℤ)).hom.app C ≫
  (NatIso.mapHomologicalComplex (upperStarId AddCommGrpCat.{u + 1} (D.obj i))
    (ComplexShape.up ℤ)).hom.app C

/-- The composition comparison evaluated termwise on a complex. 
(blueprint: lem-weil-pbc-etale-complex-pullback-transport)
-/
noncomputable def presentationCompIso {X Y T : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ T) (h : X ⟶ T) (hh : h = f ≫ g)
    (C : CochainComplex (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) ℤ) :
    presentationPullback h C ≅ presentationPullback f (presentationPullback g C) :=
  (NatIso.mapHomologicalComplex
    (upperStarComp AddCommGrpCat.{u + 1} f g h hh) (ComplexShape.up ℤ)).app C

/-- The family of termwise pullbacks along a natural family of structure maps. 
(blueprint: lem-weil-pbc-etale-complex-pullback-transport)
-/
noncomputable def presentationFamily {I : Type u} [SmallCategory I]
    {T : Scheme.{u}} (D : I ⥤ Scheme.{u}) (t : D ⟶ (Functor.const I).obj T)
    (C : CochainComplex (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) ℤ)
    (i : I) := presentationPullback (t.app i) C

/-- Canonical transition between the pullbacks of a fixed complex. 
(blueprint: lem-weil-pbc-etale-complex-pullback-transport)
-/
noncomputable def presentationTransition {I : Type u} [SmallCategory I]
    {T : Scheme.{u}} (D : I ⥤ Scheme.{u}) (t : D ⟶ (Functor.const I).obj T)
    (C : CochainComplex (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) ℤ)
    {i j : I} (f : j ⟶ i) :
    presentationPullback (D.map f) (presentationFamily D t C i) ⟶
      presentationFamily D t C j :=
  (presentationCompIso (D.map f) (t.app i) (t.app j)
    ((Category.comp_id (t.app j)).symm.trans (t.naturality f).symm) C).inv

/-- The canonical comparison between a cone pullback and an iterated pullback. 
(blueprint: lem-weil-pbc-etale-complex-pullback-transport)
-/
noncomputable def presentationConeIso {I : Type u} [SmallCategory I]
    {T : Scheme.{u}} (D : I ⥤ Scheme.{u}) (c : Cone D)
    (t : D ⟶ (Functor.const I).obj T) (p : c.pt ⟶ T)
    (hp : ∀ i, c.π.app i ≫ t.app i = p)
    (C : CochainComplex (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) ℤ)
    (i : I) : presentationPullback p C ≅
      presentationPullback (c.π.app i) (presentationFamily D t C i) :=
  presentationCompIso (c.π.app i) (t.app i) p (hp i).symm C

/-- Identify derived pullback cohomology with cohomology of a termwise representative. 
(blueprint: lem-weil-pbc-etale-complex-pullback-transport)
-/
noncomputable def presentationRepresentativeIso {X T : Scheme.{u}} (g : X ⟶ T)
    {K : DerivedCategory (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})}
    {C : CochainComplex (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) ℤ}
    (q : K ≅ DerivedCategory.Q.obj C) (n : ℤ) :
    (cohomology AddCommGrpCat.{u + 1} X n).obj
      ((upperStar AddCommGrpCat.{u + 1} g).mapDerivedCategory.obj K) ≅
    (cohomology AddCommGrpCat.{u + 1} X n).obj
      (DerivedCategory.Q.obj (presentationPullback g C)) :=
  (cohomology AddCommGrpCat.{u + 1} X n).mapIso
    (((upperStar AddCommGrpCat.{u + 1} g).mapDerivedCategory.mapIso q) ≪≫
      (upperStar AddCommGrpCat.{u + 1} g).mapDerivedCategoryFactors.app C)

/-- Derived cohomology pullback along a triangle of scheme maps, followed by the
inverse composition comparison. 
(blueprint: lem-weil-pbc-etale-complex-pullback-transport)
-/
noncomputable def presentationDerivedMap {X Y T : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ T) (h : X ⟶ T) (hh : h = f ≫ g)
    (K : DerivedCategory (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})) (n : ℤ) :
    (cohomology AddCommGrpCat.{u + 1} Y n).obj
      ((upperStar AddCommGrpCat.{u + 1} g).mapDerivedCategory.obj K) ⟶
    (cohomology AddCommGrpCat.{u + 1} X n).obj
      ((upperStar AddCommGrpCat.{u + 1} h).mapDerivedCategory.obj K) :=
  (cohomology AddCommGrpCat.{u + 1} Y n).map
    ((mapDerivedUpperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).unit.app
      ((upperStar AddCommGrpCat.{u + 1} g).mapDerivedCategory.obj K)) ≫
  (DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} n).map
    ((rightDerivedLowerStarCompRightDerivedGlobalSectionsIso
      AddCommGrpCat.{u + 1} f).hom.app
      ((upperStar AddCommGrpCat.{u + 1} f).mapDerivedCategory.obj
        ((upperStar AddCommGrpCat.{u + 1} g).mapDerivedCategory.obj K))) ≫
  (cohomology AddCommGrpCat.{u + 1} X n).map
    ((Functor.mapDerivedCategoryNatIso
      (upperStarComp AddCommGrpCat.{u + 1} f g h hh) ≪≫
      (Functor.mapDerivedCategoryCompIso
        (upperStar AddCommGrpCat.{u + 1} g)
        (upperStar AddCommGrpCat.{u + 1} f)).symm).inv.app K)

set_option backward.isDefEq.respectTransparency false in
private theorem composition_factors {X Y T : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ T) (h : X ⟶ T) (hh : h = f ≫ g)
    (C : CochainComplex (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) ℤ) :
    (Functor.mapDerivedCategoryNatIso
      (upperStarComp AddCommGrpCat.{u + 1} f g h hh) ≪≫
      (Functor.mapDerivedCategoryCompIso
        (upperStar AddCommGrpCat.{u + 1} g)
        (upperStar AddCommGrpCat.{u + 1} f)).symm).inv.app (DerivedCategory.Q.obj C) ≫
        (upperStar AddCommGrpCat.{u + 1} h).mapDerivedCategoryFactors.hom.app C =
    (upperStar AddCommGrpCat.{u + 1} f).mapDerivedCategory.map
        ((upperStar AddCommGrpCat.{u + 1} g).mapDerivedCategoryFactors.hom.app C) ≫
      (upperStar AddCommGrpCat.{u + 1} f).mapDerivedCategoryFactors.hom.app
        (presentationPullback g C) ≫
      DerivedCategory.Q.map (presentationCompIso f g h hh C).inv := by
  apply (cancel_epi ((Functor.mapDerivedCategoryNatIso
      (upperStarComp AddCommGrpCat.{u + 1} f g h hh) ≪≫
      (Functor.mapDerivedCategoryCompIso
        (upperStar AddCommGrpCat.{u + 1} g)
        (upperStar AddCommGrpCat.{u + 1} f)).symm).hom.app (DerivedCategory.Q.obj C))).mp
  rw [Iso.hom_inv_id_app_assoc]
  simp only [Iso.trans_hom, NatTrans.comp_app, Category.assoc]
  have hc := Functor.mapDerivedCategoryCompIso_fac
    (upperStar AddCommGrpCat.{u + 1} g) (upperStar AddCommGrpCat.{u + 1} f) C
  have hn := Functor.mapDerivedCategoryNatIso_fac
    (upperStarComp AddCommGrpCat.{u + 1} f g h hh) C
  have hi : DerivedCategory.Q.map
      ((Functor.mapHomologicalComplexCompIso
        (Iso.refl (upperStar AddCommGrpCat.{u + 1} g ⋙
          upperStar AddCommGrpCat.{u + 1} f)) (ComplexShape.up ℤ)).hom.app C) = 𝟙 _ := by
    rw [← DerivedCategory.Q.map_id]
    congr 1
  simp only [hi] at hc
  dsimp only [Functor.comp_obj] at hc
  simp only [Category.comp_id] at hc
  erw [reassoc_of% hc, reassoc_of% hn]
  simp only [presentationCompIso, ← Functor.map_comp]
  change _ = _ ≫ DerivedCategory.Q.map
    ((NatIso.mapHomologicalComplex (upperStarComp AddCommGrpCat.{u + 1} f g h hh)
      (ComplexShape.up ℤ)).hom.app C ≫
     (NatIso.mapHomologicalComplex (upperStarComp AddCommGrpCat.{u + 1} f g h hh)
      (ComplexShape.up ℤ)).inv.app C)
  simp

private theorem pullback_naturality {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℤ)
    {A B : DerivedCategory (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})}
    (m : A ⟶ B) :
    (cohomology AddCommGrpCat.{u + 1} Y n).map
      ((mapDerivedUpperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).unit.app A) ≫
    (DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} n).map
      ((rightDerivedLowerStarCompRightDerivedGlobalSectionsIso
        AddCommGrpCat.{u + 1} f).hom.app
        ((upperStar AddCommGrpCat.{u + 1} f).mapDerivedCategory.obj A)) ≫
    (cohomology AddCommGrpCat.{u + 1} X n).map
      ((upperStar AddCommGrpCat.{u + 1} f).mapDerivedCategory.map m) =
    (cohomology AddCommGrpCat.{u + 1} Y n).map m ≫
    (cohomology AddCommGrpCat.{u + 1} Y n).map
      ((mapDerivedUpperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).unit.app B) ≫
    (DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} n).map
      ((rightDerivedLowerStarCompRightDerivedGlobalSectionsIso
        AddCommGrpCat.{u + 1} f).hom.app
        ((upperStar AddCommGrpCat.{u + 1} f).mapDerivedCategory.obj B)) := by
  have hu := (mapDerivedUpperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).unit.naturality m
  have hl := (rightDerivedLowerStarCompRightDerivedGlobalSectionsIso
    AddCommGrpCat.{u + 1} f).hom.naturality
      ((upperStar AddCommGrpCat.{u + 1} f).mapDerivedCategory.map m)
  dsimp only [cohomology, Functor.comp_map]
  simp only [← Functor.map_comp, ← Category.assoc]
  congr 1
  rw [Category.assoc, ← hl]
  dsimp only [Functor.comp_map, Functor.id_map] at hu ⊢
  rw [← Category.assoc, ← Functor.map_comp, ← hu]

/-- Canonical pullback along one triangle commutes with replacement by a complex.
Source: Stacks Project, Tag 0GIT, proof (the pullbacks of a representative represent
its derived pullbacks); Tag 0EZM, proof (canonical transition maps).
(blueprint: lem-weil-pbc-etale-complex-pullback-transport)

Proof: first use naturality of the derived adjunction unit and the Leray comparison
with the image of q under the inverse image along g. This moves q from the source
of the canonical derived map to its target. For QC, insert the exact-functor
localization comparisons for g, f, and h. Naturality of the unit and Leray comparison
moves the comparison for g to the source. The defining equation hP identifies the
remaining unit, Leray, and comparison for f with P. The equations
mapDerivedCategoryNatIso_fac and mapDerivedCategoryCompIso_fac identify the derived
composition comparison with Q of its termwise counterpart, conjugated by these
localization comparisons. Cancel the invertible comparisons and apply functoriality
of cohomology. The resulting equality is the displayed commuting square. No limit,
filteredness, boundedness, or continuity is used. -/
theorem presentation_pullback_transport {X Y T : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ T) (h : X ⟶ T) (hh : h = f ≫ g)
    (K : DerivedCategory (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (n : ℤ)
    (C : CochainComplex (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) ℤ)
    (q : K ≅ DerivedCategory.Q.obj C)
    (P : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y)
      (K : CochainComplex (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) ℤ),
      (cohomology AddCommGrpCat.{u + 1} Y n).obj (DerivedCategory.Q.obj K) ⟶
      (cohomology AddCommGrpCat.{u + 1} X n).obj
        (DerivedCategory.Q.obj
          (((upperStar AddCommGrpCat.{u + 1} f).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj K)))
    (hP : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y)
      (K : CochainComplex (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) ℤ),
      P f K = (DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} n).map
        ((rightDerivedGlobalSections AddCommGrpCat.{u + 1} Y).map
          ((mapDerivedUpperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).unit.app
            (DerivedCategory.Q.obj K)) ≫
        (Functor.rightDerivedFunctorCompIso'
          (lowerStar AddCommGrpCat.{u + 1} f)
          (Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{u + 1})
          (Functor.isoWhiskerLeft (lowerStar AddCommGrpCat.{u + 1} f)
              (Sheaf.ΓNatIsoSheafSections Y.smallEtaleTopology AddCommGrpCat.{u + 1}
                terminalIsTerminal) ≪≫
            lowerStarCompSheafSectionsTerminalIso AddCommGrpCat.{u + 1} f ≪≫
            (Sheaf.ΓNatIsoSheafSections X.smallEtaleTopology AddCommGrpCat.{u + 1}
              terminalIsTerminal).symm)).hom.app
                ((upperStar AddCommGrpCat.{u + 1} f).mapDerivedCategory.obj
                  (DerivedCategory.Q.obj K)) ≫
        (rightDerivedGlobalSections AddCommGrpCat.{u + 1} X).map
          ((upperStar AddCommGrpCat.{u + 1} f).mapDerivedCategoryFactors.hom.app K))) :
    presentationDerivedMap f g h hh K n ≫ (presentationRepresentativeIso h q n).hom =
      (presentationRepresentativeIso g q n).hom ≫ P f (presentationPullback g C) ≫
        (cohomology AddCommGrpCat.{u + 1} X n).map
          (DerivedCategory.Q.map (presentationCompIso f g h hh C).inv) := by
  let e := (upperStar AddCommGrpCat.{u + 1} g).mapDerivedCategory.mapIso q ≪≫
    (upperStar AddCommGrpCat.{u + 1} g).mapDerivedCategoryFactors.app C
  let d := Functor.mapDerivedCategoryNatIso
    (upperStarComp AddCommGrpCat.{u + 1} f g h hh) ≪≫
      (Functor.mapDerivedCategoryCompIso
        (upperStar AddCommGrpCat.{u + 1} g) (upperStar AddCommGrpCat.{u + 1} f)).symm
  have hd : d.inv.app K ≫
      (upperStar AddCommGrpCat.{u + 1} h).mapDerivedCategory.map q.hom ≫
      (upperStar AddCommGrpCat.{u + 1} h).mapDerivedCategoryFactors.hom.app C =
      (upperStar AddCommGrpCat.{u + 1} f).mapDerivedCategory.map e.hom ≫
      (upperStar AddCommGrpCat.{u + 1} f).mapDerivedCategoryFactors.hom.app
        (presentationPullback g C) ≫
      DerivedCategory.Q.map (presentationCompIso f g h hh C).inv := by
    rw [← d.inv.naturality_assoc q.hom]
    dsimp only [Functor.comp_map]
    rw [composition_factors f g h hh C]
    simp only [e, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom,
      Functor.map_comp, Category.assoc]
  rw [hP]
  simp only [presentationDerivedMap, presentationRepresentativeIso, Functor.mapIso_hom,
    Iso.trans_hom, Iso.app_hom, Functor.map_comp, Category.assoc]
  simp only [← Functor.map_comp]
  rw [hd]
  simp only [Functor.map_comp]
  have hn := pullback_naturality f n e.hom
  dsimp only [cohomology, Functor.comp_map] at hn ⊢
  rw [reassoc_of% hn]
  simp only [e, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom, Functor.map_comp,
    Category.assoc]
  rfl

end AlgebraicGeometry.Etale
