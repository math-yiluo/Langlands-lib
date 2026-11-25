/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.Etale.Derived.GlobalSections
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusComp
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunction
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus

/-!
# Cohomology pullback and the derived unit

Source: Stacks Project, cohomology.tex, Lemmas 01EZ and 01F8, equations 01F9 and 01FA;
sites-cohomology.tex, Remark 08J6 and Lemmas 072Z and 07A6
(blueprint: lem-weil-pbc-cohomology-pullback-derived-unit).

The Leray isomorphism used below is `Functor.rightDerivedFunctorPlusCompIso'` applied to
`Etale.lowerStarCompGlobalSectionsIso`. Its type is a natural isomorphism on all of D⁺.
`Sheaf.Γ` and its bounded below right derived functor are the recorded global-sections
functors; their comparison with the unbounded version is canonical.

The pullback `u^* : RΓ(X, K) ⟶ RΓ(Y, u⁻¹K)` on D⁺ of def-weil-pbc-cohomology-pullback (whose
recorded declaration `Etale.cohomologyMap` covers only the sheaf case) is spelled inline as the
derived comparison (`Functor.rightDerivedDesc`) of the section map `Γ(X, I) ⟶ Γ(Y, u⁻¹I)` given
by the underived unit, followed by the unit of `RΓ(Y, -)`: on resolutions `I` and `u⁻¹I → J`
it is the class of `a ↦ r(η(a))`.
-/

@[expose] public section

universe v

open CategoryTheory CategoryTheory.Limits

/-- Compare a K-injective representative with a bounded below complex of injectives.
The bijectivity of localization on maps into K-injectives lifts both directions of
the comparison isomorphism, and naturality transports invertibility of the unit. -/
private theorem isIso_unit_of_kInjective
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D] [EnoughInjectives C]
    (F : C ⥤ D) [F.Additive] (K : HomotopyCategory.Plus C)
    [CochainComplex.IsKInjective K.obj.as] :
    IsIso (F.rightDerivedFunctorPlusUnith.app K) := by
  let E := DerivedCategory.Plus.injectiveObjectEquivalence C
  let I := (InjectiveObject.ι C).mapHomotopyCategoryPlus.obj
    (E.inverse.obj (DerivedCategory.Plus.Qh.obj K))
  have : CochainComplex.IsKInjective I.obj.as := inferInstance
  let e : DerivedCategory.Plus.Qh.obj I ≅ DerivedCategory.Plus.Qh.obj K :=
    E.counitIso.app (DerivedCategory.Plus.Qh.obj K)
  obtain ⟨a, ha⟩ := (DerivedCategory.Plus.Qh_map_bijective_of_isKInjective K I
    inferInstance).2 e.inv
  obtain ⟨b, hb⟩ := (DerivedCategory.Plus.Qh_map_bijective_of_isKInjective I K
    inferInstance).2 e.hom
  let h : K ≅ I :=
    { hom := a
      inv := b
      hom_inv_id := by
        apply (DerivedCategory.Plus.Qh_map_bijective_of_isKInjective K K inferInstance).1
        simp [Functor.map_comp, ha, hb]
      inv_hom_id := by
        apply (DerivedCategory.Plus.Qh_map_bijective_of_isKInjective I I inferInstance).1
        simp [Functor.map_comp, ha, hb] }
  rw [NatTrans.isIso_app_iff_of_iso F.rightDerivedFunctorPlusUnith h]
  change IsIso (F.rightDerivedFunctorPlusUnith.app
    ((InjectiveObject.ι C).mapHomotopyCategoryPlus.obj _))
  infer_instance


namespace AlgebraicGeometry.Etale

/-- A bounded below K-injective complex remains K-injective under direct image.
Source: Stacks Project, Lemma 08BJ and Remark 08J6
(blueprint: lem-weil-pbc-cohomology-pullback-derived-unit).
Proof, step 3 of the node: inverse image is exact and left adjoint to direct image.
For every acyclic complex `M`, maps `M → f_*J` up to homotopy correspond to maps
`f⁻¹M → J`, which vanish since `f⁻¹M` is acyclic and `J` is K-injective.
Boundedness is preserved because the additive direct image preserves zero objects. -/
theorem lowerStar_isKInjective_boundedBelow {X Y : Scheme.{v}} (f : Y ⟶ X)
    (J : CochainComplex.Plus (Sheaf Y.smallEtaleTopology AddCommGrpCat.{v + 1}))
    [J.obj.IsKInjective] :
    ((lowerStar AddCommGrpCat.{v + 1} f).mapCochainComplexPlus.obj J).obj.IsKInjective := by
  have := (upperStarLowerStarAdjunction AddCommGrpCat.{v + 1} f).preservesKInjectiveComplexes
  exact Functor.PreservesKInjectiveComplexes.isKInjective_map J.obj

/-- On a bounded below K-injective complex `J` the derived direct image and the derived global
sections on both sites are computed by `J` itself: the units are isomorphisms, so the natural
Leray isomorphism `Functor.rightDerivedFunctorPlusCompIso'`, characterized by its unit
compatibility `Functor.rightDerivedFunctorPlusCompIso'_fac`, is the sectionwise identification.
Source: Stacks Project, Lemma 01EZ and Remark 08J6
(blueprint: lem-weil-pbc-cohomology-pullback-derived-unit).
Proof: use the exact inverse-image adjunction to preserve K-injectivity under direct image.
For any bounded below K-injective representative, compare it with the image of a complex
of injective objects under the equivalence `K⁺(Inj) ≌ D⁺`. Localization is bijective on
maps into either K-injective complex, so both directions of the derived isomorphism lift
and their composites are identities already in the homotopy category. Naturality of the
derived-functor unit transports its invertibility from the complex of injective objects.
Apply this argument to direct image and to global sections on the two sites. -/
theorem lerayPlus_on_kInjective {X Y : Scheme.{v}} (f : Y ⟶ X)
    (J : HomotopyCategory.Plus (Sheaf Y.smallEtaleTopology AddCommGrpCat.{v + 1}))
    [CochainComplex.IsKInjective J.obj.as] :
    IsIso ((lowerStar AddCommGrpCat.{v + 1} f).rightDerivedFunctorPlusUnith.app J) ∧
    IsIso ((Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{v + 1}).rightDerivedFunctorPlusUnith.app
      ((lowerStar AddCommGrpCat.{v + 1} f).mapHomotopyCategoryPlus.obj J)) ∧
    IsIso ((Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{v + 1}).rightDerivedFunctorPlusUnith.app
      J) := by
  have := (upperStarLowerStarAdjunction AddCommGrpCat.{v + 1} f).preservesKInjectiveComplexes
  have : CochainComplex.IsKInjective
      ((lowerStar AddCommGrpCat.{v + 1} f).mapHomotopyCategoryPlus.obj J).obj.as :=
    Functor.PreservesKInjectiveComplexes.isKInjective_map J.obj.as
  exact ⟨isIso_unit_of_kInjective _ J, isIso_unit_of_kInjective _ _,
    isIso_unit_of_kInjective _ J⟩


/-- Pullback of derived global sections is Γ of the derived unit followed by the natural
Leray identification, for every bounded below derived object (including a sheaf in degree 0).
Source: Stacks Project, Lemma 01F8 and equations 01F9 and 01FA
(blueprint: lem-weil-pbc-cohomology-pullback-derived-unit).
Proof: compare the two natural transformations out of derived global sections using
`Functor.rightDerived_ext`. It suffices to precompose their components on the bounded
below homotopy category with the derived global-sections unit. The derived adjunction's
unit formula expresses its component as the localized underived unit, the direct-image
derived unit, and the inverse of the inverse-image factorization isomorphism. Move this
last isomorphism through the Leray comparison by naturality, then move the localized
underived unit through the global-sections derived unit. The Leray unit compatibility
`Functor.rightDerivedFunctorPlusCompIso'_fac` identifies the resulting composite with
global sections of the underived unit followed by the sectionwise identification.
After passing through the faithful inclusion of bounded below homotopy categories,
this final identity is the image under the quotient functor of an equality of maps of
complexes, which is definitionally true. Thus the universal property gives equality of
the natural transformations and hence of their components at every derived object. -/
theorem derivedCohomologyPullback_eq_derivedUnit {X Y : Scheme.{v}} (f : Y ⟶ X)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{v + 1})) :
    (Functor.rightDerivedDesc _
      (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{v + 1}).rightDerivedFunctorPlusUnith
      (HomotopyCategory.Plus.quasiIso _)
      ((upperStar AddCommGrpCat.{v + 1} f).mapDerivedCategoryPlus ⋙
        (Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{v + 1}).rightDerivedFunctorPlus)
      (Functor.whiskerRight
          (NatTrans.mapHomotopyCategoryPlus
            ((Functor.leftUnitor _).inv ≫
              Functor.whiskerRight (upperStarLowerStarAdjunction AddCommGrpCat.{v + 1} f).unit
                (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{v + 1}) ≫
              (Functor.associator _ _ _).hom ≫
              Functor.whiskerLeft (upperStar AddCommGrpCat.{v + 1} f)
                (lowerStarCompGlobalSectionsIso AddCommGrpCat.{v + 1} f).hom))
          DerivedCategory.Plus.Qh ≫
        Functor.whiskerRight
          (Functor.mapHomotopyCategoryPlusCompIso
            (Iso.refl (upperStar AddCommGrpCat.{v + 1} f ⋙
              Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{v + 1}))).inv
          DerivedCategory.Plus.Qh ≫
        (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft (upperStar AddCommGrpCat.{v + 1} f).mapHomotopyCategoryPlus
          (Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{v + 1}).rightDerivedFunctorPlusUnith ≫
        (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight
          (upperStar AddCommGrpCat.{v + 1} f).mapDerivedCategoryPlusFactorsh.inv
          (Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{v + 1}).rightDerivedFunctorPlus ≫
        (Functor.associator _ _ _).hom)).app K =
      (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{v + 1}).rightDerivedFunctorPlus.map
        ((upperStarLowerStarAdjunction AddCommGrpCat.{v + 1} f).derivedPlus.unit.app K) ≫
      (@Functor.rightDerivedFunctorPlusCompIso' _ _ _ _ _ _ _ _ _ _ _ _ _ _
        (lowerStar AddCommGrpCat.{v + 1} f)
        (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{v + 1}) _ _ _ _
        (Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
          (upperStarLowerStarAdjunction AddCommGrpCat.{v + 1} f))
        (lowerStarCompGlobalSectionsIso AddCommGrpCat.{v + 1} f)).hom.app
          ((upperStar AddCommGrpCat.{v + 1} f).mapDerivedCategoryPlus.obj K) := by
  let L := upperStar AddCommGrpCat.{v + 1} f
  let R := lowerStar AddCommGrpCat.{v + 1} f
  let G := Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{v + 1}
  let H := Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{v + 1}
  let adj := upperStarLowerStarAdjunction AddCommGrpCat.{v + 1} f
  have : R.PreservesInjectiveObjects :=
    Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms adj
  let e := lowerStarCompGlobalSectionsIso AddCommGrpCat.{v + 1} f
  let β := Functor.whiskerRight
      (NatTrans.mapHomotopyCategoryPlus
        ((Functor.leftUnitor G).inv ≫ Functor.whiskerRight adj.unit G ≫
          (Functor.associator L R G).hom ≫ Functor.whiskerLeft L e.hom))
      DerivedCategory.Plus.Qh ≫
    Functor.whiskerRight
      (Functor.mapHomotopyCategoryPlusCompIso (Iso.refl (L ⋙ H))).inv
      DerivedCategory.Plus.Qh ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft L.mapHomotopyCategoryPlus H.rightDerivedFunctorPlusUnith ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight L.mapDerivedCategoryPlusFactorsh.inv H.rightDerivedFunctorPlus ≫
    (Functor.associator _ _ _).hom
  let γ := (Functor.leftUnitor G.rightDerivedFunctorPlus).inv ≫
    Functor.whiskerRight adj.derivedPlus.unit G.rightDerivedFunctorPlus ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft L.mapDerivedCategoryPlus
      (Functor.rightDerivedFunctorPlusCompIso' R G e).hom
  suffices h : Functor.rightDerivedDesc _ G.rightDerivedFunctorPlusUnith
      (HomotopyCategory.Plus.quasiIso _) _ β = γ by
    simpa only [γ, NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app, Functor.associator_hom_app,
      Functor.leftUnitor_inv_app, Category.id_comp, Category.assoc] using
      NatTrans.congr_app h K
  apply Functor.rightDerived_ext _ G.rightDerivedFunctorPlusUnith
    (HomotopyCategory.Plus.quasiIso _)
  rw [Functor.rightDerived_fac]
  ext M : 2
  simp only [β, γ, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.leftUnitor_inv_app, Category.id_comp, Category.comp_id]
  -- Compute the derived unit before using naturality of the Leray comparison.
  have hu : adj.derivedPlus.unit.app (DerivedCategory.Plus.Qh.obj M) =
      DerivedCategory.Plus.Qh.map (adj.mapHomotopyCategoryPlus.unit.app M) ≫
        R.rightDerivedFunctorPlusUnith.app (L.mapHomotopyCategoryPlus.obj M) ≫
        R.rightDerivedFunctorPlus.map (L.mapDerivedCategoryPlusFactorsh.inv.app M) := by
    rw [← Category.assoc, ← adj.derivedPlus_unit_app_fac, Category.assoc,
      ← Functor.map_comp]
    simp
  rw [hu, Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc]
  have hn := (Functor.rightDerivedFunctorPlusCompIso' R G e).hom.naturality
    (L.mapDerivedCategoryPlusFactorsh.inv.app M)
  simp only [Functor.comp_map] at hn
  dsimp only [Functor.comp_obj] at hn
  rw [hn]
  have hG := G.rightDerivedFunctorPlusUnith.naturality
    (adj.mapHomotopyCategoryPlus.unit.app M)
  simp only [Functor.comp_map] at hG
  rw [← reassoc_of% hG]
  rw [← Functor.rightDerivedFunctorPlusCompUnit_app_assoc]
  have hc := NatTrans.congr_app (Functor.rightDerivedFunctorPlusCompIso'_fac R G e)
    (L.mapHomotopyCategoryPlus.obj M)
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app] at hc
  rw [reassoc_of% hc]
  rw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc]
  congr 2
  apply (HomotopyCategory.Plus.ι _).map_injective
  obtain ⟨M, hM⟩ := M
  obtain ⟨A, rfl⟩ := HomotopyCategory.quotient_obj_surjective M
  simp only [Functor.map_comp, NatTrans.ι_map_mapHomotopyCategoryPlus_app,
    Functor.mapHomotopyCategoryPlusCompIso_refl_inv_app]
  rw [(HomotopyCategory.Plus.ι _).map_id, Category.comp_id]
  change _ = (G.mapHomotopyCategory _).map
      ((HomotopyCategory.Plus.ι _).map
        (adj.mapHomotopyCategoryPlus.unit.app ⟨_, hM⟩)) ≫ _
  rw [Adjunction.ι_map_mapHomotopyCategoryPlus_unit_app]
  change (HomotopyCategory.quotient _ _).map
      ((NatTrans.mapHomologicalComplex
        (G.leftUnitor.inv ≫ Functor.whiskerRight adj.unit G ≫
          (Functor.associator L R G).hom ≫ Functor.whiskerLeft L e.hom) _).app A) ≫
        𝟙 _ =
      (G.mapHomotopyCategory _).map
        ((adj.mapHomotopyCategory _).unit.app ((HomotopyCategory.quotient _ _).obj A)) ≫
      (HomotopyCategory.quotient _ _).map
        ((NatTrans.mapHomologicalComplex e.hom _).app
          ((L.mapHomologicalComplex _).obj A))
  rw [Category.comp_id, Adjunction.mapHomotopyCategory_unit_app_quotient,
    Functor.mapHomotopyCategory_map, ← Functor.map_comp]
  congr 1

end AlgebraicGeometry.Etale
