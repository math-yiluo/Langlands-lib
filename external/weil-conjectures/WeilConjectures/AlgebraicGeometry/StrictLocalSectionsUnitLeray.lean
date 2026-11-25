/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.StrictHenselizationRestriction

/-! # Derived sections unit followed by Leray on a representative

Source: Stacks Project, Tag 03Q9, final injective-complex paragraph.
(blueprint: lem-weil-pbc-strict-local-sections-unit-leray).
-/

@[expose] public section

universe v

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

namespace AlgebraicGeometry.Etale

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
private theorem sections_exact_bridge {S : Scheme.{v}}
    {Ω : Type v} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S) :
    let G := Sheaf.Γ (Scheme.strictLocalization s).smallEtaleTopology
      AddCommGrpCat.{v + 1}
    have := strictHenselization_globalSections_preservesFiniteColimits s
    G.rightDerivedFunctorPlusCompatibility.hom =
      Functor.whiskerRight G.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus.hom
        DerivedCategory.Plus.ι ≫
      Functor.whiskerLeft DerivedCategory.Plus.ι
        G.rightDerivedFunctorIsoMapDerivedCategory.inv := by
  dsimp only
  have := strictHenselization_globalSections_preservesFiniteColimits s
  let G := Sheaf.Γ (Scheme.strictLocalization s).smallEtaleTopology
    AddCommGrpCat.{v + 1}
  apply Functor.rightDerived_ext _ G.rightDerivedFunctorPlusιUnit
    (HomotopyCategory.Plus.quasiIso _) _
  ext N
  dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
  have hc := NatTrans.congr_app
    (Functor.rightDerivedNatTrans_fac _ _ G.rightDerivedFunctorPlusιUnit
      G.ιRightDerivedFunctorUnit (HomotopyCategory.Plus.quasiIso _) (𝟙 _)) N
  have hp := NatTrans.congr_app G.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus_hom_fac N
  dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app] at hp
  trans G.rightDerivedFunctorUnit.app N.obj
  · with_unfolding_all
      simpa only [Functor.rightDerivedFunctorPlusCompatibility, Functor.rightDerivedUnique,
      Functor.rightDerivedNatIso_hom, NatTrans.comp_app, Functor.whiskerLeft_app,
      NatTrans.id_app, Category.id_comp, Iso.refl_hom,
      Functor.ιRightDerivedFunctorUnit, Functor.whiskerLeft_app, G,
      HomotopyCategory.Plus.ι, ObjectProperty.ι_obj] using hc
  · change G.rightDerivedFunctorUnit.app N.obj =
      DerivedCategory.Plus.ι.map (G.rightDerivedFunctorPlusUnith.app N) ≫
        DerivedCategory.Plus.ι.map
          (G.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus.hom.app
            (DerivedCategory.Plus.Qh.obj N)) ≫
        G.rightDerivedFunctorIsoMapDerivedCategory.inv.app (DerivedCategory.Qh.obj N.obj)
    rw [← DerivedCategory.Plus.ι.map_comp_assoc, hp]
    have hi : DerivedCategory.Plus.ι.map (G.mapDerivedCategoryPlusFactorsh.inv.app N) =
        G.mapDerivedCategoryFactorsh.inv.app N.obj := by
      apply (cancel_mono (G.mapDerivedCategoryFactorsh.hom.app N.obj)).mp
      erw [← G.ι_map_mapDerivedCategoryPlusFactorsh_hom_app N,
        ← DerivedCategory.Plus.ι.map_comp, Iso.inv_hom_id_app,
        DerivedCategory.Plus.ι.map_id]
      erw [G.ι_map_mapDerivedCategoryPlusFactorsh_hom_app N, Iso.inv_hom_id_app]
      rfl
    rw [hi]
    have hu := NatTrans.congr_app G.rightDerivedFunctorIsoMapDerivedCategory_hom_fac N.obj
    dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app] at hu
    erw [← hu, Category.assoc, Iso.hom_inv_id_app, Category.comp_id]


private lemma leray_unit_fac {X Y : Scheme.{v}} (t : Y ⟶ X) :
    Functor.rightDerivedFunctorCompUnit
        (lowerStar AddCommGrpCat.{v + 1} t)
        (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{v + 1}) ≫
      Functor.whiskerLeft DerivedCategory.Qh
        (rightDerivedLowerStarCompRightDerivedGlobalSectionsIso
          AddCommGrpCat.{v + 1} t).hom =
    Functor.whiskerRight
        (NatTrans.mapHomotopyCategory
          (lowerStarCompGlobalSectionsIso AddCommGrpCat.{v + 1} t).hom (.up ℤ))
        DerivedCategory.Qh ≫
      (Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{v + 1}).rightDerivedFunctorUnit := by
  let F := lowerStar AddCommGrpCat.{v + 1} t
  let G := Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{v + 1}
  have hc : (F ⋙ G).rightDerivedFunctorUnit ≫
      Functor.whiskerLeft DerivedCategory.Qh
        (Functor.rightDerivedFunctorCompIso F G).hom =
      Functor.rightDerivedFunctorCompUnit F G := by
    simp [Functor.rightDerivedFunctorCompIso]
  rw [← hc, Category.assoc, ← Functor.whiskerLeft_comp]
  simp only [rightDerivedLowerStarCompRightDerivedGlobalSectionsIso,
    Functor.rightDerivedFunctorCompIso', Iso.trans_hom, Iso.symm_hom]
  dsimp only [F, G]
  rw [Iso.hom_inv_id_assoc]
  exact Functor.rightDerivedNatTrans_fac _ _ _ _
    (HomotopyCategory.quasiIso (Sheaf Y.smallEtaleTopology AddCommGrpCat.{v + 1}) (.up ℤ)) _

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private lemma sections_unit_on_complex {S : Scheme.{v}}
    {Ω : Type v} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
    (E : CochainComplex
      (Sheaf (Scheme.strictLocalization s).smallEtaleTopology AddCommGrpCat.{v + 1})
      ℤ) :
    let G := Sheaf.Γ (Scheme.strictLocalization s).smallEtaleTopology
      AddCommGrpCat.{v + 1}
    have := strictHenselization_globalSections_preservesFiniteColimits s
    G.mapDerivedCategoryFactors.inv.app E ≫
      G.mapDerivedCategory.map ((DerivedCategory.quotientCompQhIso _).inv.app E) ≫
      G.rightDerivedFunctorIsoMapDerivedCategory.inv.app
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj E)) =
    (DerivedCategory.quotientCompQhIso _).inv.app
        ((G.mapHomologicalComplex (.up ℤ)).obj E) ≫
      G.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient _ _).obj E) := by
  dsimp only
  have := strictHenselization_globalSections_preservesFiniteColimits s
  let G := Sheaf.Γ (Scheme.strictLocalization s).smallEtaleTopology
    AddCommGrpCat.{v + 1}
  let N := (HomotopyCategory.quotient _ _).obj E
  have hu := NatTrans.congr_app G.rightDerivedFunctorIsoMapDerivedCategory_hom_fac N
  dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app] at hu
  have hh := G.mapDerivedCategoryFactorsh_hom_app E
  have hid : (G.mapHomotopyCategoryFactors (.up ℤ)).inv.app E = 𝟙 _ := by rfl
  erw [hid, DerivedCategory.Qh.map_id, Category.comp_id] at hh
  apply (cancel_mono (G.rightDerivedFunctorIsoMapDerivedCategory.hom.app
    (DerivedCategory.Qh.obj N))).mp
  erw [Category.assoc, Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  erw [Category.assoc, hu]
  apply (cancel_mono (G.mapDerivedCategoryFactorsh.hom.app N)).mp
  erw [Category.assoc, Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  erw [hh]
  erw [← G.mapDerivedCategory.map_comp_assoc,
    Iso.inv_hom_id_app, G.mapDerivedCategory.map_id, Category.id_comp,
    Iso.inv_hom_id_app_assoc]

-- The long naturality calculation elaborates several composed derived functors.
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The direct-image unit followed by Leray is the derived sections unit.

Source: Stacks Project, Tag 03Q9, final injective-complex paragraph, and the
unit factorization defining `Functor.rightDerivedFunctorCompIso`.
(blueprint: lem-weil-pbc-strict-local-sections-unit-leray).

Proof: expand the exact sections comparison and the bounded-below/unbounded
right-derived compatibility. Their defining unit compatibilities identify their
composite with the inverse exact-to-right-derived sections comparison.
Naturality moves the map from Q(D) to T through the Leray isomorphism. Expand
Leray as the inverse derived composition isomorphism followed by the derived
underived sections isomorphism. The composition unit factorization now gives
the sections unit at D preceded by the localized underived sections isomorphism.
Naturality of the sections unit and quotient/localization isomorphisms accounts
for the displayed transport r. This calculation never inverts the direct-image
unit or the sections unit at D; it holds for zero and nonacyclic complexes. -/
theorem strictLocalSections_unit_leray {S : Scheme.{v}}
    {Ω : Type v} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
    {Y : Scheme.{v}} (t : Y ⟶ Scheme.strictLocalization s)
    (D : CochainComplex (Sheaf Y.smallEtaleTopology AddCommGrpCat.{v + 1}) ℤ)
    (T : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology AddCommGrpCat.{v + 1}))
    (r : DerivedCategory.Q.obj D ⟶ T.obj) :
    let F := lowerStar AddCommGrpCat.{v + 1} t
    let G := Sheaf.Γ (Scheme.strictLocalization s).smallEtaleTopology
      AddCommGrpCat.{v + 1}
    let H := Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{v + 1}
    have := strictHenselization_globalSections_preservesFiniteColimits s
    let V := F.rightDerivedFunctorPlus.obj T
    let ℓ := DerivedCategory.Plus.ι.map
        (G.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus.inv.app V) ≫
      G.rightDerivedFunctorPlusCompatibility.hom.app V ≫
      G.rightDerivedFunctor.map (F.rightDerivedFunctorPlusCompatibility.hom.app T) ≫
      (rightDerivedLowerStarCompRightDerivedGlobalSectionsIso AddCommGrpCat.{v + 1}
        t).hom.app T.obj
    G.mapDerivedCategoryFactors.inv.app ((F.mapHomologicalComplex (.up ℤ)).obj D) ≫
      G.mapDerivedCategory.map ((DerivedCategory.quotientCompQhIso _).inv.app
        ((F.mapHomologicalComplex (.up ℤ)).obj D)) ≫
      G.mapDerivedCategory.map
        (F.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient _ _).obj D)) ≫
      G.mapDerivedCategory.map
        (F.rightDerivedFunctor.map ((DerivedCategory.quotientCompQhIso _).hom.app D)) ≫
      G.mapDerivedCategory.map (F.rightDerivedFunctor.map r) ≫
      G.mapDerivedCategory.map (F.rightDerivedFunctorPlusCompatibility.inv.app T) ≫ ℓ =
    DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
      (lowerStarCompGlobalSectionsIso AddCommGrpCat.{v + 1} t).hom (.up ℤ)).app D) ≫
      (DerivedCategory.quotientCompQhIso AddCommGrpCat.{v + 1}).inv.app
        ((H.mapHomologicalComplex (.up ℤ)).obj D) ≫
      H.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient _ _).obj D) ≫
      H.rightDerivedFunctor.map ((DerivedCategory.quotientCompQhIso _).hom.app D) ≫
      H.rightDerivedFunctor.map r  := by
  dsimp only
  have := strictHenselization_globalSections_preservesFiniteColimits s
  let F := lowerStar AddCommGrpCat.{v + 1} t
  let G := Sheaf.Γ (Scheme.strictLocalization s).smallEtaleTopology
    AddCommGrpCat.{v + 1}
  let H := Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{v + 1}
  let V := F.rightDerivedFunctorPlus.obj T
  let N := (HomotopyCategory.quotient _ _).obj D
  let E := (F.mapHomologicalComplex (.up ℤ)).obj D
  have hb := NatTrans.congr_app (sections_exact_bridge s) V
  dsimp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app] at hb
  erw [hb, Category.assoc, ← DerivedCategory.Plus.ι.map_comp_assoc, Iso.inv_hom_id_app,
    DerivedCategory.Plus.ι.map_id, Category.id_comp]
  have hn := G.rightDerivedFunctorIsoMapDerivedCategory.inv.naturality
    (F.rightDerivedFunctorPlusCompatibility.inv.app T)
  erw [reassoc_of% hn]
  erw [← G.rightDerivedFunctor.map_comp_assoc, Iso.inv_hom_id_app,
    G.rightDerivedFunctor.map_id, Category.id_comp]
  have h₁ := G.rightDerivedFunctorIsoMapDerivedCategory.inv.naturality
    (F.rightDerivedFunctor.map r)
  have h₂ := G.rightDerivedFunctorIsoMapDerivedCategory.inv.naturality
    (F.rightDerivedFunctor.map ((DerivedCategory.quotientCompQhIso _).hom.app D))
  have h₃ := G.rightDerivedFunctorIsoMapDerivedCategory.inv.naturality
    (F.rightDerivedFunctorUnit.app N)
  erw [reassoc_of% h₁, reassoc_of% h₂, reassoc_of% h₃]
  have hs := sections_unit_on_complex s E
  dsimp only at hs
  erw [reassoc_of% hs]
  have hl := (rightDerivedLowerStarCompRightDerivedGlobalSectionsIso
    AddCommGrpCat.{v + 1} t).hom.naturality
      ((DerivedCategory.quotientCompQhIso _).hom.app D ≫ r)
  dsimp only [Functor.comp_map] at hl
  simp only [Functor.map_comp, Category.assoc] at hl
  have hl' := congrArg
    (fun z ↦ (DerivedCategory.quotientCompQhIso _).inv.app
        ((G.mapHomologicalComplex (.up ℤ)).obj E) ≫
      G.rightDerivedFunctorUnit.app ((F.mapHomotopyCategory (.up ℤ)).obj N) ≫
      G.rightDerivedFunctor.map (F.rightDerivedFunctorUnit.app N) ≫ z) hl
  refine hl'.trans ?_
  have hc := NatTrans.congr_app (leray_unit_fac t) N
  dsimp only [Functor.rightDerivedFunctorCompUnit, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.associator_inv_app] at hc
  have hi : (Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ G)) (.up ℤ)).inv.app N =
      𝟙 _ := by
    have h := Iso.inv_hom_id_app
      (Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ G)) (.up ℤ)) N
    erw [Functor.mapHomotopyCategoryCompIso_refl_hom_app, Category.comp_id] at h
    exact h
  simp only [Category.id_comp, Category.comp_id, Category.assoc] at hc
  change DerivedCategory.Qh.map
      ((Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ G)) (.up ℤ)).inv.app N) ≫
      G.rightDerivedFunctorUnit.app ((F.mapHomotopyCategory (.up ℤ)).obj N) ≫
      G.rightDerivedFunctor.map (F.rightDerivedFunctorUnit.app N) ≫
      (rightDerivedLowerStarCompRightDerivedGlobalSectionsIso
        AddCommGrpCat.{v + 1} t).hom.app (DerivedCategory.Qh.obj N) = _ at hc
  erw [hi, DerivedCategory.Qh.map_id, Category.id_comp] at hc
  erw [reassoc_of% hc]
  have he : (DerivedCategory.quotientCompQhIso _).inv.app
      ((G.mapHomologicalComplex (.up ℤ)).obj E) ≫
        DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory
          (lowerStarCompGlobalSectionsIso AddCommGrpCat.{v + 1} t).hom (.up ℤ)).app N) =
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
        (lowerStarCompGlobalSectionsIso AddCommGrpCat.{v + 1} t).hom (.up ℤ)).app D) ≫
        (DerivedCategory.quotientCompQhIso _).inv.app
          ((H.mapHomologicalComplex (.up ℤ)).obj D) := by
    exact ((DerivedCategory.quotientCompQhIso AddCommGrpCat.{v + 1}).inv.naturality
      ((NatTrans.mapHomologicalComplex
        (lowerStarCompGlobalSectionsIso AddCommGrpCat.{v + 1} t).hom (.up ℤ)).app D)).symm
  erw [reassoc_of% he]
  rfl


end AlgebraicGeometry.Etale
