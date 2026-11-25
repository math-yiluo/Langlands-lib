/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.Etale.Derived.GlobalSections
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.CompConjugate

/-! # Composition of the unbounded Leray comparison -/

@[expose] public section

universe u' u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Etale

variable {A : Type u'} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]


private theorem lowerStarCompGlobalSectionsIso_comp_comp
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (P : Sheaf X.smallEtaleTopology A) :
    (Sheaf.Γ Z.smallEtaleTopology A).map
        ((lowerStarComp A f g (f ≫ g) rfl).hom.app P) ≫
      (lowerStarCompGlobalSectionsIso A (f ≫ g)).hom.app P =
    (lowerStarCompGlobalSectionsIso A g).hom.app
        (((f)_*[A]).obj P) ≫
      (lowerStarCompGlobalSectionsIso A f).hom.app P := by
  apply (cancel_mono ((Sheaf.ΓNatIsoSheafSections _ _ terminalIsTerminal).hom.app P)).1
  simp only [lowerStarCompGlobalSectionsIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Category.assoc,
    Iso.inv_hom_id_app, Iso.inv_hom_id_app_assoc, Category.comp_id]
  rw [reassoc_of% ((Sheaf.ΓNatIsoSheafSections Z.smallEtaleTopology
    A terminalIsTerminal).hom.naturality
    ((lowerStarComp A f g (f ≫ g) rfl).hom.app P))]
  simp only [lowerStarCompSheafSectionsTerminalIso, NatIso.ofComponents_hom_app,
    Functor.mapIso_hom, Iso.symm_hom, Iso.op_inv]
  congr 1
  change ((lowerStarComp A f g (f ≫ g) rfl).hom.app P).hom.app
    (Opposite.op (⊤_ Z.Etale)) ≫ P.obj.map (PreservesTerminal.iso (f ≫ g).Etale).inv.op = _
  simp only [lowerStarComp, Functor.sheafPushforwardContinuousComp'_hom_app_hom_app,
    Iso.symm_inv, lowerStar_obj_val_map, ← Functor.map_comp, ← op_comp]
  congr 2
  exact ((terminalIsTerminal.isTerminalObj g.Etale).isTerminalObj f.Etale).hom_ext _ _

private lemma derived_comp_eq {X Y Z : Scheme.{u}} (f : Y ⟶ X) (g : Z ⟶ Y) :
    (rightDerivedLowerStarComp A g f).hom =
      (Functor.rightDerivedFunctorCompIso'
        (lowerStar A g) (lowerStar A f)
        (lowerStarComp A g f)).hom := by
  rw [Adjunction.rightDerivedFunctorCompIso'_hom_eq_conjugateEquiv
    (upperStarLowerStarAdjunction A g)
    (upperStarLowerStarAdjunction A f)
    (upperStarLowerStarAdjunction A (g ≫ f))
    _ (upperStarComp A g f) (by
      exact (congrArg Iso.hom
        (conjugateIsoEquiv_upperStarComp A g f)).symm)]
  simp only [rightDerivedLowerStarComp, Iso.symm_hom, conjugateIsoEquiv_apply_inv,
    Iso.symm_inv]
  rfl

private lemma comp_fac
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    [CategoryTheory.Abelian.HasKInjectiveResolutions C]
    [CategoryTheory.Abelian.HasKInjectiveResolutions D]
    (F : C ⥤ D) (G : D ⥤ E) (H : C ⥤ E)
    [F.Additive] [G.Additive] [H.Additive] [F.PreservesKInjectiveComplexes]
    (e : F ⋙ G ≅ H) :
    Functor.rightDerivedFunctorCompUnit F G ≫
      Functor.whiskerLeft DerivedCategory.Qh (Functor.rightDerivedFunctorCompIso' F G e).hom =
    Functor.whiskerRight (NatTrans.mapHomotopyCategory e.hom (.up ℤ)) DerivedCategory.Qh ≫
      H.rightDerivedFunctorUnit := by
  have hc : (F ⋙ G).rightDerivedFunctorUnit ≫
      Functor.whiskerLeft DerivedCategory.Qh
        (Functor.rightDerivedFunctorCompIso F G).hom =
      Functor.rightDerivedFunctorCompUnit F G := by
    simp [Functor.rightDerivedFunctorCompIso]
  rw [← hc, Category.assoc, ← Functor.whiskerLeft_comp]
  simp only [Functor.rightDerivedFunctorCompIso', Iso.trans_hom, Iso.symm_hom]
  rw [Iso.hom_inv_id_assoc]
  exact Functor.rightDerivedNatTrans_fac _ _ _ _
    (HomotopyCategory.quasiIso C (.up ℤ)) _

private lemma comp_unit_app
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    [CategoryTheory.Abelian.HasKInjectiveResolutions C]
    [CategoryTheory.Abelian.HasKInjectiveResolutions D]
    (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive]
    (T : HomotopyCategory C (.up ℤ)) :
    (Functor.rightDerivedFunctorCompUnit F G).app T =
      G.rightDerivedFunctorUnit.app ((F.mapHomotopyCategory (.up ℤ)).obj T) ≫
        G.rightDerivedFunctor.map (F.rightDerivedFunctorUnit.app T) := by
  have hi : (Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ G)) (.up ℤ)).inv.app T =
      𝟙 _ := by
    have h := Iso.inv_hom_id_app
      (Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ G)) (.up ℤ)) T
    erw [Functor.mapHomotopyCategoryCompIso_refl_hom_app, Category.comp_id] at h
    exact h
  simp only [Functor.rightDerivedFunctorCompUnit, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.associator_hom_app,
    Functor.associator_inv_app, hi]
  erw [DerivedCategory.Qh.map_id]
  dsimp
  simp only [Category.id_comp, Category.comp_id]

-- Comparing iterated sheaf functors requires unfolding the derived-category interfaces.
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private lemma derived_leray_composition {X Y Z : Scheme.{u}} (f : Y ⟶ X) (g : Z ⟶ Y) :
    Functor.whiskerRight (rightDerivedLowerStarComp A g f).hom
        (rightDerivedGlobalSections A X) ≫
      (rightDerivedLowerStarCompRightDerivedGlobalSectionsIso
        A (g ≫ f)).hom =
    (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft (lowerStar A g).rightDerivedFunctor
        (rightDerivedLowerStarCompRightDerivedGlobalSectionsIso
          A f).hom ≫
      (rightDerivedLowerStarCompRightDerivedGlobalSectionsIso
        A g).hom := by
  let F := lowerStar A g
  let G := lowerStar A f
  let H := Sheaf.Γ X.smallEtaleTopology A
  let K := lowerStar A (g ≫ f)
  let J := Sheaf.Γ Y.smallEtaleTopology A
  let L := Sheaf.Γ Z.smallEtaleTopology A
  let e := lowerStarComp A g f
  let a := lowerStarCompGlobalSectionsIso A f
  let b := lowerStarCompGlobalSectionsIso A g
  let c := lowerStarCompGlobalSectionsIso A (g ≫ f)
  let d := Functor.rightDerivedFunctorCompIso' F G e
  have : (F ⋙ G).PreservesKInjectiveComplexes := ⟨fun T _ => by
    change CochainComplex.IsKInjective
      ((G.mapHomologicalComplex (.up ℤ)).obj ((F.mapHomologicalComplex (.up ℤ)).obj T))
    infer_instance⟩
  let i := Functor.isoWhiskerRight (Functor.rightDerivedFunctorCompIso F G)
    H.rightDerivedFunctor
  let α := Functor.rightDerivedFunctorCompUnit (F ⋙ G) H ≫
    Functor.whiskerLeft DerivedCategory.Qh i.hom
  have : ((F.rightDerivedFunctor ⋙ G.rightDerivedFunctor) ⋙ H.rightDerivedFunctor
      ).IsRightDerivedFunctor α (HomotopyCategory.quasiIso _ (.up ℤ)) :=
    (Functor.isRightDerivedFunctor_iff_of_iso
      (Functor.rightDerivedFunctorCompUnit (F ⋙ G) H) α
      (HomotopyCategory.quasiIso _ (.up ℤ)) i rfl).mp inferInstance
  rw [derived_comp_eq (A := A)]
  refine Functor.rightDerived_ext _ α (HomotopyCategory.quasiIso _ (.up ℤ)) _ _ _ ?_
  ext T : 2
  have hα : α.app T =
      H.rightDerivedFunctorUnit.app
          ((G.mapHomotopyCategory (.up ℤ)).obj ((F.mapHomotopyCategory (.up ℤ)).obj T)) ≫
        H.rightDerivedFunctor.map ((Functor.rightDerivedFunctorCompUnit F G).app T) := by
    dsimp only [α, i, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.isoWhiskerRight_hom, Functor.whiskerRight_app]
    rw [comp_unit_app]
    erw [Category.assoc, ← Functor.map_comp]
    congr 2
    simp [Functor.rightDerivedFunctorCompIso]
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, hα, Category.assoc]
  dsimp only [Functor.comp_obj]
  erw [Category.id_comp]
  have hfg := NatTrans.congr_app (comp_fac F G K e) T
  have hc := NatTrans.congr_app (comp_fac K H L c) T
  have ha := NatTrans.congr_app (comp_fac G H J a)
    ((F.mapHomotopyCategory (.up ℤ)).obj T)
  have hb := NatTrans.congr_app (comp_fac F J L b) T
  dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app] at hfg hc ha hb
  rw [comp_unit_app] at hc ha hb
  have hn := H.rightDerivedFunctorUnit.naturality
    ((NatTrans.mapHomotopyCategory e.hom (.up ℤ)).app T)
  have hna := (Functor.rightDerivedFunctorCompIso' G H a).hom.naturality
    (F.rightDerivedFunctorUnit.app T)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hn hna
  change H.rightDerivedFunctorUnit.app _ ≫
      H.rightDerivedFunctor.map ((Functor.rightDerivedFunctorCompUnit F G).app T) ≫
      H.rightDerivedFunctor.map (d.hom.app (DerivedCategory.Qh.obj T)) ≫
      (Functor.rightDerivedFunctorCompIso' K H c).hom.app (DerivedCategory.Qh.obj T) =
    H.rightDerivedFunctorUnit.app _ ≫
      H.rightDerivedFunctor.map ((Functor.rightDerivedFunctorCompUnit F G).app T) ≫
      (Functor.rightDerivedFunctorCompIso' G H a).hom.app
        (F.rightDerivedFunctor.obj (DerivedCategory.Qh.obj T)) ≫
      (Functor.rightDerivedFunctorCompIso' F J b).hom.app (DerivedCategory.Qh.obj T)
  rw [← Functor.map_comp_assoc, hfg, Functor.map_comp]
  simp only [Category.assoc] at hc ha hb ⊢
  erw [← reassoc_of% hn]
  erw [hc]
  rw [comp_unit_app, Functor.map_comp, Category.assoc]
  erw [reassoc_of% hna, reassoc_of% ha, hb]
  rw [← DerivedCategory.Qh.map_comp_assoc, ← DerivedCategory.Qh.map_comp_assoc]
  congr 2
  obtain ⟨T, rfl⟩ := HomotopyCategory.quotient_obj_surjective T
  have ht : (H.mapHomologicalComplex (.up ℤ)).map
        ((NatTrans.mapHomologicalComplex e.hom (.up ℤ)).app T) ≫
      (NatTrans.mapHomologicalComplex c.hom (.up ℤ)).app T =
    (NatTrans.mapHomologicalComplex a.hom (.up ℤ)).app
        ((F.mapHomologicalComplex (.up ℤ)).obj T) ≫
      (NatTrans.mapHomologicalComplex b.hom (.up ℤ)).app T := by
    ext n : 1
    exact lowerStarCompGlobalSectionsIso_comp_comp g f (T.X n)
  have hq := (HomotopyCategory.quotient A (.up ℤ)).congr_map ht
  simpa only [NatTrans.mapHomotopyCategory_app, Functor.mapHomotopyCategory_obj,
    Functor.mapHomotopyCategory_map, HomotopyCategory.quotient_obj_as,
    Functor.map_comp] using hq

/-- The canonical Leray comparisons associate with the derived direct-image comparison.
Source: Stacks Project, Tags 05T2, 015M and 03CB.
(blueprint: lem-weil-pbc-derived-leray-composition).

Proof: The underived direct-image comparison and terminal-section comparisons associate.
Both composites evaluate a sheaf on the same composite base change of the terminal object;
the two base-change isomorphisms coincide by the uniqueness of the pullback isomorphism
commuting with the projections. Apply the right-derived comparison construction to this
equality. The composition comparison for direct images agrees with the mate defining
rightDerivedLowerStarComp: the underived comparison is the mate of upperStarComp, and the
right-derived comparison preserves this conjugacy for exact left adjoints. Each direct
image preserves K-injective complexes, being right adjoint to exact inverse image. Thus
iterated direct image followed by global sections computes the composite right-derived
functor. Precomposing either displayed transformation with its composite derived unit gives
the localization of the same underived terminal-section comparison. The universal property
of this composite right-derived functor identifies the transformations; evaluate at M.
This works on the unbounded category, using K-injectives, with no boundedness hypothesis. -/
theorem derivedLeray_comp {X Y Z : Scheme.{u}} (f : Y ⟶ X) (g : Z ⟶ Y)
    (M : DerivedCategory (Sheaf Z.smallEtaleTopology A)) :
    (rightDerivedGlobalSections A X).map
      ((rightDerivedLowerStarComp A g f).hom.app M) ≫
      (rightDerivedLowerStarCompRightDerivedGlobalSectionsIso
        A (g ≫ f)).hom.app M =
    (rightDerivedLowerStarCompRightDerivedGlobalSectionsIso
      A f).hom.app
        ((lowerStar A g).rightDerivedFunctor.obj M) ≫
      (rightDerivedLowerStarCompRightDerivedGlobalSectionsIso
        A g).hom.app M := by
  simpa only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Category.id_comp] using
      NatTrans.congr_app (derived_leray_composition (A := A) f g) M

end AlgebraicGeometry.Etale
