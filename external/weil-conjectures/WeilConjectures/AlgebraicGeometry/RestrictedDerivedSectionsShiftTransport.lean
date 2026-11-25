/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module



public import WeilConjectures.AlgebraicGeometry.RawRestrictedCohomologyComparisonMap
public import WeilConjectures.AlgebraicGeometry.RestrictedDerivedSectionZeroComparison
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.AdjunctionShift
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.Shift.ExactFunctor
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs



/-! # Transport of restricted section pullback through the shift comparison

Source: Stacks Project, Tags 07A6 and 0D6F.
(blueprint: lem-sbc-restricted-derived-sections-shift-transport).
-/

@[expose] public section

universe v
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale.RawRestrictedComparison

attribute [local instance] etaleComposition etaleIdentities etalePullbacks
  etaleBaseChange sheafifyInstance weakSheafifyInstance

private theorem restriction_commShift {S Y Y' : Scheme.{v}}
    (a : Y' ⟶ Y) (h : Y ⟶ S) (h' : Y' ⟶ S) (w : a ≫ h = h') (U : S.Etale) :
    NatTrans.CommShift (derivedRestrictionIso a h h' w U).hom ℤ := by
  dsimp only [derivedRestrictionIso, Iso.trans_hom, Iso.symm_hom]
  have : NatTrans.CommShift
      (Functor.mapDerivedCategoryCompIso
        (upperStar AddCommGrpCat.{v + 1} a)
        (upperStar AddCommGrpCat.{v + 1} (Limits.pullback.snd U.hom h'))).inv ℤ :=
    NatTrans.CommShift.of_iso_inv _ ℤ
  infer_instance

set_option backward.isDefEq.respectTransparency false in
private theorem canonical_unit_commShift
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasKInjectiveResolutions C]
    (F : C ⥤ D) [F.Additive] : NatTrans.CommShift F.rightDerivedFunctorUnit ℤ := by
  let inj := ObjectProperty.ι (HomotopyCategory.subcategoryAcyclic C).rightOrthogonal
  let E := HomotopyCategory.KInjectives.equivalence C
  let G := inj ⋙ F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh
  have hI : NatTrans.CommShift F.rightDerivedFunctorIsoKInjectives.inv ℤ :=
    Functor.CommShift.ofIso_compatibility F.rightDerivedFunctorIsoKInjectives.symm ℤ
  have hinv (Y : DerivedCategory C) :
      F.rightDerivedFunctorIsoKInjectives.inv.app Y =
        F.rightDerivedFunctorUnit.app (inj.obj (E.inverse.obj Y)) ≫
          F.rightDerivedFunctor.map (E.counit.app Y) := by
    simp [Functor.rightDerivedFunctorIsoKInjectives, inj, E]
  have heq : Functor.whiskerLeft inj F.rightDerivedFunctorUnit =
      (Functor.leftUnitor G).inv ≫ Functor.whiskerRight E.unitIso.hom G ≫
        (Functor.associator E.functor E.inverse G).hom ≫
        Functor.whiskerLeft E.functor F.rightDerivedFunctorIsoKInjectives.inv ≫
        (Functor.associator inj DerivedCategory.Qh F.rightDerivedFunctor).hom := by
    ext X
    have hn := F.rightDerivedFunctorUnit.naturality (inj.map (E.unit.app X))
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.associator_hom_app, Functor.leftUnitor_inv_app, hinv]
    dsimp only [G, E, inj] at hn ⊢
    simp only [Category.id_comp, Category.assoc]
    rw [← Category.assoc]
    erw [hn]
    erw [Category.comp_id]
    simp only [Functor.comp_map, Category.assoc]
    change _ = _ ≫ F.rightDerivedFunctor.map (E.functor.map (E.unit.app X)) ≫
      F.rightDerivedFunctor.map (E.counit.app (E.functor.obj X))
    rw [← Functor.map_comp]
    erw [E.functor_unit_comp, CategoryTheory.Functor.map_id, Category.comp_id]
    rfl
  have : NatTrans.CommShift (Functor.whiskerLeft inj F.rightDerivedFunctorUnit) ℤ := by
    rw [heq]
    dsimp only [G, E, inj]
    infer_instance
  refine NatTrans.CommShift.of_whiskerLeft _ inj (fun K ↦ ?_)
  let J := E.inverse.obj (DerivedCategory.Qh.obj K)
  obtain ⟨f, hf⟩ := (J.property.map_bijective_of_isTriangulated DerivedCategory.Qh
    K).surjective
      (E.counitIso.inv.app (DerivedCategory.Qh.obj K))
  refine ⟨J, f, ?_⟩
  rw [Functor.comp_map, hf]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
private theorem canonical_adjunction_unit_commShift
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasKInjectiveResolutions D]
    {L : C ⥤ D} {R : D ⥤ C} [L.Additive] [R.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L] (adj : L ⊣ R) :
    NatTrans.CommShift adj.mapDerivedCategoryRightDerivedAdjunction.unit ℤ := by
  have : NatTrans.CommShift R.rightDerivedFunctorUnit ℤ := canonical_unit_commShift R
  have hunit : NatTrans.CommShift (adj.mapHomologicalComplex (.up ℤ)).unit ℤ := by
    constructor
    intro n
    ext K i
    dsimp [Adjunction.mapHomologicalComplex]
    simp only [Functor.commShiftIso_comp_hom_app, Functor.commShiftIso_id_hom_app,
      HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
      Functor.mapHomologicalComplex_commShiftIso_hom_app_f]
    simp only [HomologicalComplex.id_f, CochainComplex.shiftFunctor_obj_X', Category.id_comp,
      Functor.comp_obj, CategoryTheory.Functor.map_id, Category.comp_id]
    erw [Category.comp_id]
  have : NatTrans.CommShift (adj.mapHomotopyCategory (.up ℤ)).unit ℤ := by
    have heq : Functor.whiskerLeft (HomotopyCategory.quotient C (.up ℤ))
        (adj.mapHomotopyCategory (.up ℤ)).unit =
        (Functor.rightUnitor _).hom ≫ (Functor.leftUnitor _).inv ≫
          Functor.whiskerRight (adj.mapHomologicalComplex (.up ℤ)).unit
            (HomotopyCategory.quotient C (.up ℤ)) ≫
          (Functor.associator _ _ _).hom ≫
          Functor.whiskerLeft (L.mapHomologicalComplex (.up ℤ))
            (R.mapHomotopyCategoryFactors (.up ℤ)).inv ≫
          (Functor.associator _ _ _).inv ≫
          Functor.whiskerRight (L.mapHomotopyCategoryFactors (.up ℤ)).inv
            (R.mapHomotopyCategory (.up ℤ)) ≫
          (Functor.associator _ _ _).hom := by
      ext K
      simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
        Functor.associator_hom_app, Functor.associator_inv_app,
        Functor.leftUnitor_inv_app, Functor.rightUnitor_hom_app,
        Adjunction.mapHomotopyCategory_unit_app_quotient, Category.id_comp]
      simp [Functor.mapHomotopyCategoryFactors]
    have : NatTrans.CommShift (Functor.whiskerLeft (HomotopyCategory.quotient C (.up ℤ))
        (adj.mapHomotopyCategory (.up ℤ)).unit) ℤ := by
      rw [heq]
      infer_instance
    exact NatTrans.CommShift.of_whiskerLeft _ (HomotopyCategory.quotient C (.up ℤ))
      (fun X ↦ ⟨_, 𝟙 _, (HomotopyCategory.quotient_obj_surjective X).choose_spec ▸
        inferInstance⟩)
  let η := adj.mapDerivedCategoryRightDerivedAdjunction.unit
  have heq : Functor.whiskerLeft DerivedCategory.Qh η =
      (Functor.rightUnitor _).hom ≫ (Functor.leftUnitor _).inv ≫
        Functor.whiskerRight (adj.mapHomotopyCategory (.up ℤ)).unit DerivedCategory.Qh ≫
        (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft (L.mapHomotopyCategory (.up ℤ)) R.rightDerivedFunctorUnit ≫
        (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight L.mapDerivedCategoryFactorsh.inv R.rightDerivedFunctor ≫
        (Functor.associator _ _ _).hom := by
    ext K
    apply (cancel_mono (R.rightDerivedFunctor.map
      (L.mapDerivedCategoryFactorsh.hom.app K))).1
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.associator_hom_app, Functor.associator_inv_app,
      Functor.leftUnitor_inv_app, Functor.rightUnitor_hom_app, Category.id_comp,
      Category.assoc, ← R.rightDerivedFunctor.map_comp,
      L.mapDerivedCategoryFactorsh.inv_hom_id_app, R.rightDerivedFunctor.map_id,
      Category.comp_id]
    erw [Category.id_comp, Category.comp_id]
    exact (adj.mapHomotopyCategory (.up ℤ)).derivedη_fac_app
      (HomotopyCategory.quasiIso C (.up ℤ)) L.mapDerivedCategoryFactorsh.hom
      R.rightDerivedFunctorUnit K
  have : NatTrans.CommShift (Functor.whiskerLeft DerivedCategory.Qh η) ℤ := by
    rw [heq]
    infer_instance
  exact NatTrans.CommShift.of_whiskerLeft _ DerivedCategory.Qh
    (fun X ↦ ⟨_, (DerivedCategory.Qh.objObjPreimageIso X).inv, inferInstance⟩)


set_option backward.isDefEq.respectTransparency false in
private theorem pullback_commShift {X Y : Scheme.{v}} (f : X ⟶ Y) :
    NatTrans.CommShift (derivedSectionPullback f) ℤ := by
  have : NatTrans.CommShift (lowerStar AddCommGrpCat.{v + 1} f).rightDerivedFunctorUnit ℤ :=
    canonical_unit_commShift _
  dsimp only [derivedSectionPullback]
  have : NatTrans.CommShift
      (Functor.rightDerivedFunctorCompIso'
        (lowerStar AddCommGrpCat.{v + 1} f)
        (Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{v + 1})
        (Functor.isoWhiskerLeft (lowerStar AddCommGrpCat.{v + 1} f)
            (Sheaf.ΓNatIsoSheafSections Y.smallEtaleTopology AddCommGrpCat.{v + 1}
              terminalIsTerminal) ≪≫
          lowerStarCompSheafSectionsTerminalIso AddCommGrpCat.{v + 1} f ≪≫
          (Sheaf.ΓNatIsoSheafSections X.smallEtaleTopology AddCommGrpCat.{v + 1}
            terminalIsTerminal).symm)).hom ℤ := by
    have := canonical_unit_commShift
      (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{v + 1})
    have := canonical_unit_commShift
      (Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{v + 1})
    apply Functor.commShift_rightDerivedFunctorCompIso'_hom
  let R := rightDerivedGlobalSections AddCommGrpCat.{v + 1} Y
  let L := D(upperStar AddCommGrpCat.{v + 1} f)
  let P := (lowerStar AddCommGrpCat.{v + 1} f).rightDerivedFunctor
  have hu : NatTrans.CommShift
      (mapDerivedUpperStarLowerStarAdjunction AddCommGrpCat.{v + 1} f).unit ℤ :=
    canonical_adjunction_unit_commShift (upperStarLowerStarAdjunction _ f)
  have heq : derivedSectionPullback f =
      (Functor.leftUnitor R).inv ≫
        Functor.whiskerRight
          (mapDerivedUpperStarLowerStarAdjunction AddCommGrpCat.{v + 1} f).unit R ≫
        (Functor.associator L P R).hom ≫
        Functor.whiskerLeft L
          (Functor.rightDerivedFunctorCompIso'
            (lowerStar AddCommGrpCat.{v + 1} f)
            (Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{v + 1})
            (Functor.isoWhiskerLeft (lowerStar AddCommGrpCat.{v + 1} f)
                (Sheaf.ΓNatIsoSheafSections Y.smallEtaleTopology AddCommGrpCat.{v + 1}
                  terminalIsTerminal) ≪≫
              lowerStarCompSheafSectionsTerminalIso AddCommGrpCat.{v + 1} f ≪≫
              (Sheaf.ΓNatIsoSheafSections X.smallEtaleTopology AddCommGrpCat.{v + 1}
                terminalIsTerminal).symm)).hom := by
    ext K
    simp [derivedSectionPullback, R, L, P]
  change NatTrans.CommShift (derivedSectionPullback f) ℤ
  rw [heq]
  infer_instance

private theorem lift_composite_commShift
    {C C' B B' E : Type*} [Category C] [Category C'] [Category B] [Category B']
    [Category E] [HasShift C ℤ] [HasShift C' ℤ] [HasShift B ℤ] [HasShift B' ℤ]
    [HasShift E ℤ] (A : C ⥤ B) (A' : C' ⥤ B') (N : B ⥤ B') (L : C ⥤ C')
    (P : B ⥤ E) (Q : B' ⥤ E) [A.CommShift ℤ] [A'.CommShift ℤ] [N.CommShift ℤ]
    [L.CommShift ℤ] [P.CommShift ℤ] [Q.CommShift ℤ]
    (β : P ⟶ N ⋙ Q) [NatTrans.CommShift β ℤ]
    (ε : L ⋙ A' ≅ A ⋙ N) [NatTrans.CommShift ε.inv ℤ]
    (τ : A ⋙ P ⟶ L ⋙ A' ⋙ Q)
    (hτ : τ = Functor.whiskerLeft A β ≫ (Functor.associator A N Q).inv ≫
      Functor.whiskerRight ε.inv Q ≫ (Functor.associator L A' Q).hom) :
    NatTrans.CommShift τ ℤ := by
  rw [hτ]
  infer_instance

private theorem transport_homology
    {C C' D E : Type*} [Category C] [Category C'] [Category D] [Category E]
    [HasShift C ℤ] [HasShift C' ℤ] [HasShift D ℤ]
    (T : C ⥤ D) (T' : C' ⥤ D) (L : C ⥤ C')
    [T.CommShift ℤ] [T'.CommShift ℤ] [L.CommShift ℤ]
    (τ : T ⟶ L ⋙ T') [NatTrans.CommShift τ ℤ]
    (H₀ Hp : D ⥤ E) (n : ℤ) (σ : shiftFunctor D n ⋙ H₀ ⟶ Hp)
    {K : C} {K' : C'} (f : L.obj K ⟶ K')
    {X X' : D} (e : T.obj K ≅ X) (e' : T'.obj K' ≅ X') :
    H₀.map (τ.app (K⟦n⟧)) ≫
        H₀.map (T'.map ((L.commShiftIso n).hom.app K ≫ (shiftFunctor _ n).map f)) ≫
        H₀.map ((T'.commShiftIso n).hom.app K') ≫
          σ.app (T'.obj K') ≫ Hp.map e'.hom =
      H₀.map ((T.commShiftIso n).hom.app K) ≫ σ.app (T.obj K) ≫ Hp.map e.hom ≫
        Hp.map (e.inv ≫ τ.app K ≫ T'.map f ≫ e'.hom) := by
  have hc := NatTrans.shift_app_comm τ n K
  simp only [Functor.commShiftIso_comp_hom_app] at hc
  have ht : τ.app (K⟦n⟧) ≫
      T'.map ((L.commShiftIso n).hom.app K ≫ (shiftFunctor _ n).map f) ≫
      (T'.commShiftIso n).hom.app K' =
    (T.commShiftIso n).hom.app K ≫ (shiftFunctor _ n).map (τ.app K ≫ T'.map f) := by
    rw [T'.map_comp, Category.assoc, T'.commShiftIso_hom_naturality]
    simp only [← Category.assoc] at hc ⊢
    rw [← hc]
    simp only [Functor.map_comp, Category.assoc]
  rw [← H₀.map_comp_assoc, ← H₀.map_comp_assoc]
  simp only [Category.assoc]
  rw [ht, H₀.map_comp, Category.assoc]
  erw [σ.naturality_assoc]
  simp only [Functor.map_comp, Category.assoc]
  have he : Hp.map e.hom ≫ Hp.map e.inv = 𝟙 _ := by
    rw [← Hp.map_comp, e.hom_inv_id, Hp.map_id]
  rw [reassoc_of% he]

private theorem evaluation_shift_transport
    {C C' D D' : Type*} [Category C] [Category C'] [Category D] [Category D']
    [Abelian C] [Abelian C'] [Abelian D] [Abelian D']
    [HasDerivedCategory C] [HasDerivedCategory C'] [HasDerivedCategory D]
    [HasDerivedCategory D'] [EnoughInjectives D] [EnoughInjectives D']
    [HasKInjectiveResolutions D] [HasKInjectiveResolutions D']
    (L₀ : C ⥤ D) [L₀.Additive] [PreservesFiniteLimits L₀] [PreservesFiniteColimits L₀]
    (L₀' : C' ⥤ D') [L₀'.Additive] [PreservesFiniteLimits L₀']
    [PreservesFiniteColimits L₀']
    (R : D ⥤ AddCommGrpCat.{v + 1}) [R.Additive] [PreservesFiniteLimits R]
    (R' : D' ⥤ AddCommGrpCat.{v + 1}) [R'.Additive] [PreservesFiniteLimits R']
    (N : DerivedCategory.Plus C ⥤ DerivedCategory.Plus C') [N.CommShift ℤ]
    (τ : Evaluation.functor L₀ R ⟶ N ⋙ Evaluation.functor L₀' R')
    [NatTrans.CommShift τ ℤ] (p : ℕ) (F : C) (F' : C')
    (f : N.obj ((DerivedCategory.Plus.singleFunctor C 0).obj F) ⟶
      (DerivedCategory.Plus.singleFunctor C' 0).obj F') :
    let K := (DerivedCategory.Plus.singleFunctor C 0).obj F
    let T' := Evaluation.functor L₀' R'
    (DerivedCategory.homologyFunctor AddCommGrpCat.{v + 1} 0).map (τ.app (K⟦(p : ℤ)⟧)) ≫
      (T' ⋙ DerivedCategory.homologyFunctor AddCommGrpCat.{v + 1} 0).map
        ((N.commShiftIso (p : ℤ)).hom.app K ≫ (shiftFunctor _ (p : ℤ)).map f) ≫
      (Evaluation.shiftIso L₀' R' p F').hom =
    (Evaluation.shiftIso L₀ R p F).hom ≫
      (DerivedCategory.homologyFunctor AddCommGrpCat.{v + 1} (p : ℤ)).map
        ((Evaluation.singleIso L₀ R F).inv ≫ τ.app K ≫ T'.map f ≫
          (Evaluation.singleIso L₀' R' F').hom) := by
  dsimp only
  simp only [Evaluation.shiftIso, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom,
    Functor.comp_map, Category.assoc]
  exact transport_homology (Evaluation.functor L₀ R) (Evaluation.functor L₀' R') N τ
    (DerivedCategory.homologyFunctor AddCommGrpCat.{v + 1} 0)
    (DerivedCategory.homologyFunctor AddCommGrpCat.{v + 1} (p : ℤ)) (p : ℤ)
    ((DerivedCategory.homologyFunctor AddCommGrpCat.{v + 1} 0).shiftIso
      (p : ℤ) 0 (p : ℤ) (by simp)).hom f
    (Evaluation.singleIso L₀ R F) (Evaluation.singleIso L₀' R' F')

set_option backward.isDefEq.respectTransparency false in
-- The composite shift structures require several coherence comparisons.
set_option synthInstance.maxSize 256 in
set_option maxRecDepth 2048 in
/-- Shifted restricted section pullback is the conjugate of its unshifted derived map.
Source: Stacks Project, Tags 07A6 and 0D6F.
(blueprint: lem-sbc-restricted-derived-sections-shift-transport).

Proof: Write T and T' for restriction followed by derived global sections, L for
D+(a^*), and tau for the derived pullback followed by the restriction-composition
comparison. The inverse-image adjunction on complexes is degreewise, so its unit
commutes with shifts. Localize that equality. The Leray comparison commutes with
shifts because it is characterized by the composite right-derived unit, whose
factors commute with shifts. The comparison q^*r^* = r'^*a^* is induced from exact
functors on complexes and also commutes with shifts. Whiskering and composing
these equalities proves shift compatibility of tau for the canonical composite
shift structures on T and L followed by T'. Apply this identity at F[0].
Naturality of the target shift comparison moves the arbitrary shifted morphism f
past that comparison. Naturality of the homology shift isomorphism then identifies
H^0 of the shifted composite with H^p of tau at F[0] followed by T'(f).
Expand both shiftIso maps into their functor shift, homology shift and single
comparisons. Insert the inverse of the source single comparison immediately
before the unshifted map; its product with that single comparison is the identity.
Associativity and functoriality give the displayed conjugation formula. This
argument does not compute the unshifted map on any coefficient morphism and
works for any f, for p=0, and for an empty restricted scheme. -/
theorem restrictedDerivedSections_shiftTransport {S Y Y' : Scheme.{v}}
    (a : Y' ⟶ Y) (h : Y ⟶ S) (h' : Y' ⟶ S) (w : a ≫ h = h') (p : ℕ)
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{v + 1})
    (F' : Sheaf Y'.smallEtaleTopology AddCommGrpCat.{v + 1})
    (f : D+(upperStar AddCommGrpCat.{v + 1} a).obj
      ((DerivedCategory.Plus.singleFunctor _ 0).obj F) ⟶
        (DerivedCategory.Plus.singleFunctor _ 0).obj F') (U : S.Etale) :
    let T' := sectionsFunctor ((MorphismProperty.Over.pullback @Etale ⊤ h').obj U)
    let K := (DerivedCategory.Plus.singleFunctor _ 0).obj F
    let τ := Functor.whiskerLeft
      (DerivedCategory.Plus.ι ⋙
        D(upperStar AddCommGrpCat.{v + 1} (Limits.pullback.snd U.hom h)))
      (derivedSectionPullback (rawAffineRestrictedMap a h h' w U)) ≫
      Functor.whiskerRight
        (Functor.whiskerLeft DerivedCategory.Plus.ι
          (derivedRestrictionIso a h h' w U).hom)
        (rightDerivedGlobalSections AddCommGrpCat.{v + 1} (Limits.pullback U.hom h'))
    let e := Evaluation.singleIso
      (upperStar AddCommGrpCat.{v + 1} (Limits.pullback.snd U.hom h))
      (Sheaf.Γ (Limits.pullback U.hom h).smallEtaleTopology AddCommGrpCat.{v + 1}) F
    let e' := Evaluation.singleIso
      (upperStar AddCommGrpCat.{v + 1} (Limits.pullback.snd U.hom h'))
      (Sheaf.Γ (Limits.pullback U.hom h').smallEtaleTopology AddCommGrpCat.{v + 1}) F'
    (restrictedSectionPullback a h h' w U).app (K⟦(p : ℤ)⟧) ≫
      (T' ⋙ DerivedCategory.homologyFunctor AddCommGrpCat.{v + 1} 0).map
        ((D+(upperStar AddCommGrpCat.{v + 1} a).commShiftIso (p : ℤ)).hom.app K ≫
          (shiftFunctor _ (p : ℤ)).map f) ≫ (shiftIso h' p F' U).hom =
      (shiftIso h p F U).hom ≫
        (DerivedCategory.homologyFunctor AddCommGrpCat.{v + 1} (p : ℤ)).map
          (e.inv ≫ τ.app K ≫ T'.map f ≫ e'.hom) := by
  dsimp only
  let T := Evaluation.functor
    (upperStar AddCommGrpCat.{v + 1} (Limits.pullback.snd U.hom h))
    (Sheaf.Γ (Limits.pullback U.hom h).smallEtaleTopology AddCommGrpCat.{v + 1})
  let T' := Evaluation.functor
    (upperStar AddCommGrpCat.{v + 1} (Limits.pullback.snd U.hom h'))
    (Sheaf.Γ (Limits.pullback U.hom h').smallEtaleTopology AddCommGrpCat.{v + 1})
  let L := D+(upperStar AddCommGrpCat.{v + 1} a)
  let K := (DerivedCategory.Plus.singleFunctor _ 0).obj F
  let τ : T ⟶ L ⋙ T' := Functor.whiskerLeft
      (DerivedCategory.Plus.ι ⋙
        D(upperStar AddCommGrpCat.{v + 1} (Limits.pullback.snd U.hom h)))
      (derivedSectionPullback (rawAffineRestrictedMap a h h' w U)) ≫
    Functor.whiskerRight
      (Functor.whiskerLeft DerivedCategory.Plus.ι
        (derivedRestrictionIso a h h' w U).hom)
      (rightDerivedGlobalSections AddCommGrpCat.{v + 1} (Limits.pullback U.hom h'))
  let A := (DerivedCategory.Plus.ι :
    DerivedCategory.Plus (Sheaf Y.smallEtaleTopology AddCommGrpCat.{v + 1}) ⥤ _)
  let B := (DerivedCategory.Plus.ι :
    DerivedCategory.Plus (Sheaf Y'.smallEtaleTopology AddCommGrpCat.{v + 1}) ⥤ _)
  let R := D(upperStar AddCommGrpCat.{v + 1} (Limits.pullback.snd U.hom h))
  let R' := D(upperStar AddCommGrpCat.{v + 1} (Limits.pullback.snd U.hom h'))
  let N := D(upperStar AddCommGrpCat.{v + 1} a)
  let M := D(upperStar AddCommGrpCat.{v + 1} (rawAffineRestrictedMap a h h' w U))
  let P := rightDerivedGlobalSections AddCommGrpCat.{v + 1} (Limits.pullback U.hom h)
  let Q := rightDerivedGlobalSections AddCommGrpCat.{v + 1} (Limits.pullback U.hom h')
  have hcomp : NatTrans.CommShift
      (upperStar AddCommGrpCat.{v + 1} a).mapDerivedCategoryPlusCompatibility.inv ℤ := by
    change NatTrans.CommShift
      (DerivedCategory.TStructure.t.plus.liftCompιIso
        (A ⋙ N) (fun X ↦ (L.obj X).2)).inv ℤ
    infer_instance
  have hτ : NatTrans.CommShift τ ℤ := by
    have := restriction_commShift a h h' w U
    have := pullback_commShift (rawAffineRestrictedMap a h h' w U)
    let β : R ⋙ P ⟶ N ⋙ R' ⋙ Q :=
      Functor.whiskerLeft R (derivedSectionPullback (rawAffineRestrictedMap a h h' w U)) ≫
        (Functor.associator R M Q).inv ≫
        Functor.whiskerRight (derivedRestrictionIso a h h' w U).hom Q ≫
        (Functor.associator N R' Q).hom
    have : NatTrans.CommShift β ℤ := by
      dsimp only [β, R, R', N, M, P, Q]
      infer_instance
    have heq : τ =
        Functor.whiskerLeft A β ≫
          (Functor.associator A N (R' ⋙ Q)).inv ≫
          Functor.whiskerRight
            (upperStar AddCommGrpCat.{v + 1} a).mapDerivedCategoryPlusCompatibility.inv
            (R' ⋙ Q) ≫
          (Functor.associator L B (R' ⋙ Q)).hom := by
      ext X
      simp only [Functor.comp_obj, Functor.id_obj, Functor.const_obj_obj, NatTrans.comp_app,
        Functor.whiskerLeft_app, Functor.associator_inv_app, ObjectProperty.ι_obj,
        Functor.whiskerRight_app, Functor.comp_map, Functor.associator_hom_app, Category.id_comp]
      erw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, Category.comp_id]
      dsimp only [τ, β, A, R, R', N, M, Q, P, Functor.whiskerLeft_app,
        Functor.whiskerRight_app, NatTrans.comp_app, Functor.associator_hom_app,
        Functor.associator_inv_app]
      simp only [Category.id_comp, Category.comp_id]
      exact (Category.comp_id _).symm
    exact lift_composite_commShift A B N L (R ⋙ P) (R' ⋙ Q) β
      (upperStar AddCommGrpCat.{v + 1} a).mapDerivedCategoryPlusCompatibility τ heq
  exact evaluation_shift_transport
    (upperStar AddCommGrpCat.{v + 1} (Limits.pullback.snd U.hom h))
    (upperStar AddCommGrpCat.{v + 1} (Limits.pullback.snd U.hom h'))
    (Sheaf.Γ (Limits.pullback U.hom h).smallEtaleTopology AddCommGrpCat.{v + 1})
    (Sheaf.Γ (Limits.pullback U.hom h').smallEtaleTopology AddCommGrpCat.{v + 1})
    L τ p F F' f

end AlgebraicGeometry.Etale.RawRestrictedComparison
