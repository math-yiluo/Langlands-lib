/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Affine.Trace.AffineTraceConstruction
import WeilConjectures.SixFunctors.Etale.Derived.ClopenTransfer
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarIdCoherence

/-!
# Open counit compatibility for the standard affine-line exchange
Source: blueprint proposition-purity-vector-bundles, Step 5(b), detailed trace proof step 8.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v w
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

set_option backward.isDefEq.respectTransparency false in
private lemma pullback_comp_congr (A : Type (u + 1)) [CommRing A]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (h h' : X ⟶ Z)
    (w : h = f ≫ g) (w' : h' = f ≫ g) (M : DerivedCategoryModule A Z) :
    (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) f g h w).hom.app M =
      eqToHom (by rw [w, w']) ≫
        (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) f g h' w').hom.app M := by
  subst w w'
  simp

set_option backward.isDefEq.respectTransparency false in
private abbrev lineFormalism (A : Type (u + 1)) [CommRing A] : CompactSupportFormalism where
  obj X := DerivedCategoryModule A X
  category X := inferInstanceAs (Category.{u + 1} (DerivedCategoryModule A X))
  pb f := ordinaryFinitePullback A f
  pbId X := leftDerivedUpperStarId (ModuleCat.{u + 1} A) X
  pbComp f g := leftDerivedUpperStarComp (ModuleCat.{u + 1} A) f g
  pbComp_assoc f g h M := by
    have hh := leftDerivedUpperStarComp_assoc'_app (ModuleCat.{u + 1} A)
      f g h (f ≫ g) (g ≫ h) ((f ≫ g) ≫ h) rfl rfl rfl M
    dsimp only [ordinaryFinitePullback]
    rw [← hh, pullback_comp_congr A f (g ≫ h) _ (f ≫ g ≫ h)
      (Category.assoc _ _ _) rfl]
    simp only [Category.assoc]
  pbId_comp f M := by
    dsimp only [ordinaryFinitePullback]
    rw [pullback_comp_congr A (𝟙 _) f _ f rfl (Category.id_comp f).symm]
    rw [Category.assoc, leftDerivedUpperStarComp_id_left_hom_app]
    simp
  pbComp_id f M := by
    dsimp only [ordinaryFinitePullback]
    rw [pullback_comp_congr A f (𝟙 _) _ f rfl (Category.comp_id f).symm]
    rw [Category.assoc, leftDerivedUpperStarComp_id_right_hom_app]
    simp
  pf f := ordinaryFinitePushforward A f
  adj f := derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f
  sh j hj := haveI := hj.out; (openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategory
  shAdj j hj := haveI := hj.out; derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction A j

private lemma line_pb_comp (A : Type (u + 1)) [CommRing A]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z) (w : f ≫ g = h) :
    (lineFormalism A).pbComp' f g h w =
      leftDerivedUpperStarComp (ModuleCat.{u + 1} A) f g h w.symm := by
  subst w
  rw [ExchangeFormalism.pbComp'_rfl]

private lemma line_square (A : Type (u + 1)) [CommRing A]
    {X X' Y Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {g : Y' ⟶ Y} {g' : X' ⟶ X} (sq : CommSq g' f' f g) :
    (lineFormalism A).sqIso g' f' f g sq.w =
      (derivedSquareUpperStarIso (ModuleCat.{u + 1} A) sq).symm := by
  simp only [ExchangeFormalism.sqIso, line_pb_comp, derivedSquareUpperStarIso]
  rfl

private lemma line_open_baseChange (A : Type (u + 1)) [CommRing A]
    {U U' X X' : Scheme.{u}} {t : U' ⟶ U} {j' : U' ⟶ X'}
    {j : U ⟶ X} {b : X' ⟶ X} [IsOpenImmersion j] [IsOpenImmersion j']
    (sq : IsPullback t j' j b) :
    ((lineFormalism A).baseChange t j' j b sq.w) =
      (derivedOpenImmersionLowerShriekBaseChangeIso (ModuleCat.{u + 1} A) sq).hom := by
  rw [ExchangeFormalism.baseChange, line_square A sq.toCommSq]
  exact
    ((mateEquiv _ _).symm_apply_eq.mpr
      (mateEquiv_derivedOpenImmersionLowerShriekBaseChangeIso A sq).symm)

private local instance line_has_baseChange (A : Type (u + 1)) [CommRing A] :
    (lineFormalism A).HasBaseChange where
  isIso_baseChange sq := by
    rw [line_open_baseChange A sq]
    infer_instance

set_option backward.isDefEq.respectTransparency false in
private local instance line_has_properExchange (A : Type (u + 1)) [CommRing A] [Finite A] :
    (lineFormalism A).HasProperExchange where
  isIso_exchange {U' U Z' Z t l r b} _ _ _ sq := by
    let B := ModuleCat.{u + 1} A
    let F := lineFormalism A
    let := CompactSupportFormalism.HasBaseChange.isIso_baseChange
      (F := F) sq
    let α := F.exchange t l r b sq.w
    have (K : DerivedCategoryModule A U') : IsIso (α.app K) := by
      apply isIso_of_isIso_mapDerivedCategoryUpperStar_map B r r.closedComplement
        r.range_closedComplement
      · apply (NatIso.isIso_map_iff
          (leftDerivedUpperStarIsoMapDerivedCategory B r) _).mp
        have : IsIso (F.shAdj r).unit :=
          isIso_derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction_unit A r
        have : IsIso (F.shAdj l).unit :=
          isIso_derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction_unit A l
        exact isIso_map_mateEquiv_app_of_isIso (F.adj t) (F.adj b)
          (F.shAdj r) (F.shAdj l)
          (TwoSquare.mk _ _ _ _ (inv (F.baseChange t l r b sq.w))) K
      · have hdisj : Disjoint (Set.range r.closedComplement.base) (Set.range r.base) := by
          rw [r.range_closedComplement]
          exact disjoint_compl_left
        let sc := IsPullback.of_hasPullback b r.closedComplement
        have := isIso_derivedBaseChangeMap_of_isProper_of_isAddTorsion_ring A
          isAddTorsion_of_finite sc
        have hdisj' : Disjoint (Set.range (pullback.fst b r.closedComplement).base)
            (Set.range l.base) := by
          rw [Set.disjoint_left]
          rintro _ ⟨p, rfl⟩ ⟨x, hx⟩
          refine Set.disjoint_left.1 hdisj
            ⟨(pullback.snd b r.closedComplement).base p, rfl⟩ ⟨t.base x, ?_⟩
          rw [← Scheme.Hom.comp_apply, sq.w, Scheme.Hom.comp_apply, hx,
            ← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]
        refine isIso_of_source_target_iso_zero _
          (isZero_mapDerivedCategoryUpperStar_obj_openImmersionLowerShriek_of_disjoint_range
            B r r.closedComplement hdisj _).isoZero (IsZero.isoZero ?_)
        have hN : IsZero ((ordinaryFinitePullback A
            (pullback.fst b r.closedComplement)).obj ((F.sh l).obj K)) :=
          (isZero_mapDerivedCategoryUpperStar_obj_openImmersionLowerShriek_of_disjoint_range
            B l _ hdisj' K).of_iso ((leftDerivedUpperStarIsoMapDerivedCategory B _).app _)
        exact IsZero.of_iso
          (((lowerStar (ModuleCat.{u + 1} A)
            (pullback.snd b r.closedComplement)).rightDerivedFunctor).map_isZero hN)
          ((leftDerivedUpperStarIsoMapDerivedCategory B _).symm.app _ ≪≫
            asIso ((derivedBaseChangeMap B sc.toCommSq).app _))
    exact NatIso.isIso_of_isIso_app _

set_option backward.isDefEq.respectTransparency false in
private lemma line_refinement_baseChange (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} {c d : Compactification f}
    (r : c.Refinement d) (hr : IsPullback c.i (𝟙 X) r.hom d.i) :
    ((lineFormalism A).baseChange (𝟙 X) c.i d.i r.hom hr.flip.w) =
      Functor.whiskerRight ((lineFormalism A).pbId X).hom
          ((lineFormalism A).sh c.i) ≫
        (Functor.leftUnitor _).hom ≫
          (refinementLowerShriekBaseChangeLeftDerivedIso (ModuleCat.{u + 1} A) r hr).hom := by
  let B := ModuleCat.{u + 1} A
  let F := lineFormalism A
  apply (mateEquiv (F.shAdj d.i) (F.shAdj c.i)).injective
  rw [ExchangeFormalism.baseChange, Equiv.apply_symm_apply]
  apply (mateEquiv_eq_of_unit (F.shAdj d.i) (F.shAdj c.i) _ _ _).symm
  intro K
  have h := unit_map_refinementLowerShriekBaseChangeLeftDerivedIso B r hr K
  have hn := (leftDerivedUpperStarIsoMapDerivedCategory B c.i).inv.naturality
    ((refinementLowerShriekBaseChangeLeftDerivedIso B r hr).hom.app K)
  have hu : (derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction A c.i).unit.app K ≫
      (ordinaryFinitePullback A c.i).map
        ((refinementLowerShriekBaseChangeLeftDerivedIso B r hr).hom.app K) =
      (derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction A d.i).unit.app K ≫
        (leftDerivedUpperStarComp B c.i r.hom d.i r.i_hom.symm).hom.app
          (((openImmersionLowerShriek B d.i).mapDerivedCategory).obj K) := by
    simp only [derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction,
      Adjunction.ofNatIsoRight_unit, NatTrans.comp_app, Functor.whiskerLeft_app,
      Iso.symm_hom, Category.assoc]
    dsimp only [ordinaryFinitePullback, B] at hn h ⊢
    rw [← hn, reassoc_of% h, refinementSquareMap_app]
    simp only [Functor.comp_obj, Category.assoc, Iso.hom_inv_id_app, Category.comp_id]
  rw [ExchangeFormalism.sqIso_eq _ _ _ _ _ _ d.i (Category.id_comp _) r.i_hom]
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.leftUnitor_hom_app, Functor.map_comp]
  rw [ExchangeFormalism.pbComp'_id_left_inv_app, line_pb_comp]
  have h₁ := (F.pbId X).hom.naturality ((F.shAdj d.i).unit.app K)
  have h₂ := (F.shAdj c.i).unit_naturality ((F.pbId X).hom.app K)
  erw [reassoc_of% h₁, CategoryTheory.Functor.map_id, Category.id_comp, reassoc_of% h₂]
  simpa only [refinementLowerShriekBaseChangeLeftDerivedIso, Iso.trans_hom,
    NatTrans.comp_app, Functor.map_comp, Category.assoc] using
      congrArg (fun t ↦ (F.pbId X).hom.app K ≫ t) hu.symm

private lemma line_pf_comp (A : Type (u + 1)) [CommRing A]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z) (w : f ≫ g = h) :
    ((lineFormalism A).pfComp' f g h w).inv =
      (rightDerivedLowerStarCompHom (ModuleCat.{u + 1} A) f g h w.symm) := by
  rw [ExchangeFormalism.pfComp', line_pb_comp]
  rfl

private lemma line_refinement_comparison (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} {c d : Compactification f}
    (r : c.Refinement d) (hr : IsPullback c.i (𝟙 X) r.hom d.i) :
    (lineFormalism A).refinementComparison r hr =
      rightDerivedLowerShriekOfCompactificationComparison (ModuleCat.{u + 1} A) r hr := by
  rw [CompactSupportFormalism.refinementComparison_eq_of_baseChange
    (lineFormalism A) r hr
    (refinementLowerShriekBaseChangeLeftDerivedIso (ModuleCat.{u + 1} A) r hr)
    (line_refinement_baseChange A r hr), line_pf_comp]
  ext K
  rw [rightDerivedLowerShriekOfCompactificationComparison_app]
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.comp_map, Iso.trans_inv, Functor.isoWhiskerLeft_inv, Iso.symm_inv,
    Category.assoc, Functor.map_comp]
  rfl

private lemma line_comparison (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f] (c d : Compactification f) :
    (lineFormalism A).shriekIso c d = rightDerivedLowerShriekOfCompactificationIso A c d := by
  apply Iso.ext
  simp only [CompactSupportFormalism.shriekIso, rightDerivedLowerShriekOfCompactificationIso,
    Iso.trans_hom, Iso.symm_hom, asIso_hom, asIso_inv, line_refinement_comparison]

private lemma mate_ofNatIsoLeft
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    {L₁ L₁' : C ⥤ D} {R₁ : D ⥤ C} {L₂ L₂' : E ⥤ F} {R₂ : F ⥤ E}
    {G : C ⥤ E} {H : D ⥤ F}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (e₁ : L₁ ≅ L₁') (e₂ : L₂ ≅ L₂')
    (α : TwoSquare G L₁' L₂' H) :
    (mateEquiv (adj₁.ofNatIsoLeft e₁) (adj₂.ofNatIsoLeft e₂) α) =
      (mateEquiv adj₁ adj₂ ((α.whiskerRight e₂.hom).whiskerLeft e₁.inv)) := by
  ext K
  simp [mateEquiv_apply, Adjunction.ofNatIsoLeft_unit,
    Adjunction.ofNatIsoLeft_counit, Category.assoc, ← Functor.map_comp]

private lemma mate_whiskerTop
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : E ⥤ F} {R₂ : F ⥤ E}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    {G G' : C ⥤ E} {H : D ⥤ F}
    (α : TwoSquare G' L₁ L₂ H) (γ : G ⟶ G') (K : D) :
    (mateEquiv adj₁ adj₂ (α.whiskerTop γ)).app K =
      γ.app (R₁.obj K) ≫ (mateEquiv adj₁ adj₂ α).app K := by
  simp [mateEquiv, TwoSquare.whiskerTop]

private lemma mate_whiskerBottom
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : E ⥤ F} {R₂ : F ⥤ E}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    {G : C ⥤ E} {H H' : D ⥤ F}
    (α : TwoSquare G L₁ L₂ H) (δ : H ⟶ H') (K : D) :
    (mateEquiv adj₁ adj₂ (α.whiskerBottom δ)).app K =
      (mateEquiv adj₁ adj₂ α).app K ≫ R₂.map (δ.app K) := by
  simp [mateEquiv, TwoSquare.whiskerBottom, ← Functor.map_comp, δ.naturality]

private lemma exact_exchange_transport
    (A : Type (u + 1)) [CommRing A]
    {X X' Y Y' : Scheme.{u}}
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {g : Y' ⟶ Y} {g' : X' ⟶ X}
    (sq : CommSq g' f' f g) :
    Functor.whiskerLeft (rightDerivedLowerStar (ModuleCat.{u + 1} A) f)
        (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) g).inv ≫
      derivedBaseChangeMap (ModuleCat.{u + 1} A) sq ≫
      Functor.whiskerRight
        (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) g').hom _ =
      exactDerivedBaseChangeMap (ModuleCat.{u + 1} A) sq := by
  let B := ModuleCat.{u + 1} A
  let α := TwoSquare.mk _ _ _ _ (exactDerivedSquareUpperStarIso B sq).hom
  have hs :
      ((((α.whiskerTop (leftDerivedUpperStarIsoMapDerivedCategory B g).hom).whiskerBottom
        (leftDerivedUpperStarIsoMapDerivedCategory B g').inv).whiskerRight
        (leftDerivedUpperStarIsoMapDerivedCategory B f').hom).whiskerLeft
        (leftDerivedUpperStarIsoMapDerivedCategory B f).inv) =
      TwoSquare.mk _ _ _ _ (derivedSquareUpperStarIso B sq).hom := by
    ext M
    simp only [α, TwoSquare.whiskerTop_app, TwoSquare.whiskerBottom_app,
      TwoSquare.whiskerLeft_app, TwoSquare.whiskerRight_app, TwoSquare.mk]
    simp only [derivedSquareUpperStarIso, leftDerivedUpperStarComp,
      exactDerivedSquareUpperStarIso, squareUpperStarIso,
      Functor.leftDerivedFunctorNatIso, Functor.leftDerivedFunctorCompIso,
      leftDerivedUpperStarIsoMapDerivedCategory, Iso.trans_hom, Iso.trans_inv,
      Iso.symm_hom, Iso.symm_inv, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
      Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv, Category.assoc,
      Functor.mapDerivedCategoryNatIso_trans, Functor.mapDerivedCategoryNatIso_symm,
      Iso.inv_hom_id_app_assoc]
    rw [← (upperStar B g').leftDerivedFunctorIsoMapDerivedCategory.inv.naturality]
  have hm := mate_ofNatIsoLeft
    (derivedUpperStarLowerStarAdjunction B f) (derivedUpperStarLowerStarAdjunction B f')
    (leftDerivedUpperStarIsoMapDerivedCategory B f)
    (leftDerivedUpperStarIsoMapDerivedCategory B f')
    ((α.whiskerTop (leftDerivedUpperStarIsoMapDerivedCategory B g).hom).whiskerBottom
      (leftDerivedUpperStarIsoMapDerivedCategory B g').inv)
  rw [← mapDerivedUpperStarLowerStarAdjunction_eq,
    ← mapDerivedUpperStarLowerStarAdjunction_eq, hs] at hm
  change _ = derivedBaseChangeMap B sq at hm
  rw [← hm]
  ext K
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
  rw [mate_whiskerBottom, mate_whiskerTop]
  change _ = (mateEquiv (mapDerivedUpperStarLowerStarAdjunction B f)
    (mapDerivedUpperStarLowerStarAdjunction B f') α).app K
  dsimp only [B, rightDerivedLowerStar, Functor.comp_obj]
  simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app]
  simp only [Iso.inv_hom_id_app_assoc]
  erw [CategoryTheory.Functor.map_id, Category.comp_id]

private lemma line_projective_exchange (A : Type (u + 1)) [CommRing A]
    {S' S : Scheme.{u}} (g : S' ⟶ S) (M : DerivedCategoryModule A (ProjectiveLine S)) :
    ordinaryFiniteP1Exchange A g M =
      (derivedBaseChangeMap (ModuleCat.{u + 1} A)
        (ProjectiveSpace.isPullback_map (ULift.{u} (Fin 2)) g).toCommSq).app M := by
  have h := NatTrans.congr_app (exact_exchange_transport A
    (ProjectiveSpace.isPullback_map (ULift.{u} (Fin 2)) g).toCommSq) M
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app] at h
  rw [ordinaryFiniteP1Exchange, ← h]
  dsimp only [ordinaryFinitePushforward, rightDerivedLowerStar]
  simp [Category.assoc, ← Functor.map_comp]

private lemma line_shriek_exchange (A : Type (u + 1)) [CommRing A]
    {X X' Y Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {g : Y' ⟶ Y} {g' : X' ⟶ X}
    (c : Compactification f) (c' : Compactification f') (h : c'.Z ⟶ c.Z)
    (hi : IsPullback g' c'.i c.i h) (hp : IsPullback h c'.g c.g g) :
    ((lineFormalism A).shriekBaseChange c c' h hi hp) =
      rightDerivedLowerShriekOfCompactificationBaseChangeMap'
        (ModuleCat.{u + 1} A) c c' h hi hp.toCommSq := by
  have := CompactSupportFormalism.HasBaseChange.isIso_baseChange
    (F := lineFormalism A) hi
  have hbc : inv ((lineFormalism A).baseChange g' c'.i c.i h hi.w) =
      (derivedOpenImmersionLowerShriekBaseChangeIso (ModuleCat.{u + 1} A) hi).inv := by
    apply IsIso.inv_eq_of_hom_inv_id
    rw [line_open_baseChange]
    exact Iso.hom_inv_id _
  simp only [CompactSupportFormalism.shriekBaseChange, ExchangeFormalism.shriekBaseChange,
    ExchangeFormalism.pfBaseChange,
    line_square A hp.toCommSq, Iso.symm_inv, hbc,
    rightDerivedLowerShriekOfCompactificationBaseChangeMap', TwoSquare.hComp,
    derivedBaseChangeMap, derivedBaseChangeSquare]
  rfl

private noncomputable def pullbackRefinement
    {X X' Y Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {g : Y' ⟶ Y} {g' : X' ⟶ X} (sq : IsPullback g' f' f g)
    (c : Compactification f) (c' : Compactification f') (h : c'.Z ⟶ c.Z)
    (hi : IsPullback g' c'.i c.i h) (hp : IsPullback h c'.g c.g g) :
    c'.Refinement (c.ofIsPullback sq) where
  hom := hp.isoPullback.hom
  i_hom := by
    apply pullback.hom_ext
    · simp only [Category.assoc, IsPullback.isoPullback_hom_fst,
        Compactification.ofIsPullback_i_fst]
      exact hi.w.symm
    · simp only [Category.assoc, IsPullback.isoPullback_hom_snd,
        Compactification.ofIsPullback_i_snd]
      exact c'.comm.symm
  hom_g := hp.isoPullback_hom_snd

private lemma pullbackRefinement_cartesian
    {X X' Y Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {g : Y' ⟶ Y} {g' : X' ⟶ X} (sq : IsPullback g' f' f g)
    (c : Compactification f) (c' : Compactification f') (h : c'.Z ⟶ c.Z)
    (hi : IsPullback g' c'.i c.i h) (hp : IsPullback h c'.g c.g g) :
    IsPullback c'.i (𝟙 X') (pullbackRefinement sq c c' h hi hp).hom
      (c.ofIsPullback sq).i := by
  have : IsIso (pullbackRefinement sq c c' h hi hp).hom := by
    change IsIso hp.isoPullback.hom
    infer_instance
  exact IsPullback.of_vert_isIso ⟨by
    rw [Category.id_comp, Compactification.Refinement.i_hom]⟩

private lemma shriekBaseChange_arbitrary
    (F : CompactSupportFormalism.{w, v, u}) [F.HasProperExchange]
    {X X' Y Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {g : Y' ⟶ Y} {g' : X' ⟶ X} (sq : IsPullback g' f' f g)
    [QuasiCompact f'] (c : Compactification f) (c' : Compactification f')
    (h : c'.Z ⟶ c.Z) (hi : IsPullback g' c'.i c.i h)
    (hp : IsPullback h c'.g c.g g) :
    (F.shriekBaseChange c c' h hi hp) =
      (F.shriekBaseChangeOfIsPullback sq c) ≫
        Functor.whiskerLeft (F.pb g') (F.shriekIso (c.ofIsPullback sq) c').hom := by
  let r := pullbackRefinement sq c c' h hi hp
  have hr := pullbackRefinement_cartesian sq c c' h hi hp
  have hid : IsPullback c.i (𝟙 X) (Compactification.Refinement.id c).hom c.i :=
    by
      rw [Compactification.Refinement.id_hom]
      exact IsPullback.of_vert_isIso ⟨by simp⟩
  have he := F.shriekBaseChange_refinementComparison
    (Compactification.Refinement.id c) hid r hr h hi hp
    (pullback.fst c.g g) (c.isPullback_i_ofIsPullback sq)
    (c.isPullback_g_ofIsPullback sq).flip (by
      change h ≫ 𝟙 c.Z = hp.isoPullback.hom ≫ pullback.fst c.g g
      rw [Category.comp_id, hp.isoPullback_hom_fst])
  rw [F.refinementComparison_eq_id _ hid rfl] at he
  have hh : Functor.whiskerRight (𝟙 (F.shriek c)) (F.pb g) = 𝟙 _ := by
    apply NatTrans.ext
    funext K
    exact (F.pb g).map_id _
  erw [hh, Category.id_comp] at he
  rw [← F.shriekIso_symm c' (c.ofIsPullback sq), F.shriekIso_eq_symm r hr]
  exact he

private lemma line_exchange_standard (A : Type (u + 1)) [CommRing A] [Finite A]
    {S' S : Scheme.{u}} (g : S' ⟶ S)
    (M : DerivedCategoryModule A (AffineSpace PUnit.{u + 1} S)) :
    affineTraceLineExchange A g M =
      (rightDerivedLowerShriekOfCompactificationBaseChangeMap' (ModuleCat.{u + 1} A)
        (affineTraceLineCompactification S) (affineTraceLineCompactification S')
        (ProjectiveSpace.map (ULift.{u} (Fin 2)) g) (affineTraceChart_isPullback g)
        (ProjectiveSpace.isPullback_map (ULift.{u} (Fin 2)) g).toCommSq).app M := by
  have he := shriekBaseChange_arbitrary (lineFormalism A)
    (AffineSpace.isPullback_map (n := PUnit.{u + 1}) g)
    (affineTraceLineCompactification S) (affineTraceLineCompactification S')
    (ProjectiveSpace.map (ULift.{u} (Fin 2)) g) (affineTraceChart_isPullback g)
    (ProjectiveSpace.isPullback_map (ULift.{u} (Fin 2)) g)
  rw [line_shriek_exchange, line_comparison] at he
  rw [affineTraceLineExchange_eq]
  dsimp only [CompactSupportFormalism.shriekBaseChangeOfIsPullback] at he
  rw [line_shriek_exchange] at he
  exact (NatTrans.congr_app he M).symm

private lemma line_square_standard (A : Type (u + 1)) [CommRing A]
    {S' S : Scheme.{u}} (g : S' ⟶ S) :
    affineTraceOpenPullbackSquare A g =
      (derivedSquareUpperStarIso (ModuleCat.{u + 1} A)
        (affineTraceChart_isPullback g).toCommSq).symm := by
  have hc {X Y Z : Scheme.{u}} (f : X ⟶ Y) (h : Y ⟶ Z)
      (k k' : X ⟶ Z) (e : k = k') (hk : k = f ≫ h) (hk' : k' = f ≫ h) :
      eqToIso (congrArg (ordinaryFinitePullback A) e) ≪≫
          leftDerivedUpperStarComp (ModuleCat.{u + 1} A) f h k' hk' =
        leftDerivedUpperStarComp (ModuleCat.{u + 1} A) f h k hk := by
    subst e
    simp
  unfold affineTraceOpenPullbackSquare derivedSquareUpperStarIso
  rw [Iso.trans_symm]
  change _ = _ ≪≫ leftDerivedUpperStarComp _ _ _ _ _
  rw [hc]
  exact (affineTraceChart_isPullback g).w

/-- The standard compact-support exchange respects the open counit before the
projective trace is applied.
Source: blueprint lemma-integral-linear-character--1, proof step 8
(blueprint: lem-amb-affine-trace-line-open-counit-base-change).

Proof: first work with the pulled-back projective compactification. Expand its
exchange as proper direct-image exchange followed by inverse open exchange.
The identity unit_map_derivedOpenImmersionLowerShriekBaseChangeIso says that open
exchange is the mate of the pullback square. Apply the open adjunction hom-equivalence
to the two proposed counit composites: both become the same pullback-square map by
the unit-counit triangle identity. Thus the open square commutes on every M.
Naturality of proper direct-image exchange moves the old open counit through the
proper factor. Transport the resulting square from the pulled-back projective
compactification to the standard one. The comparison is the composite through a
common refinement of the proper/open unit, inverse open exchange and direct-image
composition. The units and composition comparisons cancel by their triangle and
pasting identities, giving the displayed square for the actual chosen comparison.
The inverse-image comparisons from derived to exact inverse image are natural, so
the same equation holds for the left-derived pullbacks in this statement.
This is a formal mate identity; it applies to arbitrary unbounded M and includes
identity base change, empty schemes and zero coefficients. No Tate datum or
projective trace is used. -/
theorem affineTraceLineExchange_openCounit (A : Type (u + 1)) [CommRing A] [Finite A]
    {S' S : Scheme.{u}} (g : S' ⟶ S)
    (M : DerivedCategoryModule A (ProjectiveLine S)) :
    let J := affineTraceOpenAdjunction A S
    let J' := affineTraceOpenAdjunction A S'
    affineTraceLineExchange A g
        ((ordinaryFinitePullback A (ProjectiveLine.affineChart S)).obj M) ≫
      (affineTraceLineLeft A S').map ((affineTraceOpenPullbackSquare A g).hom.app M) ≫
      (ordinaryFinitePushforward A (ProjectiveLine S' ↘ S')).map
        (J'.counit.app ((ordinaryFinitePullback A
          (ProjectiveSpace.map (ULift.{u} (Fin 2)) g)).obj M)) =
    (ordinaryFinitePullback A g).map
      ((ordinaryFinitePushforward A (ProjectiveLine S ↘ S)).map (J.counit.app M)) ≫
        ordinaryFiniteP1Exchange A g M := by
  dsimp only
  rw [line_exchange_standard, line_square_standard, line_projective_exchange,
    rightDerivedLowerShriekOfCompactificationBaseChangeMap'_app]
  have hc := leftDerivedUpperStar_map_counit_derivedOpenImmersionLowerShriek A
    (affineTraceChart_isPullback g) M
  have hn := (derivedBaseChangeMap (ModuleCat.{u + 1} A)
    (ProjectiveSpace.isPullback_map (ULift.{u} (Fin 2)) g).toCommSq).naturality
      ((affineTraceOpenAdjunction A S).counit.app M)
  have ha (T : Scheme.{u}) : affineTraceOpenAdjunction A T =
      derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction A
        (ProjectiveLine.affineChart T) := by
    unfold affineTraceOpenAdjunction derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction
    rfl
  rw [ha] at hn
  simp only [Functor.comp_map, Functor.comp_obj] at hn
  dsimp only [affineTraceLineCompactification, affineTraceLineLeft, affineTraceOpenLeft,
    ordinaryFinitePullback, ordinaryFinitePushforward, Iso.symm_hom] at hn ⊢
  simp only [Functor.comp_map, Category.assoc, ha]
  erw [← (ordinaryFinitePushforward A (ProjectiveLine S' ↘ S')).map_comp,
    ← (ordinaryFinitePushforward A (ProjectiveLine S' ↘ S')).map_comp, ← hc, ← hn]
  rfl

end AlgebraicGeometry.Etale
