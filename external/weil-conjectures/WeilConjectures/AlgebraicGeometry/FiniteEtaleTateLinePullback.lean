/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateSheaf
public import WeilConjectures.EtaleCohomology.TateTwist.Sheaf
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
import WeilConjectures.EtaleCohomology.TateTwist.RootsOfUnityPullback

/-! # Generator-normalized pullback of finite Tate lines
Source: Stacks Project, Etale Cohomology, Section 03PK. -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u u'
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Scheme

private lemma finiteEtaleGenerator_smul (T : Scheme.{u}) (N : ℕ)
    (A : Type (u + 1)) [CommRing A] (hA : (N : A) = 0) (W : T.Etaleᵒᵖ)
    (a : A) (z : (T.rootsOfUnitySheaf N).obj.obj W) :
    finiteEtaleTateOneGenerator A N T hA W a z =
      a • finiteEtaleTateOneGenerator A N T hA W 1 z := by
  unfold finiteEtaleTateOneGenerator
  let f := (toSheafify T.smallEtaleTopology
    (finiteEtaleMuModulePresheaf T N ⋙
      ModuleCat.extendScalars (finiteEtaleTwistScalar N A hA))).app W
  exact (congrArg f (by
    simpa only [mul_one] using
      (ModuleCat.ExtendScalars.smul_tmul (finiteEtaleTwistScalar N A hA)
        (M := finiteEtaleMuModuleObj T N W) a 1 z).symm)).trans
    (f.hom.map_smul a _)

private noncomputable def muHomEquiv (T : Scheme.{u}) (N : ℕ) (A : Type (u + 1)) [CommRing A]
    (hA : (N : A) = 0) (P : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    (finiteEtaleMuModulePresheaf T N ⟶
      P.obj ⋙ ModuleCat.restrictScalars (finiteEtaleTwistScalar N A hA)) ≃
    (T.rootsOfUnitySheaf N ⟶
      (sheafCompose T.smallEtaleTopology
        (forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1})).obj P) where
  toFun f := ⟨{
    app := fun U ↦ AddCommGrpCat.ofHom (f.app U).hom.toAddMonoidHom
    naturality := by
      intro U V g
      ext x
      exact ConcreteCategory.congr_hom (f.naturality g) x }⟩
  invFun f := {
    app := fun U ↦ ModuleCat.ofHom
      (X := finiteEtaleMuModuleObj T N U)
      (Y := (ModuleCat.restrictScalars (finiteEtaleTwistScalar N A hA)).obj (P.obj.obj U))
      (AddMonoidHom.toZModLinearMap N
        (M := finiteEtaleMuModuleObj T N U)
        (M₁ := (ModuleCat.restrictScalars (finiteEtaleTwistScalar N A hA)).obj (P.obj.obj U))
        (f.hom.app U).hom)
    naturality := by
      intro U V g
      ext x
      exact ConcreteCategory.congr_hom (f.hom.naturality g) x }
  left_inv f := by ext U x; rfl
  right_inv f := by ext U x; rfl

private noncomputable def lineHomEquiv (T : Scheme.{u}) (N : ℕ) (A : Type (u + 1)) [CommRing A]
    (hA : (N : A) = 0) (P : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    (finiteEtaleTateLine T N A hA ⟶ P) ≃
    (T.rootsOfUnitySheaf N ⟶
      (sheafCompose T.smallEtaleTopology
        (forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1})).obj P) :=
  ((sheafificationAdjunction T.smallEtaleTopology (ModuleCat.{u + 1} A)).homEquiv _ P).trans
    ((((ModuleCat.extendRestrictScalarsAdj.{u + 1, 0, u + 1}
      (finiteEtaleTwistScalar N A hA)).whiskerRight
      T.Etaleᵒᵖ).homEquiv _ P.obj).trans (muHomEquiv T N A hA P))

private lemma lineHomEquiv_generator (T : Scheme.{u}) (N : ℕ)
    (A : Type (u + 1)) [CommRing A] (hA : (N : A) = 0)
    (P : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))
    (f : finiteEtaleTateLine T N A hA ⟶ P) (U : T.Etaleᵒᵖ)
    (z : (T.rootsOfUnitySheaf N).obj.obj U) :
    (lineHomEquiv T N A hA P f).hom.app U z =
      f.hom.app U (finiteEtaleTateOneGenerator A N T hA U 1 z) := by
  dsimp [lineHomEquiv, muHomEquiv]
  change ((ModuleCat.extendRestrictScalarsAdj.{u + 1, 0, u + 1}
      (finiteEtaleTwistScalar N A hA)).homEquiv _ _
        ((toSheafify T.smallEtaleTopology _ ≫ f.hom).app U)) z = _
  rfl

private lemma lineHomEquiv_comp (T : Scheme.{u}) (N : ℕ)
    (A : Type (u + 1)) [CommRing A] (hA : (N : A) = 0)
    {P Q : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)}
    (f : finiteEtaleTateLine T N A hA ⟶ P) (g : P ⟶ Q) :
    lineHomEquiv T N A hA Q (f ≫ g) =
      lineHomEquiv T N A hA P f ≫
        (sheafCompose T.smallEtaleTopology
          (forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1})).map g := by
  ext U z
  change g.hom.app U (f.hom.app U
    (finiteEtaleTateOneGenerator A N T hA U 1 z)) =
    g.hom.app U ((lineHomEquiv T N A hA P f).hom.app U z)
  rw [lineHomEquiv_generator]

private noncomputable def linePullbackMap
    (A : Type (u + 1)) [CommRing A] (m : ℕ) (hA : (m : A) = 0)
    {T T' : Scheme.{u}} (v : T' ⟶ T) :
    (Etale.upperStar (ModuleCat.{u + 1} A) v).obj (finiteEtaleTateLine T m A hA) ⟶
      finiteEtaleTateLine T' m A hA :=
  ((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) v).homEquiv _ _).symm
    ((lineHomEquiv T m A hA
      ((Etale.lowerStar (ModuleCat.{u + 1} A) v).obj (finiteEtaleTateLine T' m A hA))).symm
      (((Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} v).homEquiv _ _)
        (upperStarRootsOfUnitySheafToRootsOfUnitySheaf m v) ≫
        (Etale.lowerStar AddCommGrpCat.{u + 1} v).map
          (lineHomEquiv T' m A hA _ (𝟙 _))))

private lemma linePullbackMap_generator
    (A : Type (u + 1)) [CommRing A] (m : ℕ) (hA : (m : A) = 0)
    {T T' : Scheme.{u}} (v : T' ⟶ T) (W : T.Etaleᵒᵖ) (a : A)
    (z : (T.rootsOfUnitySheaf m).obj.obj W) :
    ((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) v).homEquiv _ _
      (linePullbackMap A m hA v)).hom.app W
        (finiteEtaleTateOneGenerator A m T hA W a z) =
      finiteEtaleTateOneGenerator A m T' hA
        ((MorphismProperty.Over.pullback @Etale ⊤ v).op.obj W) a
        (((Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} v).homEquiv _ _
          (upperStarRootsOfUnitySheafToRootsOfUnitySheaf m v)).hom.app W z) := by
  let z' : (T'.rootsOfUnitySheaf m).obj.obj
      ((MorphismProperty.Over.pullback @Etale ⊤ v).op.obj W) :=
    (((Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} v).homEquiv _ _
      (upperStarRootsOfUnitySheafToRootsOfUnitySheaf m v)).hom.app W z)
  let f := ((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) v).homEquiv _ _
    (linePullbackMap A m hA v)).hom.app W
  have h1 : f (finiteEtaleTateOneGenerator A m T hA W 1 z) =
      finiteEtaleTateOneGenerator A m T' hA
        ((MorphismProperty.Over.pullback @Etale ⊤ v).op.obj W) 1 z' := by
    have h := congrArg (fun g ↦ g.hom.app W z)
      ((lineHomEquiv T m A hA
        ((Etale.lowerStar (ModuleCat.{u + 1} A) v).obj
          (finiteEtaleTateLine T' m A hA))).apply_symm_apply
        (((Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} v).homEquiv _ _)
          (upperStarRootsOfUnitySheafToRootsOfUnitySheaf m v) ≫
          (Etale.lowerStar AddCommGrpCat.{u + 1} v).map
            (lineHomEquiv T' m A hA _ (𝟙 _))))
    rw [lineHomEquiv_generator] at h
    dsimp only [f, linePullbackMap]
    rw [Equiv.apply_symm_apply]
    exact h.trans (lineHomEquiv_generator T' m A hA _ (𝟙 _)
      ((MorphismProperty.Over.pullback @Etale ⊤ v).op.obj W) z')
  change f (finiteEtaleTateOneGenerator A m T hA W a z) =
    finiteEtaleTateOneGenerator A m T' hA _ a z'
  rw [finiteEtaleGenerator_smul, _root_.map_smul, h1]
  exact (finiteEtaleGenerator_smul T' m A hA _ a z').symm

private lemma linePullbackMap_comp
    (A : Type (u + 1)) [CommRing A] (m : ℕ) (hA : (m : A) = 0)
    {T T' : Scheme.{u}} (v : T' ⟶ T)
    (P : Sheaf T'.smallEtaleTopology (ModuleCat.{u + 1} A))
    (g : finiteEtaleTateLine T' m A hA ⟶ P) :
    lineHomEquiv T m A hA _
        ((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) v).homEquiv _ _
          (linePullbackMap A m hA v ≫ g)) =
      ((Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} v).homEquiv _ _)
        (upperStarRootsOfUnitySheafToRootsOfUnitySheaf m v ≫
          lineHomEquiv T' m A hA P g) := by
  rw [Adjunction.homEquiv_naturality_right, lineHomEquiv_comp]
  rw [linePullbackMap, Equiv.apply_symm_apply, Equiv.apply_symm_apply,
    Adjunction.homEquiv_naturality_right]
  have hforget :
      (sheafCompose T.smallEtaleTopology
        (forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1})).map
        ((Etale.lowerStar (ModuleCat.{u + 1} A) v).map g) =
      (Etale.lowerStar AddCommGrpCat.{u + 1} v).map
        ((sheafCompose T'.smallEtaleTopology
          (forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1})).map g) := rfl
  rw [Category.assoc, hforget, ← Functor.map_comp]
  rw [← lineHomEquiv_comp]
  rw [Category.id_comp]

private lemma linePullbackMap_isIso
    (A : Type (u + 1)) [CommRing A] (m : ℕ) (hm : 0 < m) (hA : (m : A) = 0)
    {T T' : Scheme.{u}} (v : T' ⟶ T) (hT : IsUnit (m : Γ(T, ⊤))) :
    IsIso (linePullbackMap A m hA v) := by
  have : NeZero m := ⟨Nat.ne_of_gt hm⟩
  have := isIso_upperStarRootsOfUnitySheafToRootsOfUnitySheaf_of_isUnit m v hT
  apply isIso_of_coyoneda_map_bijective
  intro P
  let e := (lineHomEquiv T' m A hA P).trans
    ((Iso.homCongr (asIso (upperStarRootsOfUnitySheafToRootsOfUnitySheaf m v)).symm
      (Iso.refl _)).trans
        (((Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} v).homEquiv _ _).trans
          ((lineHomEquiv T m A hA
            ((Etale.lowerStar (ModuleCat.{u + 1} A) v).obj P)).symm.trans
              ((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) v).homEquiv _ _).symm)))
  suffices (fun g : finiteEtaleTateLine T' m A hA ⟶ P ↦ linePullbackMap A m hA v ≫ g) = e by
    rw [this]
    exact e.bijective
  funext g
  apply ((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) v).homEquiv _ _).injective
  apply (lineHomEquiv T m A hA _).injective
  simp only [e, Equiv.trans_apply, Equiv.apply_symm_apply, Iso.homCongr_apply,
    Iso.symm_inv, asIso_hom, Iso.refl_hom, Category.comp_id]
  exact (linePullbackMap_comp A m hA v P g).trans
    ((lineHomEquiv T m A hA
      ((Etale.lowerStar (ModuleCat.{u + 1} A) v).obj P)).apply_symm_apply _).symm

private lemma transpose_composite
    (D : Type u') [Category.{u + 1} D] [Abelian D]
    [IsGrothendieckAbelian.{u + 1} D]
    {T T' T'' : Scheme.{u}} (v : T' ⟶ T) (w : T'' ⟶ T')
    {X : Sheaf T.smallEtaleTopology D} {Y : Sheaf T'.smallEtaleTopology D}
    {Z : Sheaf T''.smallEtaleTopology D}
    (f : (Etale.upperStar D v).obj X ⟶ Y)
    (g : (Etale.upperStar D w).obj Y ⟶ Z) :
    (Etale.upperStarLowerStarAdjunction D (w ≫ v)).homEquiv _ _
      ((Etale.upperStarComp D w v).hom.app X ≫ (Etale.upperStar D w).map f ≫ g) =
    (Etale.upperStarLowerStarAdjunction D v).homEquiv _ _ f ≫
      (Etale.lowerStar D v).map
        ((Etale.upperStarLowerStarAdjunction D w).homEquiv _ _ g) ≫
      (Etale.lowerStarComp D w v).hom.app Z := by
  simp only [Adjunction.homEquiv_unit]
  rw [Functor.map_comp, reassoc_of% (Etale.upperStarComp_hom_app_unit_app D w v X),
    ← (Etale.lowerStarComp D w v).hom.naturality]
  have hn := (Etale.upperStarLowerStarAdjunction D w).unit.naturality f
  simp only [Adjunction.comp_unit_app, Functor.comp_map, Functor.map_comp,
    Functor.id_map, Category.assoc] at hn ⊢
  simp only [← Functor.map_comp_assoc (Etale.lowerStar D v)]
  rw [← reassoc_of% hn]

private lemma linePullbackMap_composition
    (A : Type (u + 1)) [CommRing A] (m : ℕ) (hA : (m : A) = 0)
    {T T' T'' : Scheme.{u}} (v : T' ⟶ T) (w : T'' ⟶ T') :
    (Etale.upperStarComp (ModuleCat.{u + 1} A) w v).hom.app
        (finiteEtaleTateLine T m A hA) ≫
      (Etale.upperStar (ModuleCat.{u + 1} A) w).map (linePullbackMap A m hA v) ≫
        linePullbackMap A m hA w = linePullbackMap A m hA (w ≫ v) := by
  apply ((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) (w ≫ v)).homEquiv
    _ _).injective
  apply (lineHomEquiv T m A hA _).injective
  rw [transpose_composite (ModuleCat.{u + 1} A) v w]
  rw [← Category.assoc, ← Adjunction.homEquiv_naturality_right]
  rw [lineHomEquiv_comp, linePullbackMap_comp]
  have hw := linePullbackMap_comp A m hA w (finiteEtaleTateLine T'' m A hA) (𝟙 _)
  simp only [Category.comp_id] at hw
  rw [hw]
  conv_rhs => rw [linePullbackMap, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  rw [← upperStarRootsOfUnitySheafToRootsOfUnitySheaf_comp m w v]
  rw [Adjunction.homEquiv_naturality_right, transpose_composite AddCommGrpCat.{u + 1} v w,
    Adjunction.homEquiv_naturality_right]
  simp only [Functor.map_comp, Category.assoc]
  have hforget :
      (sheafCompose T.smallEtaleTopology
        (forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1})).map
          ((Etale.lowerStarComp (ModuleCat.{u + 1} A) w v).hom.app
            (finiteEtaleTateLine T'' m A hA)) =
        (Etale.lowerStarComp AddCommGrpCat.{u + 1} w v).hom.app
          ((sheafCompose T''.smallEtaleTopology
            (forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1})).obj
              (finiteEtaleTateLine T'' m A hA)) := rfl
  rw [hforget]
  exact congrArg (fun f ↦ _ ≫ _ ≫ f)
    ((Etale.lowerStarComp AddCommGrpCat.{u + 1} w v).hom.naturality
      (lineHomEquiv T'' m A hA _ (𝟙 _)))

private lemma linePullbackMap_composition_eq
    (A : Type (u + 1)) [CommRing A] (m : ℕ) (hA : (m : A) = 0)
    {T T' T'' : Scheme.{u}} (v : T' ⟶ T) (w : T'' ⟶ T') (wv : T'' ⟶ T)
    (h : wv = w ≫ v) :
    (Etale.upperStarComp (ModuleCat.{u + 1} A) w v wv h).hom.app
        (finiteEtaleTateLine T m A hA) ≫
      (Etale.upperStar (ModuleCat.{u + 1} A) w).map (linePullbackMap A m hA v) ≫
        linePullbackMap A m hA w = linePullbackMap A m hA wv := by
  subst h
  exact linePullbackMap_composition A m hA v w

private lemma linePullbackMap_identity
    (A : Type (u + 1)) [CommRing A] (m : ℕ) (hm : 0 < m) (hA : (m : A) = 0)
    (T : Scheme.{u}) (hT : IsUnit (m : Γ(T, ⊤))) :
    linePullbackMap A m hA (𝟙 T) =
      (Etale.upperStarId (ModuleCat.{u + 1} A) T).hom.app (finiteEtaleTateLine T m A hA) := by
  have := linePullbackMap_isIso A m hm hA (𝟙 T) hT
  have hc := linePullbackMap_composition_eq A m hA (𝟙 T) (𝟙 T) (𝟙 T)
    (Category.id_comp _).symm
  let F := Etale.upperStar (ModuleCat.{u + 1} A) (𝟙 T)
  let s := Etale.upperStarId (ModuleCat.{u + 1} A) T
  let X := finiteEtaleTateLine T m A hA
  let f := linePullbackMap A m hA (𝟙 T)
  have hmap : s.inv.app (F.obj X) ≫ F.map f ≫ f = f := by
    have hi := Etale.upperStarComp_id_left (ModuleCat.{u + 1} A) (𝟙 T)
    have hi' := congrArg (fun i ↦ i.hom.app X) hi
    have h := congrArg (fun t ↦ t ≫ F.map f ≫ f) hi'
    simpa only [Iso.trans_hom, NatTrans.comp_app, Iso.symm_hom,
      Functor.isoWhiskerLeft_hom, Functor.rightUnitor_inv_app, Category.id_comp,
      Functor.whiskerLeft_app] using h.symm.trans hc
  have hn := s.inv.naturality f
  change f ≫ s.inv.app X = s.inv.app (F.obj X) ≫ F.map f at hn
  rw [← Category.assoc, ← hn, Category.assoc] at hmap
  have he : s.inv.app X ≫ f = 𝟙 _ := by
    apply (cancel_epi f).mp
    exact hmap.trans (Category.comp_id _).symm
  calc
    f = s.hom.app X ≫ s.inv.app X ≫ f := by simp
    _ = s.hom.app X := by rw [he, Category.comp_id]

/-- The Tate-line inverse-image comparison, normalized on pure tensors, with identity
and composition compatibility. The scalar-extension adjunction carries the roots comparison
to this map; its Hom equivalences prove invertibility. Naturality of adjunction units gives
composition and the unit law then gives the identity.
Source: Stacks Project, Tags 03PK and 03Q1.
(auxiliary; not a blueprint node). -/
theorem finiteEtaleTateLine_pullback_normalized
    (A : Type (u + 1)) [CommRing A] (m : ℕ) (hm : 0 < m) (hA : (m : A) = 0) :
    ∃ c : ∀ {T T' : Scheme.{u}} (v : T' ⟶ T), IsUnit (m : Γ(T, ⊤)) →
        ((Etale.upperStar (ModuleCat.{u + 1} A) v).obj (finiteEtaleTateLine T m A hA) ≅
          finiteEtaleTateLine T' m A hA),
      (∀ {T T' : Scheme.{u}} (v : T' ⟶ T) (hT : IsUnit (m : Γ(T, ⊤)))
          (W : T.Etaleᵒᵖ) (a : A) (z : (T.rootsOfUnitySheaf m).obj.obj W),
        ((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) v).homEquiv _ _
          (c v hT).hom).hom.app W (finiteEtaleTateOneGenerator A m T hA W a z) =
        finiteEtaleTateOneGenerator A m T' hA
          ((MorphismProperty.Over.pullback @Etale ⊤ v).op.obj W) a
          (((Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} v).homEquiv _ _
            (upperStarRootsOfUnitySheafToRootsOfUnitySheaf m v)).hom.app W z)) ∧
      (∀ (T : Scheme.{u}) (hT : IsUnit (m : Γ(T, ⊤))), c (𝟙 T) hT =
        (Etale.upperStarId (ModuleCat.{u + 1} A) T).app (finiteEtaleTateLine T m A hA)) ∧
      (∀ {T T' T'' : Scheme.{u}} (v : T' ⟶ T) (w : T'' ⟶ T')
          (hT : IsUnit (m : Γ(T, ⊤))) (hT' : IsUnit (m : Γ(T', ⊤))),
        c (w ≫ v) hT = (Etale.upperStarComp (ModuleCat.{u + 1} A) w v).app _ ≪≫
          (Etale.upperStar (ModuleCat.{u + 1} A) w).mapIso (c v hT) ≪≫ c w hT') := by
  let c {T T' : Scheme.{u}} (v : T' ⟶ T) (hT : IsUnit (m : Γ(T, ⊤))) :=
    letI := linePullbackMap_isIso A m hm hA v hT
    asIso (linePullbackMap A m hA v)
  refine ⟨@c, ?_, ?_, ?_⟩
  · exact fun v hT W a z ↦ linePullbackMap_generator A m hA v W a z
  · intro T hT
    exact Iso.ext (linePullbackMap_identity A m hm hA T hT)
  · intro T T' T'' v w hT hT'
    exact Iso.ext (linePullbackMap_composition A m hA v w).symm

end AlgebraicGeometry.Scheme
