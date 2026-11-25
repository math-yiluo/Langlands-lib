/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import Mathlib.Algebra.Homology.Embedding.ExtendHomotopy
public import WeilConjectures.AlgebraicGeometry.AbelianCounitResolutionCalculation
import WeilConjectures.Algebra.Homology.KInjectiveResolution

@[expose] public section
universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite
noncomputable section
namespace AlgebraicGeometry.Scheme.Modules.ExtEdgeResolution

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem lift_to_nat_injective
    {C : Type*} [Category C] [Abelian C]
    {A B R : CochainComplex C ℕ} [∀ n, Injective (R.X n)]
    (l : A ⟶ B) [QuasiIso l] (r : A ⟶ R) :
    ∃ k : B ⟶ R, Nonempty (Homotopy (l ≫ k) r) := by
  let e := ComplexShape.embeddingUpNat
  let q := HomotopyCategory.quotient C (.up ℤ)
  let R' : CochainComplex C ℤ := R.extend e
  let : R'.IsKInjective := CochainComplex.isKInjective_of_injective R' 0
  let := HasDerivedCategory.standard C
  have hbij := CochainComplex.IsKInjective.bijective_quotient_map_comp (J := R')
      (HomologicalComplex.extendMap l e)
  obtain ⟨k, hk⟩ := hbij.surjective (q.map (HomologicalComplex.extendMap r e))
  obtain ⟨k, rfl⟩ := q.map_surjective k
  obtain ⟨k, rfl⟩ := (e.extendFunctor C).map_surjective k
  refine ⟨k, ⟨Homotopy.ofExtend (e := e) (HomotopyCategory.homotopyOfEq _ _ ?_)⟩⟩
  simpa only [HomologicalComplex.extendMap_comp, Functor.map_comp,
    ComplexShape.Embedding.extendFunctor_map] using hk

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem homotopy_of_comp_nat_injective
    {C : Type*} [Category C] [Abelian C]
    {A B R : CochainComplex C ℕ} [∀ n, Injective (R.X n)]
    (l : A ⟶ B) [QuasiIso l] (r s : B ⟶ R)
    (h : Nonempty (Homotopy (l ≫ r) (l ≫ s))) : Nonempty (Homotopy r s) := by
  let e := ComplexShape.embeddingUpNat
  let q := HomotopyCategory.quotient C (.up ℤ)
  let R' : CochainComplex C ℤ := R.extend e
  let : R'.IsKInjective := CochainComplex.isKInjective_of_injective R' 0
  let := HasDerivedCategory.standard C
  have hbij := CochainComplex.IsKInjective.bijective_quotient_map_comp (J := R')
      (HomologicalComplex.extendMap l e)
  refine ⟨Homotopy.ofExtend (e := e) (HomotopyCategory.homotopyOfEq _ _ ?_)⟩
  apply hbij.injective
  simpa only [HomologicalComplex.extendMap_comp, Functor.map_comp] using
    HomotopyCategory.eq_of_homotopy _ _ (h.some.extend e)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem single_map_inv_f_zero
    {C D : Type*} [Category C] [Category D]
    [HasZeroMorphisms C] [HasZeroMorphisms D] [HasZeroObject C] [HasZeroObject D]
    (G : C ⥤ D) [G.PreservesZeroMorphisms] (M : C) :
    ((HomologicalComplex.singleMapHomologicalComplex G (.up ℕ) 0).inv.app M).f 0 =
      𝟙 (G.obj M) := by
  rw [HomologicalComplex.singleMapHomologicalComplex_inv_app_self]
  dsimp [HomologicalComplex.singleObjXSelf, HomologicalComplex.singleObjXIsoOfEq]
  simp only [Category.id_comp]
  exact G.map_id M

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem forgotten_augmentation_f_zero (X : Scheme.{u})
    {F : X.Modules} (I : InjectiveResolution F) :
    (forgottenAugmentation X I).f 0 =
      (SheafOfModules.toSheaf (moduleRings X.toRingedSpace)).map (I.ι.f 0) := by
  simp only [forgottenAugmentation, HomologicalComplex.comp_f, single_map_inv_f_zero,
    Functor.mapHomologicalComplex_map_f]
  exact Category.id_comp _

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem counit_source_augmentation_f_zero {X Y : Scheme.{u}} (f : X ⟶ Y)
    (F : X.Modules) (J : InjectiveResolution ((pushforward f).obj F)) :
    (counitSourceAugmentation f F J).f 0 =
      (invImage f).map
        ((SheafOfModules.toSheaf (moduleRings Y.toRingedSpace)).map (J.ι.f 0)) := by
  simp only [counitSourceAugmentation, HomologicalComplex.comp_f, single_map_inv_f_zero,
    Functor.mapHomologicalComplex_map_f, forgotten_augmentation_f_zero]
  exact Category.id_comp _

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem forgotten_resolution_augmentation_f_zero (X : Scheme.{u})
    {F : X.Modules} (I : InjectiveResolution F) :
    (SheafOfModules.toSheaf (moduleRings X.toRingedSpace)).map (I.ι.f 0) ≫
      (forgottenResolutionMap X I).f 0 = (standardAbelianResolution X F).ι.f 0 := by
  have h := congrArg (fun g ↦ g.f 0)
    (InjectiveResolution.descOfQuasiIso_commutes
      (𝟙 _) (standardAbelianResolution X F) (forgottenAugmentation X I))
  simp only [HomologicalComplex.comp_f, forgotten_augmentation_f_zero,
    CochainComplex.single₀_map_f_zero] at h
  unfold forgottenResolutionMap
  exact h.trans (Category.id_comp _)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem counit_adjoint_augmentation_f_zero {X Y : Scheme.{u}} (f : X ⟶ Y)
    (F : X.Modules) (J : InjectiveResolution ((pushforward f).obj F)) :
    (SheafOfModules.toSheaf (moduleRings Y.toRingedSpace)).map (J.ι.f 0) ≫
      (counitResolutionAdjoint f F J).f 0 =
        (abelianPushforward f).map ((standardAbelianResolution X F).ι.f 0) := by
  let T := SheafOfModules.toSheaf (moduleRings Y.toRingedSpace)
  let G := abelianPushforward f
  have h := congrArg (fun g ↦ g.f 0)
    (InjectiveResolution.descOfQuasiIso_commutes
      (coeff f (𝟙 ((pushforward f).obj F))) (standardAbelianResolution X F)
      (counitSourceAugmentation f F J))
  have hLift : (invImage f).map (T.map (J.ι.f 0)) ≫ (counitResolutionLift f F J).f 0 =
      coeff f (𝟙 ((pushforward f).obj F)) ≫ (standardAbelianResolution X F).ι.f 0 := by
    simpa only [counitResolutionLift, HomologicalComplex.comp_f,
      counit_source_augmentation_f_zero, CochainComplex.single₀_map_f_zero] using h
  have hCoeff : (abelianAdjunction f).unit.app (T.obj ((pushforward f).obj F)) ≫
      G.map (coeff f (𝟙 ((pushforward f).obj F))) = 𝟙 _ := by
    exact ((abelianAdjunction f).homEquiv _ _).apply_symm_apply (𝟙 _)
  unfold counitResolutionAdjoint
  change T.map (J.ι.f 0) ≫ (abelianAdjunction f).unit.app (T.obj (J.cocomplex.X 0)) ≫
    G.map ((counitResolutionLift f F J).f 0) =
      G.map ((standardAbelianResolution X F).ι.f 0)
  have hn := (abelianAdjunction f).unit.naturality (T.map (J.ι.f 0))
  change T.map (J.ι.f 0) ≫ (abelianAdjunction f).unit.app (T.obj (J.cocomplex.X 0)) =
    (abelianAdjunction f).unit.app (T.obj ((pushforward f).obj F)) ≫
      G.map ((invImage f).map (T.map (J.ι.f 0))) at hn
  rw [← Category.assoc, hn, Category.assoc]
  rw [← G.map_comp, hLift, G.map_comp, ← Category.assoc, hCoeff]
  exact Category.id_comp _

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The first comparison construction, before the second homotopy is imposed.
The proof lifts into the bounded-below injective direct-image resolution using
K-injective comparison after extension by zero, then reflects homotopies across
the forgotten augmentation and applies sections.
Source: Stacks Project, Tags 013P and 013S.
(blueprint: new-abelian-replacement-section-homotopies-core-counit) -/
theorem exists_section_map_with_counit_homotopy {X Y : Scheme.{u}} (f : X ⟶ Y)
    {F : X.Modules} (I : InjectiveResolution F)
    (J : InjectiveResolution ((pushforward f).obj F)) (K : CochainComplex Y.Modules ℕ)
    (l : ((pushforward f).mapHomologicalComplex (.up ℕ)).obj I.cocomplex ⟶ K)
    (hl : QuasiIso l) (β : J.cocomplex ⟶ K)
    (hβ : J.ι.f 0 ≫ β.f 0 = (pushforward f).map (I.ι.f 0) ≫ l.f 0)
    (a : ((moduleSections X).mapHomologicalComplex (.up ℕ)).obj I.cocomplex ≅
      ((moduleSections Y).mapHomologicalComplex (.up ℕ)).obj
        (((pushforward f).mapHomologicalComplex (.up ℕ)).obj I.cocomplex))
    (ha : ∀ n : ℕ, a.inv.f n = (presheaf (I.cocomplex.X n)).map
      (eqToHom (by simp) : (⊤ : X.Opens) ⟶ f ⁻¹ᵁ (⊤ : Y.Opens)).op) :
    ∃ q : ((moduleSections Y).mapHomologicalComplex (.up ℕ)).obj K ⟶
        ((abelianSections X).mapHomologicalComplex (.up ℕ)).obj
          (standardAbelianResolution X F).cocomplex,
      Nonempty (Homotopy
        (((moduleSections Y).mapHomologicalComplex (.up ℕ)).map β ≫ q)
        (counitSectionMap f F J)) := by
  have _ := ha 0
  let G := abelianPushforward f
  let : G.Additive := ⟨by intros; ext U x; rfl⟩
  let T := SheafOfModules.toSheaf (moduleRings Y.toRingedSpace)
  let R := (standardAbelianResolution X F).cocomplex
  let L := (T.mapHomologicalComplex (.up ℕ)).map l
  let r : (T.mapHomologicalComplex (.up ℕ)).obj
      (((pushforward f).mapHomologicalComplex (.up ℕ)).obj I.cocomplex) ⟶
      (G.mapHomologicalComplex (.up ℕ)).obj R :=
    (G.mapHomologicalComplex (.up ℕ)).map (forgottenResolutionMap X I)
  let : ∀ n, Injective (((G.mapHomologicalComplex (.up ℕ)).obj R).X n) :=
    fun n ↦ (abelianAdjunction f).map_injective _ inferInstance
  let : QuasiIso l := hl
  obtain ⟨k, hk⟩ := lift_to_nat_injective L r
  let b := (T.mapHomologicalComplex (.up ℕ)).map β
  have hb : Nonempty (Homotopy (b ≫ k) (counitResolutionAdjoint f F J)) := by
    apply homotopy_of_comp_nat_injective (forgottenAugmentation Y J)
    let d := (HomologicalComplex.singleMapHomologicalComplex G (.up ℕ) 0).inv.app
      ((SheafOfModules.toSheaf (moduleRings X.toRingedSpace)).obj F) ≫
        (G.mapHomologicalComplex (.up ℕ)).map (forgottenAugmentation X I)
    have hp : forgottenAugmentation Y J ≫ b = d ≫ L := by
      apply HomologicalComplex.from_single_hom_ext
      simp only [HomologicalComplex.comp_f, forgotten_augmentation_f_zero, d, b, L,
        single_map_inv_f_zero, Functor.mapHomologicalComplex_map_f]
      change T.map (J.ι.f 0) ≫ T.map (β.f 0) =
        T.map ((pushforward f).map (I.ι.f 0)) ≫ T.map (l.f 0)
      simpa only [← Functor.map_comp] using congrArg T.map hβ
    have hc : forgottenAugmentation Y J ≫ counitResolutionAdjoint f F J = d ≫ r := by
      apply HomologicalComplex.from_single_hom_ext
      simp only [HomologicalComplex.comp_f, forgotten_augmentation_f_zero, d, r,
        single_map_inv_f_zero, Functor.mapHomologicalComplex_map_f]
      change T.map (J.ι.f 0) ≫ (counitResolutionAdjoint f F J).f 0 =
        G.map ((SheafOfModules.toSheaf (moduleRings X.toRingedSpace)).map (I.ι.f 0)) ≫
          G.map ((forgottenResolutionMap X I).f 0)
      exact (counit_adjoint_augmentation_f_zero f F J).trans
        ((congrArg G.map (forgotten_resolution_augmentation_f_zero X I)).symm.trans
          (G.map_comp _ _))
    refine ⟨(Homotopy.ofEq ?_).trans ((hk.some.compLeft d).trans (Homotopy.ofEq hc.symm))⟩
    simpa only [Category.assoc] using congrArg (fun z ↦ z ≫ k) hp
  let t := (NatTrans.mapHomologicalComplex (abelianPushforwardSectionsIso f).hom
    (.up ℕ)).app R
  let q := ((abelianSections Y).mapHomologicalComplex (.up ℕ)).map k ≫ t
  refine ⟨q, ⟨?_⟩⟩
  have h := ((abelianSections Y).mapHomotopy hb.some).compRight t
  unfold counitSectionMap
  convert h using 1 <;> rfl


set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
-- Comparing the composed section functors unfolds the concrete sheaf categories.
/-- Construct one section map carrying both comparison homotopies, uniformly in the
compatible section isomorphism a. The map q is chosen before a is given.
Proof: Lift the forgotten resolution map across the forgotten l into the injective
complex f_*R, obtaining k and a lifting homotopy as in the first proof. Augmentation
compatibility and homotopy reflection across the forgotten augmentation of J give
T_Y(β) ≫ k homotopic to the counit adjoint. Set q to sections of this same k followed
by the direct-image section comparison, giving the counit homotopy. Apply sections
to the same lifting homotopy; naturality of the direct-image section comparison
and ha identify its ends with Γ(l) ≫ q and a.inv ≫ Γ(forgottenResolutionMap).
Precompose with a.hom and cancel a.hom ≫ a.inv to obtain the second homotopy.
No arbitrary witness of the first theorem is selected. The construction applies
also to zero complexes, zero coefficients and empty schemes.
Source: Stacks Project, Tags 013P and 013S.
(blueprint: new-abelian-replacement-section-homotopies-core-second) -/
theorem second_section_homotopy_of_counit {X Y : Scheme.{u}} (f : X ⟶ Y)
    {F : X.Modules} (I : InjectiveResolution F)
    (J : InjectiveResolution ((pushforward f).obj F)) (K : CochainComplex Y.Modules ℕ)
    (l : ((pushforward f).mapHomologicalComplex (.up ℕ)).obj I.cocomplex ⟶ K)
    (hl : QuasiIso l) (β : J.cocomplex ⟶ K)
    (hβ : J.ι.f 0 ≫ β.f 0 = (pushforward f).map (I.ι.f 0) ≫ l.f 0) :
    ∃ q : ((moduleSections Y).mapHomologicalComplex (.up ℕ)).obj K ⟶
        ((abelianSections X).mapHomologicalComplex (.up ℕ)).obj
          (standardAbelianResolution X F).cocomplex,
      Nonempty (Homotopy
        (((moduleSections Y).mapHomologicalComplex (.up ℕ)).map β ≫ q)
        (counitSectionMap f F J)) ∧
      ∀ (a : ((moduleSections X).mapHomologicalComplex (.up ℕ)).obj I.cocomplex ≅
          ((moduleSections Y).mapHomologicalComplex (.up ℕ)).obj
            (((pushforward f).mapHomologicalComplex (.up ℕ)).obj I.cocomplex))
        (_ha : ∀ n : ℕ, a.inv.f n = (presheaf (I.cocomplex.X n)).map
          (eqToHom (by simp) : (⊤ : X.Opens) ⟶ f ⁻¹ᵁ (⊤ : Y.Opens)).op),
      Nonempty (Homotopy
        ((a.hom ≫ ((moduleSections Y).mapHomologicalComplex (.up ℕ)).map l) ≫ q)
        (((abelianSections X).mapHomologicalComplex (.up ℕ)).map
          (forgottenResolutionMap X I))) := by
  let G := abelianPushforward f
  let : G.Additive := ⟨by intros; ext U x; rfl⟩
  let T := SheafOfModules.toSheaf (moduleRings Y.toRingedSpace)
  let R := (standardAbelianResolution X F).cocomplex
  let L := (T.mapHomologicalComplex (.up ℕ)).map l
  let r : (T.mapHomologicalComplex (.up ℕ)).obj
      (((pushforward f).mapHomologicalComplex (.up ℕ)).obj I.cocomplex) ⟶
      (G.mapHomologicalComplex (.up ℕ)).obj R :=
    (G.mapHomologicalComplex (.up ℕ)).map (forgottenResolutionMap X I)
  let : ∀ n, Injective (((G.mapHomologicalComplex (.up ℕ)).obj R).X n) :=
    fun n ↦ (abelianAdjunction f).map_injective _ inferInstance
  let : QuasiIso l := hl
  obtain ⟨k, hk⟩ := lift_to_nat_injective L r
  let b := (T.mapHomologicalComplex (.up ℕ)).map β
  have hb : Nonempty (Homotopy (b ≫ k) (counitResolutionAdjoint f F J)) := by
    apply homotopy_of_comp_nat_injective (forgottenAugmentation Y J)
    let d := (HomologicalComplex.singleMapHomologicalComplex G (.up ℕ) 0).inv.app
      ((SheafOfModules.toSheaf (moduleRings X.toRingedSpace)).obj F) ≫
        (G.mapHomologicalComplex (.up ℕ)).map (forgottenAugmentation X I)
    have hp : forgottenAugmentation Y J ≫ b = d ≫ L := by
      apply HomologicalComplex.from_single_hom_ext
      simp only [HomologicalComplex.comp_f, forgotten_augmentation_f_zero, d, b, L,
        single_map_inv_f_zero, Functor.mapHomologicalComplex_map_f]
      change T.map (J.ι.f 0) ≫ T.map (β.f 0) =
        T.map ((pushforward f).map (I.ι.f 0)) ≫ T.map (l.f 0)
      simpa only [← Functor.map_comp] using congrArg T.map hβ
    have hc : forgottenAugmentation Y J ≫ counitResolutionAdjoint f F J = d ≫ r := by
      apply HomologicalComplex.from_single_hom_ext
      simp only [HomologicalComplex.comp_f, forgotten_augmentation_f_zero, d, r,
        single_map_inv_f_zero, Functor.mapHomologicalComplex_map_f]
      change T.map (J.ι.f 0) ≫ (counitResolutionAdjoint f F J).f 0 =
        G.map ((SheafOfModules.toSheaf (moduleRings X.toRingedSpace)).map (I.ι.f 0)) ≫
          G.map ((forgottenResolutionMap X I).f 0)
      exact (counit_adjoint_augmentation_f_zero f F J).trans
        ((congrArg G.map (forgotten_resolution_augmentation_f_zero X I)).symm.trans
          (G.map_comp _ _))
    refine ⟨(Homotopy.ofEq ?_).trans ((hk.some.compLeft d).trans (Homotopy.ofEq hc.symm))⟩
    simpa only [Category.assoc] using congrArg (fun z ↦ z ≫ k) hp
  let t := (NatTrans.mapHomologicalComplex (abelianPushforwardSectionsIso f).hom
    (.up ℕ)).app R
  let q := ((abelianSections Y).mapHomologicalComplex (.up ℕ)).map k ≫ t
  refine ⟨q, ?_, ?_⟩
  · refine ⟨?_⟩
    have h := ((abelianSections Y).mapHomotopy hb.some).compRight t
    unfold counitSectionMap
    convert h using 1 <;> rfl
  · intro a ha
    have h := (((abelianSections Y).mapHomotopy hk.some).compRight t).compLeft a.hom
    have he :
        ((abelianSections Y).mapHomologicalComplex (.up ℕ)).map r ≫ t =
          a.inv ≫ ((abelianSections X).mapHomologicalComplex (.up ℕ)).map
            (forgottenResolutionMap X I) := by
      apply HomologicalComplex.hom_ext
      intro n
      simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f, ha]
      exact (((forgottenResolutionMap X I).f n).hom.naturality
        (eqToHom (by simp) : (⊤ : X.Opens) ⟶ f ⁻¹ᵁ (⊤ : Y.Opens)).op).symm
    refine ⟨?_⟩
    convert h using 1
    · change (a.hom ≫ ((moduleSections Y).mapHomologicalComplex (.up ℕ)).map l) ≫
          (((abelianSections Y).mapHomologicalComplex (.up ℕ)).map k ≫ t) = _
      rw [Functor.map_comp]
      simp only [Category.assoc]
      rfl
    · rw [he, ← Category.assoc, a.hom_inv_id, Category.id_comp]


end AlgebraicGeometry.Scheme.Modules.ExtEdgeResolution
