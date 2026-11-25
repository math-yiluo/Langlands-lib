/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.LocalExtendedCechDescription
public import WeilConjectures.CategoryTheory.LocallyDerivedRingedIdealComplete
public import WeilConjectures.CategoryTheory.RingedCompletionUnit
import Mathlib.CategoryTheory.Sites.LocalProperties
import WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationNaturality
import WeilConjectures.AlgebraicGeometry.ExtendedCechCompleteUnitCriterion
import WeilConjectures.AlgebraicGeometry.FiniteIdealGeneratingCover
import WeilConjectures.CategoryTheory.RingedCechCompletionUnitIdempotence

/-!
# Core reflector properties for the extended Cech completion

Source: Stacks Project, algebraization.tex, Tags 099B and 099F
(auxiliary; not a blueprint node).

The remaining finite localization-filtration and orthogonality argument is isolated here.
-/

@[expose] public noncomputable section

universe u w

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

private def homUnitOnRepresentatives
    {A D : Type*} [Category A] [Category D]
    (Q : A ⥤ D) (I : A ⥤ A) (eta : 𝟭 A ⟶ I)
    (H : Aᵒᵖ ⥤ A ⥤ A) (G : Dᵒᵖ × D ⥤ D) (U : A)
    (a : H.obj (op U) ≅ 𝟭 A)
    (c : Q.op.prod Q ⋙ G ≅ (𝟭 Aᵒᵖ).prod I ⋙ Functor.uncurry.obj H ⋙ Q) :
    Q ⋙ 𝟭 D ⟶ Q ⋙ (Functor.curry.obj G).obj (op (Q.obj U)) where
  app M := Q.map (eta.app M) ≫ Q.map (a.inv.app (I.obj M)) ≫ c.inv.app (op U, M)
  naturality {M N} f := by
    have hc := c.inv.naturality (X := (op U, M)) (Y := (op U, N)) (𝟙 _, f)
    have ha := a.inv.naturality (I.map f)
    have he := eta.naturality f
    dsimp only [Functor.comp_map, Functor.prod_map, Functor.id_map, Functor.op_map,
      Functor.curry_obj_obj_map, Functor.uncurry_obj_map] at hc ha he ⊢
    dsimp only [Functor.prod_obj, Functor.id_obj] at hc
    simp only [Functor.map_id, NatTrans.id_app, Category.id_comp, op_id, unop_id] at hc
    have he' : Q.map f ≫ Q.map (eta.app N) = Q.map (eta.app M) ≫ Q.map (I.map f) := by
      simpa only [← Q.map_comp] using congrArg Q.map he
    have ha' : Q.map (I.map f) ≫ Q.map (a.inv.app (I.obj N)) =
        Q.map (a.inv.app (I.obj M)) ≫ Q.map ((H.obj (op U)).map (I.map f)) := by
      simpa only [← Q.map_comp] using congrArg Q.map ha
    rw [← Category.assoc, he']
    simp only [Category.assoc]
    rw [← Category.assoc (Q.map (I.map f)), ha']
    simp only [Category.assoc]
    rw [hc]

-- Naturality compares the product-localization factorization with chosen representatives.
private theorem completion_unit_natural_core
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u})
    [HasDerivedCategory.{w} (ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))]
    (K : ringedSiteComplex O) (ε : K ⟶ ringedSiteRingComplex O)
    (E E' : ringedSiteDerived O) (g : E ⟶ E') :
    ringedCechCompletionUnit O K ε E ≫ (ringedCechCompletionFunctor O K).map g =
      g ≫ ringedCechCompletionUnit O K ε E' := by
  let A := ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)
  let : IsGrothendieckAbelian.{u} A := SheafOfModules.isGrothendieckAbelian _
  let Q := DerivedCategory.Q (C := A)
  let I := CochainComplex.kInjectiveResolutionFunctor.{u} A
  let η := CochainComplex.toKInjectiveResolution.{u} A
  let H := derivedInternalHom J O
  let F := ringedCechCompletionFunctor O (ringedSiteRingComplex O)
  let c := Localization.fac
    ((𝟭 _).prod I ⋙ Functor.uncurry.obj (homComplexFunctor (R := O)) ⋙ Q)
    (derivedInternalHom_inverts J O I η (fun M ↦
      ⟨(CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{u} _ M).2,
        CochainComplex.isKInjective_kInjectiveResolutionFunctor_obj.{u} _ M⟩))
    (Q.op.prod Q)
  let a : (homComplexFunctor (R := O)).obj
      (Opposite.op (ringedSiteRingComplex O)) ≅ 𝟭 _ :=
    NatIso.ofComponents (ringedHomUnitEvaluationIso O) (by
      intro M N f
      apply HomologicalComplex.hom_ext
      intro n
      exact homComplex_unit_evaluation_naturality J O f n)
  let t : Q ⋙ 𝟭 _ ⟶ Q ⋙ F :=
    homUnitOnRepresentatives Q I η (homComplexFunctor (R := O))
      H (ringedSiteRingComplex O) a c
  let W := HomologicalComplex.quasiIso A (ComplexShape.up ℤ)
  let full := Localization.fullyFaithfulWhiskeringLeft Q W (DerivedCategory A)
  let d : 𝟭 (DerivedCategory A) ⟶ F := full.preimage t
  have hd (M : CochainComplex A ℤ) : d.app (Q.obj M) = t.app M :=
    congrArg (fun z ↦ z.app M) (full.map_preimage t)
  have hu (X : ringedSiteDerived O) : ringedDerivedHomUnit O X = d.app X := by
    let e := Q.objObjPreimageIso X
    have hn := d.naturality e.hom
    dsimp at hn
    rw [← cancel_epi e.hom]
    rw [hn, hd]
    simp only [ringedDerivedHomUnit, t, homUnitOnRepresentatives, a, e, Q, I, η, c,
      Category.assoc, Iso.hom_inv_id_assoc]
    rfl
  have hn := d.naturality g
  change (ringedDerivedHomUnit O E ≫ H.map
      (X := (Opposite.op (Q.obj (ringedSiteRingComplex O)), E))
      (Y := (Opposite.op (Q.obj K), E)) ((Q.map ε).op, 𝟙 E)) ≫
      H.map (X := (Opposite.op (Q.obj K), E))
        (Y := (Opposite.op (Q.obj K), E')) (𝟙 _, g) =
    g ≫ ringedDerivedHomUnit O E' ≫ H.map
      (X := (Opposite.op (Q.obj (ringedSiteRingComplex O)), E'))
      (Y := (Opposite.op (Q.obj K), E')) ((Q.map ε).op, 𝟙 E')
  have hs : H.map
      (X := (Opposite.op (Q.obj (ringedSiteRingComplex O)), E))
      (Y := (Opposite.op (Q.obj K), E)) ((Q.map ε).op, 𝟙 E) ≫
      H.map (X := (Opposite.op (Q.obj K), E))
        (Y := (Opposite.op (Q.obj K), E')) (𝟙 _, g) =
      H.map (X := (Opposite.op (Q.obj (ringedSiteRingComplex O)), E))
        (Y := (Opposite.op (Q.obj (ringedSiteRingComplex O)), E')) (𝟙 _, g) ≫
      H.map (X := (Opposite.op (Q.obj (ringedSiteRingComplex O)), E'))
        (Y := (Opposite.op (Q.obj K), E')) ((Q.map ε).op, 𝟙 E') := by
    rw [← H.map_comp, ← H.map_comp]
    congr 1
    ext <;> simp
  rw [Category.assoc, hs, ← Category.assoc, hu E, hu E']
  change (d.app E ≫ F.map g) ≫ _ = _
  rw [← hn, Category.assoc]
  rfl

private def homRestrictionIso
    {A B : Type*} [Category A] [Category B]
    (H : Aᵒᵖ × A ⥤ A) (H' : Bᵒᵖ × B ⥤ B) (R : A ⥤ B)
    (e : H ⋙ R ≅ (R.op.prod R) ⋙ H')
    {K : A} {K' : B} (k : R.obj K ≅ K') :
    (Functor.curry.obj H).obj (op K) ⋙ R ≅
      R ⋙ (Functor.curry.obj H').obj (op K') := by
  refine NatIso.ofComponents (fun E ↦ e.app (op K, E) ≪≫
    H'.mapIso (k.symm.op.prod (Iso.refl (R.obj E)))) ?_
  intro E E' f
  have he := e.hom.naturality (X := (op K, E)) (Y := (op K, E')) (𝟙 _, f)
  dsimp at he ⊢
  simp only [Functor.map_id, op_id] at he
  rw [← Category.assoc, he]
  simp only [Category.assoc, ← H'.map_comp]
  congr 2
  ext <;> simp

private theorem homRestrictionIso_augmentation
    {A B : Type*} [Category A] [Category B]
    (H : Aᵒᵖ × A ⥤ A) (H' : Bᵒᵖ × B ⥤ B) (R : A ⥤ B)
    (e : H ⋙ R ≅ (R.op.prod R) ⋙ H')
    {K O : A} {K' O' : B} (k : R.obj K ≅ K') (o : R.obj O ≅ O')
    (a : K ⟶ O) (a' : K' ⟶ O')
    (ha : R.map a ≫ o.hom = k.hom ≫ a') (E : A) :
    R.map (H.map (a.op, 𝟙 E)) ≫ (homRestrictionIso H H' R e k).hom.app E =
      (homRestrictionIso H H' R e o).hom.app E ≫ H'.map (a'.op, 𝟙 (R.obj E)) := by
  have he := e.hom.naturality (X := (op O, E)) (Y := (op K, E)) (a.op, 𝟙 E)
  simp only [homRestrictionIso, NatIso.ofComponents_hom_app, Iso.trans_hom,
    Functor.mapIso_hom, Iso.prod_hom, Iso.op_hom, Iso.symm_hom, Iso.refl_hom,
    Iso.app_hom]
  dsimp at he
  simp only [Functor.map_id] at he
  rw [← Category.assoc, he]
  simp only [Category.assoc, ← H'.map_comp]
  congr 2
  apply Prod.hom_ext
  · change (k.inv ≫ R.map a).op = (a' ≫ o.inv).op
    congr 1
    apply (cancel_mono o.hom).mp
    simp [Category.assoc, ha]
  · simp

private theorem normalizeRestrictionIso
    {A B : Type*} [Category A] [Category B]
    {L : A ⥤ A} {L' : B ⥤ B} (R : A ⥤ B)
    (eta : 𝟭 A ⟶ L) (eta' : 𝟭 B ⟶ L')
    (e : L ⋙ R ≅ R ⋙ L') (sigma : R ≅ R)
    (he : ∀ E, R.map (eta.app E) ≫ e.hom.app E =
      sigma.hom.app E ≫ eta'.app (R.obj E)) :
    ∃ t : L ⋙ R ≅ R ⋙ L',
      ∀ E, R.map (eta.app E) ≫ t.hom.app E = eta'.app (R.obj E) := by
  refine ⟨e ≪≫ Functor.isoWhiskerRight sigma.symm L', ?_⟩
  intro E
  dsimp only [Iso.trans_hom, Functor.isoWhiskerRight_hom,
    NatTrans.comp_app, Functor.whiskerRight_app, Iso.symm_hom]
  rw [← Category.assoc, he, Category.assoc, ← eta'.naturality]
  simp

private theorem normalizedHomRestriction_exists
    {A B : Type*} [Category A] [Category B]
    (H : Aᵒᵖ × A ⥤ A) (H' : Bᵒᵖ × B ⥤ B) (R : A ⥤ B)
    (e : H ⋙ R ≅ (R.op.prod R) ⋙ H')
    {K O : A} {K' O' : B} (k : R.obj K ≅ K') (o : R.obj O ≅ O')
    (a : K ⟶ O) (a' : K' ⟶ O')
    (ha : R.map a ≫ o.hom = k.hom ≫ a')
    (d : 𝟭 A ≅ (Functor.curry.obj H).obj (op O))
    (d' : 𝟭 B ≅ (Functor.curry.obj H').obj (op O'))
    (eta : 𝟭 A ⟶ (Functor.curry.obj H).obj (op K))
    (eta' : 𝟭 B ⟶ (Functor.curry.obj H').obj (op K'))
    (heta : ∀ E, eta.app E = d.hom.app E ≫ H.map (a.op, 𝟙 E))
    (heta' : ∀ E, eta'.app E = d'.hom.app E ≫ H'.map (a'.op, 𝟙 E)) :
    ∃ t : (Functor.curry.obj H).obj (op K) ⋙ R ≅
        R ⋙ (Functor.curry.obj H').obj (op K'),
      ∀ E, R.map (eta.app E) ≫ t.hom.app E = eta'.app (R.obj E) := by
  let eO := homRestrictionIso H H' R e o
  let sigma : R ≅ R := Functor.isoWhiskerRight d R ≪≫ eO ≪≫
    Functor.isoWhiskerLeft R d'.symm
  apply normalizeRestrictionIso R eta eta' (homRestrictionIso H H' R e k) sigma
  intro E
  rw [heta E, Functor.map_comp, Category.assoc,
    homRestrictionIso_augmentation H H' R e k o a a' ha E, heta']
  dsimp only [sigma, eO, Iso.trans_hom, Iso.symm_hom,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
  simp

private def derivedHomUnitIso
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))] :
    𝟭 (ringedSiteDerived O) ≅ ringedCechCompletionFunctor O (ringedSiteRingComplex O) := by
  have hdelta (E : ringedSiteDerived O) : IsIso (ringedDerivedHomUnit O E) := by
    let A := SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)
    let : IsGrothendieckAbelian.{u} A := SheafOfModules.isGrothendieckAbelian _
    have : QuasiIso ((CochainComplex.toKInjectiveResolution.{u} A).app
        (DerivedCategory.Q.objPreimage E)) :=
      (CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{u} A _).2
    let e := DerivedCategory.Q.objObjPreimageIso E
    dsimp only [ringedDerivedHomUnit]
    repeat' apply IsIso.comp_isIso'
    all_goals try infer_instance
    change IsIso ((derivedInternalHom J O).mapIso ((Iso.refl _).prod e)).hom
    infer_instance
  refine NatIso.ofComponents (fun E ↦ @asIso _ _ _ _ (ringedDerivedHomUnit O E)
    (hdelta E)) ?_
  intro E E' g
  have hn := completion_unit_natural_core O (ringedSiteRingComplex O) (𝟙 _) E E' g
  simp only [ringedCechCompletionUnit, Functor.map_id, op_id] at hn
  change (ringedDerivedHomUnit O E ≫ (derivedInternalHom J O).map (𝟙 _)) ≫ _ =
    g ≫ ringedDerivedHomUnit O E' ≫ (derivedInternalHom J O).map (𝟙 _) at hn
  simpa only [Functor.map_id, Category.comp_id, asIso_hom, Functor.id_map] using hn.symm

private theorem augmentedCompletionRestriction
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (O : Sheaf J CommRingCat.{u}) (P : Sheaf K CommRingCat.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))]
    [HasDerivedCategory.{w} (SheafOfModules.{u}
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj P))]
    (R : ringedSiteDerived O ⥤ ringedSiteDerived P)
    (e : derivedInternalHom J O ⋙ R ≅ (R.op.prod R) ⋙ derivedInternalHom K P)
    (X : ringedSiteComplex O) (a : X ⟶ ringedSiteRingComplex O)
    (X' : ringedSiteComplex P) (a' : X' ⟶ ringedSiteRingComplex P)
    (h : Arrow.mk (R.map (DerivedCategory.Q.map a)) ≅
      Arrow.mk (DerivedCategory.Q.map a')) :
    ∃ t : ringedCechCompletionFunctor O X ⋙ R ≅ R ⋙ ringedCechCompletionFunctor P X',
      ∀ E, R.map (ringedCechCompletionUnit O X a E) ≫ t.hom.app E =
        ringedCechCompletionUnit P X' a' (R.obj E) := by
  let eta : 𝟭 _ ⟶ ringedCechCompletionFunctor O X :=
    { app := ringedCechCompletionUnit O X a
      naturality := fun {E E'} g ↦ (completion_unit_natural_core O X a E E' g).symm }
  let eta' : 𝟭 _ ⟶ ringedCechCompletionFunctor P X' :=
    { app := ringedCechCompletionUnit P X' a'
      naturality := fun {E E'} g ↦ (completion_unit_natural_core P X' a' E E' g).symm }
  exact normalizedHomRestriction_exists (derivedInternalHom J O) (derivedInternalHom K P)
    R e (Arrow.leftFunc.mapIso h) (Arrow.rightFunc.mapIso h)
    (DerivedCategory.Q.map a) (DerivedCategory.Q.map a') h.hom.w.symm
    (derivedHomUnitIso O) (derivedHomUnitIso P) eta eta'
    (fun _ ↦ by simp only [eta, derivedHomUnitIso, NatIso.ofComponents_hom_app,
      asIso_hom, ringedCechCompletionUnit])
    (fun _ ↦ by simp only [eta', derivedHomUnitIso, NatIso.ofComponents_hom_app,
      asIso_hom, ringedCechCompletionUnit])

-- Exact restriction commutes with cohomology; ordinary sheaf isomorphisms descend.

attribute [local irreducible] derivedInternalHom

private theorem derived_isIso_of_cover
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u})
    [HasDerivedCategory.{w} (ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))]
    [∀ U : C, HasDerivedCategory.{w} (ringedSiteModules.{u}
      ((sheafCompose (J.over U) (forget₂ CommRingCat RingCat)).obj (O.over U)))]
    {A : Type u} (U : A → C) (hU : J.CoversTop U)
    {X Y : ringedSiteDerived O} (g : X ⟶ Y)
    (hg : ∀ a, IsIso ((ringedDerivedRestriction O (U a)).map g)) : IsIso g := by
  let R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj O
  let (U : C) : HasDerivedCategory.{w} (SheafOfModules.{u}
      (((sheafCompose J (forget₂ CommRingCat RingCat)).obj O).over U)) :=
    inferInstanceAs (HasDerivedCategory.{w} (ringedSiteModules.{u}
      ((sheafCompose (J.over U) (forget₂ CommRingCat RingCat)).obj (O.over U))))
  apply (DerivedCategory.isIso_iff _ g).mpr
  intro n
  have hsheaf : IsIso ((SheafOfModules.toSheaf R).map
      ((DerivedCategory.homologyFunctor _ n).map g)) := by
    apply Sheaf.isIso_of_coversTop hU
    intro a
    let F := SheafOfModules.overFunctor.{u} R (U a)
    have : IsIso (F.mapDerivedCategory.map g) := hg a
    have hhom : IsIso ((DerivedCategory.homologyFunctor _ n).map
        (F.mapDerivedCategory.map g)) := inferInstance
    have : IsIso (F.map ((DerivedCategory.homologyFunctor _ n).map g)) :=
      (NatIso.isIso_map_iff (F.mapDerivedCategoryHomologyFunctorIso n) g).mpr (by
        change IsIso ((DerivedCategory.homologyFunctor _ n).map
          (F.mapDerivedCategory.map g))
        exact hhom)
    change IsIso ((SheafOfModules.toSheaf (R.over (U a))).map
      (F.map ((DerivedCategory.homologyFunctor _ n).map g)))
    infer_instance
  have := hsheaf
  exact isIso_of_reflects_iso _ (SheafOfModules.toSheaf R)

private theorem idempotence_of_comparison
    {A B : Type*} [Category A] [Category B]
    (F : A ⥤ A) (G : B ⥤ B) (R : A ⥤ B)
    (eta : ∀ E, E ⟶ F.obj E) (eta' : ∀ E, E ⟶ G.obj E)
    (hn : ∀ (X Y : B) (f : X ⟶ Y), eta' X ≫ G.map f = f ≫ eta' Y)
    (e : F ⋙ R ≅ R ⋙ G)
    (he : ∀ E, R.map (eta E) ≫ e.hom.app E = eta' (R.obj E))
    (E : A) (hl : IsIso (G.map (eta' (R.obj E))))
    (hr : IsIso (eta' (G.obj (R.obj E)))) :
    IsIso (R.map (F.map (eta E))) ∧ IsIso (R.map (eta (F.obj E))) := by
  have := hl
  have := hr
  have hmap : IsIso (G.map (R.map (eta E))) := by
    have h : G.map (R.map (eta E)) ≫ G.map (e.hom.app E) =
        G.map (eta' (R.obj E)) := by rw [← G.map_comp, he]
    have : IsIso (G.map (R.map (eta E)) ≫ G.map (e.hom.app E)) := by
      rw [h]
      infer_instance
    exact IsIso.of_isIso_comp_right _ (G.map (e.hom.app E))
  have := hmap
  have hright : IsIso (eta' (R.obj (F.obj E))) := by
    have h := hn _ _ (e.hom.app E)
    dsimp only [Functor.comp_obj] at h
    have : IsIso (eta' (R.obj (F.obj E)) ≫ G.map (e.hom.app E)) := by
      rw [h]
      infer_instance
    exact IsIso.of_isIso_comp_right _ (G.map (e.hom.app E))
  have := hright
  constructor
  · apply (NatIso.isIso_map_iff e (eta E)).mpr
    change IsIso (G.map (R.map (eta E)))
    exact hmap
  · have : IsIso (R.map (eta (F.obj E)) ≫ e.hom.app (F.obj E)) := by
      rw [he]
      infer_instance
    exact IsIso.of_isIso_comp_right _ (e.hom.app (F.obj E))

private theorem local_model_idempotence
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u})
    [HasDerivedCategory.{w} (ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))]
    [∀ U : C, HasDerivedCategory.{w} (ringedSiteModules.{u}
      ((sheafCompose (J.over U) (forget₂ CommRingCat RingCat)).obj (O.over U)))]
    (I : ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))
    (ι : I ⟶ SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))
    [I.IsFiniteType]
    (K : ringedSiteComplex O) (ε : K ⟶ ringedSiteRingComplex O)
    (hK : HasLocalExtendedCechDescription O I ι K ε) (E : ringedSiteDerived O) :
    IsIso ((ringedCechCompletionFunctor O K).map (ringedCechCompletionUnit O K ε E)) ∧
    IsIso (ringedCechCompletionUnit O K ε ((ringedCechCompletionFunctor O K).obj E)) := by
  classical
  let R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj O
  let (U : C) : HasDerivedCategory.{w} (SheafOfModules.{u}
      (((sheafCompose J (forget₂ CommRingCat RingCat)).obj O).over U)) :=
    inferInstanceAs (HasDerivedCategory.{w} (ringedSiteModules.{u}
      ((sheafCompose (J.over U) (forget₂ CommRingCat RingCat)).obj (O.over U))))
  obtain ⟨A, U, r, f, hU, hf⟩ := exists_finiteIdealGeneratingCover O I ι
  obtain ⟨eHom, _, _⟩ := ringedInternalHom_restriction J O
  have hlocal (a : A) :
      IsIso ((ringedDerivedRestriction O (U a)).map
        ((ringedCechCompletionFunctor O K).map (ringedCechCompletionUnit O K ε E))) ∧
      IsIso ((ringedDerivedRestriction O (U a)).map
        (ringedCechCompletionUnit O K ε ((ringedCechCompletionFunctor O K).obj E))) := by
    let b := fun i ↦ ringedSliceSection O (U a) (f a i)
    let K' := (ringedExtendedCech (O.over (U a)) (r a) b).1
    let ε' := (ringedExtendedCech (O.over (U a)) (r a) b).2
    let F := ringedCechCompletionFunctor O K
    let G := ringedCechCompletionFunctor (O.over (U a)) K'
    let V := ringedDerivedRestriction O (U a)
    obtain ⟨k, hk⟩ := hK (U a) (r a) (f a) (hf a)
    let o := ringedDerivedRingRestrictionIso O (U a)
    have ha : V.map (DerivedCategory.Q.map ε) ≫ o.hom =
        k.inv ≫ DerivedCategory.Q.map ε' := by
      change V.map (DerivedCategory.Q.map ε) ≫ o.hom =
        k.inv ≫ DerivedCategory.Q.map
          (ringedExtendedCech (O.over (U a)) (r a) b).2
      rw [← hk, Iso.inv_hom_id_assoc]
    let h : Arrow.mk (V.map (DerivedCategory.Q.map ε)) ≅
        Arrow.mk (DerivedCategory.Q.map ε') := Arrow.isoMk k.symm o ha.symm
    obtain ⟨t, ht⟩ := augmentedCompletionRestriction O (O.over (U a)) V (by
        dsimp only [V, ringedDerivedRestriction]
        exact eHom (U a))
      K ε K' ε' h
    have hi := ringed_cech_completion_unit_idempotence (O.over (U a)) (r a) b (V.obj E)
    exact idempotence_of_comparison F G V (ringedCechCompletionUnit O K ε)
      (ringedCechCompletionUnit (O.over (U a)) K' ε')
      (completion_unit_natural_core (O.over (U a)) K' ε') t ht E hi.1 hi.2
  exact ⟨derived_isIso_of_cover O U hU _ (fun a ↦ (hlocal a).1),
    derived_isIso_of_cover O U hU _ (fun a ↦ (hlocal a).2)⟩

private theorem universal_of_idempotence
    {D : Type*} [Category D] (F : D ⥤ D)
    (eta : ∀ E, E ⟶ F.obj E)
    (hn : ∀ (X Y : D) (f : X ⟶ Y), eta X ≫ F.map f = f ≫ eta Y)
    (E L : D) (hE : IsIso (F.map (eta E))) (hL : IsIso (eta L)) :
    Function.Bijective (fun h : F.obj E ⟶ L ↦ eta E ≫ h) := by
  have := hE
  have := hL
  constructor
  · intro f g hfg
    have hmap : F.map f = F.map g := by
      apply (cancel_epi (F.map (eta E))).mp
      simpa only [Functor.map_comp] using congrArg F.map hfg
    apply (cancel_mono (eta L)).mp
    rw [← hn, ← hn, hmap]
  · intro f
    refine ⟨F.map f ≫ inv (eta L), ?_⟩
    change eta E ≫ (F.map f ≫ inv (eta L)) = f
    rw [← Category.assoc, hn, Category.assoc, IsIso.hom_inv_id, Category.comp_id]

/-- The completeness and universal mapping clauses of the extended Cech reflector.
Source: Stacks Project, algebraization.tex, Tags 099B and 099F.
(auxiliary; not a blueprint node).

The proof contracts the localized extended Cech complex on each finite-generator slice,
filters the augmentation cone by its positive localization terms, and globalizes the
resulting orthogonality through restriction. The sequential-localization comparison
needed by this finite filtration is the remaining admitted argument.
-/
theorem ringedExtendedCech_reflector_core
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (O : Sheaf J CommRingCat.{u})
    [HasDerivedCategory.{w} (ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))]
    [∀ U : C, HasDerivedCategory.{w} (ringedSiteModules.{u}
      ((sheafCompose (J.over U) (forget₂ CommRingCat RingCat)).obj (O.over U)))]
    (I : ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))
    (ι : I ⟶ SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))
    [Mono ι] [I.IsFiniteType]
    (K : ringedSiteComplex O) (ε : K ⟶ ringedSiteRingComplex O)
    (hK : HasLocalExtendedCechDescription O I ι K ε) :
    (∀ E : ringedSiteDerived O,
      IsLocallyDerivedRingedIdealComplete O I ι
        ((ringedCechCompletionFunctor O K).obj E)) ∧
    (∀ (E L : ringedSiteDerived O),
      IsLocallyDerivedRingedIdealComplete O I ι L →
      Function.Bijective
        (fun h : (ringedCechCompletionFunctor O K).obj E ⟶ L ↦
          ringedCechCompletionUnit O K ε E ≫ h)) := by
  have hi := local_model_idempotence O I ι K ε hK
  constructor
  · intro E
    exact (ringedExtendedCech_complete_iff_unit_isIso J O I ι K ε hK _).mpr (hi E).2
  · intro E L hL
    exact universal_of_idempotence (ringedCechCompletionFunctor O K)
      (ringedCechCompletionUnit O K ε) (completion_unit_natural_core O K ε)
      E L (hi E).1 ((ringedExtendedCech_complete_iff_unit_isIso J O I ι K ε hK L).mp hL)

end CategoryTheory
