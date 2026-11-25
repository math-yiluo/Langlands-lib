/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMap

/-! # Normalized descent of an ordinary internal Hom comparison

Source: Stacks Project, Tags 08J7, 0A95 and 08JB.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section

set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory.RingedHomRestriction

abbrev Rings {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u}) :=
  (sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R

abbrev Modules {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u}) := SheafOfModules.{u} (Rings R)

abbrev Complex {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u}) := CochainComplex (Modules R) ℤ

abbrev ordinary {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u}) : (Complex R)ᵒᵖ × Complex R ⥤ Complex R :=
  Functor.uncurry.obj (homComplexFunctor (R := R))

/-- Transport both arguments of a Hom bifunctor along the same natural isomorphism.
Source: Stacks 08JB (auxiliary; not a blueprint node). -/
def pairIso {A B : Type*} [Category A] [Category B] {F G : A ⥤ B} (c : F ≅ G) :
    F.op.prod F ≅ G.op.prod G :=
  NatIso.ofComponents (fun X ↦ ((c.app X.1.unop).symm.op).prod (c.app X.2)) (by
    intro X Y f
    apply Prod.ext
    · exact congrArg Quiver.Hom.op (c.inv.naturality f.1.unop).symm
    · exact c.hom.naturality f.2)

/-- The composite of two internal Hom comparisons, transported along composition.
Source: Stacks 08JB (auxiliary; not a blueprint node). -/
def composite {A B E : Type*} [Category A] [Category B] [Category E]
    {H : Aᵒᵖ × A ⥤ A} {HU : Bᵒᵖ × B ⥤ B} {HV : Eᵒᵖ × E ⥤ E}
    {F : A ⥤ B} {G : B ⥤ E} {V : A ⥤ E} (c : F ⋙ G ≅ V)
    (a : H ⋙ F ≅ (F.op.prod F) ⋙ HU)
    (b : HU ⋙ G ≅ (G.op.prod G) ⋙ HV) : H ⋙ V ≅ (V.op.prod V) ⋙ HV :=
  Functor.isoWhiskerLeft H c.symm ≪≫ Functor.isoWhiskerRight a G ≪≫
    Functor.isoWhiskerLeft (F.op.prod F) b ≪≫ Functor.isoWhiskerRight (pairIso c) HV

/-- Compatibility of three comparisons with a specified composition isomorphism.
Source: Stacks 08JB (auxiliary; not a blueprint node). -/
def Compatible {A B E : Type*} [Category A] [Category B] [Category E]
    (H : Aᵒᵖ × A ⥤ A) (HU : Bᵒᵖ × B ⥤ B) (HV : Eᵒᵖ × E ⥤ E)
    (F : A ⥤ B) (G : B ⥤ E) (V : A ⥤ E) (c : F ⋙ G ≅ V)
    (a : H ⋙ F ≅ (F.op.prod F) ⋙ HU)
    (b : HU ⋙ G ≅ (G.op.prod G) ⋙ HV)
    (d : H ⋙ V ≅ (V.op.prod V) ⋙ HV) : Prop :=
  ∀ L M : A,
    G.map (a.hom.app (op L, M)) ≫ b.hom.app (op (F.obj L), F.obj M) ≫
      HV.map (X := (op (G.obj (F.obj L)), G.obj (F.obj M)))
        (Y := (op (V.obj L), V.obj M)) ((c.inv.app L).op, c.hom.app M) =
      c.hom.app (H.obj (op L, M)) ≫ d.hom.app (op L, M)

/-- Compatibility says precisely that the transported composite is the direct comparison.
Source: Stacks 08JB (auxiliary; not a blueprint node).
Proof: cancel the given composition isomorphism in each component. -/
theorem compatible_iff {A B E : Type*} [Category A] [Category B] [Category E]
    (H : Aᵒᵖ × A ⥤ A) (HU : Bᵒᵖ × B ⥤ B) (HV : Eᵒᵖ × E ⥤ E)
    (F : A ⥤ B) (G : B ⥤ E) (V : A ⥤ E) (c : F ⋙ G ≅ V)
    (a : H ⋙ F ≅ (F.op.prod F) ⋙ HU)
    (b : HU ⋙ G ≅ (G.op.prod G) ⋙ HV)
    (d : H ⋙ V ≅ (V.op.prod V) ⋙ HV) :
    Compatible H HU HV F G V c a b d ↔ composite c a b = d := by
  constructor
  · intro h
    apply Iso.ext
    ext X
    obtain ⟨L, M⟩ := X
    change c.inv.app (H.obj (L, M)) ≫
      (G.map (a.hom.app (L, M)) ≫ b.hom.app (op (F.obj L.unop), F.obj M) ≫
        HV.map (X := (op (G.obj (F.obj L.unop)), G.obj (F.obj M)))
          (Y := (op (V.obj L.unop), V.obj M))
          ((c.inv.app L.unop).op, c.hom.app M)) = d.hom.app (L, M)
    rw [h L.unop M, Iso.inv_hom_id_app_assoc]
  · intro h L M
    have hh := congrArg (fun e ↦ c.hom.app (H.obj (op L, M)) ≫
      e.hom.app (op L, M)) h
    simpa [composite, pairIso, Category.assoc] using hh

/-- The fixed augmentation comparison, using the factorization that defines derived Hom.
Source: Stacks 08J7 and 0A95
(auxiliary; not a blueprint node). -/
def augmentation {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (R : Sheaf J CommRingCat.{u}) [HasDerivedCategory.{w} (Modules R)] :
    ordinary R ⋙ DerivedCategory.Q ⟶
      (DerivedCategory.Q.op.prod DerivedCategory.Q) ⋙ derivedInternalHom.{u, w} J R := by
  let A := Modules R
  let : IsGrothendieckAbelian.{u} A := SheafOfModules.isGrothendieckAbelian _
  let I := CochainComplex.kInjectiveResolutionFunctor.{u} A
  let η := CochainComplex.toKInjectiveResolution.{u} A
  let c := Localization.fac
    ((𝟭 _).prod I ⋙ ordinary R ⋙ DerivedCategory.Q)
    (derivedInternalHom_inverts J R I η (fun M ↦
      ⟨(CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{u} A M).2,
        CochainComplex.isKInjective_kInjectiveResolutionFunctor_obj.{u} A M⟩))
    (DerivedCategory.Q.op.prod DerivedCategory.Q)
  exact Functor.whiskerRight (NatTrans.prod (𝟙 (𝟭 _)) η)
    (ordinary R ⋙ DerivedCategory.Q) ≫ c.inv

/-- Normalization on actual K-injective representatives. The chain comparison is supplied,
rather than chosen by the predicate. Source: Stacks 08JB
(auxiliary; not a blueprint node). -/
def Normalized
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (R : Sheaf J CommRingCat.{u}) (S : Sheaf K CommRingCat.{u})
    [HasDerivedCategory.{w} (Modules R)] [HasDerivedCategory.{w} (Modules S)]
    (T : Modules R ⥤ Modules S) [T.Additive]
    [PreservesFiniteLimits T] [PreservesFiniteColimits T]
    (a : ordinary R ⋙ T.mapHomologicalComplex (.up ℤ) ≅
      ((T.mapHomologicalComplex (.up ℤ)).op.prod
        (T.mapHomologicalComplex (.up ℤ))) ⋙ ordinary S)
    (e : derivedInternalHom.{u, w} J R ⋙ T.mapDerivedCategory ≅
      (T.mapDerivedCategory.op.prod T.mapDerivedCategory) ⋙ derivedInternalHom.{u, w} K S) :
    Prop :=
  ∀ (L I : Complex R) [I.IsKInjective],
    T.mapDerivedCategory.map ((augmentation J R).app (op L, I)) ≫
      e.hom.app (op (DerivedCategory.Q.obj L), DerivedCategory.Q.obj I) ≫
      (derivedInternalHom.{u, w} K S).map
        (X := (op (T.mapDerivedCategory.obj (DerivedCategory.Q.obj L)),
          T.mapDerivedCategory.obj (DerivedCategory.Q.obj I)))
        (Y := (op (DerivedCategory.Q.obj ((T.mapHomologicalComplex (.up ℤ)).obj L)),
          DerivedCategory.Q.obj ((T.mapHomologicalComplex (.up ℤ)).obj I)))
        ((T.mapDerivedCategoryFactors.inv.app L).op, T.mapDerivedCategoryFactors.hom.app I) =
    T.mapDerivedCategoryFactors.hom.app ((ordinary R).obj (op L, I)) ≫
      DerivedCategory.Q.map (a.hom.app (op L, I)) ≫
      (augmentation K S).app
        (op ((T.mapHomologicalComplex (.up ℤ)).obj L),
          (T.mapHomologicalComplex (.up ℤ)).obj I)

private theorem augmentation_isIso
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (R : Sheaf J CommRingCat.{u}) [HasDerivedCategory.{w} (Modules R)]
    (L I : Complex R) [I.IsKInjective] :
    IsIso ((augmentation J R).app (op L, I)) := by
  let A := Modules R
  let : IsGrothendieckAbelian.{u} A := SheafOfModules.isGrothendieckAbelian _
  let F := CochainComplex.kInjectiveResolutionFunctor.{u} A
  let η := CochainComplex.toKInjectiveResolution.{u} A
  have : (F.obj I).IsKInjective :=
    CochainComplex.isKInjective_kInjectiveResolutionFunctor_obj.{u} A I
  have : QuasiIso (η.app I) :=
    (CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{u} A I).2
  have h : QuasiIso ((ordinary R).map (X := (op L, I)) (Y := (op L, F.obj I))
      (𝟙 (op L), η.app I)) := by
    simpa only [ordinary, Functor.uncurry_obj_map, Functor.map_id,
      NatTrans.id_app, op_id, Category.id_comp] using quasiIso_homComplex_map
        (I' := I) (I := F.obj I) (L' := L) (L := L) (η.app I) (𝟙 L)
  have : IsIso (DerivedCategory.Q.map ((ordinary R).map (X := (op L, I)) (Y := (op L, F.obj I))
      (𝟙 (op L), η.app I))) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).mpr h
  dsimp only [augmentation, NatTrans.comp_app, Functor.whiskerRight_app,
    NatTrans.id_app, Functor.id_obj]
  change IsIso (DerivedCategory.Q.map ((ordinary R).map
    (X := (op L, I)) (Y := (op L, F.obj I)) (𝟙 (op L), η.app I)) ≫ _)
  infer_instance

/-- An ordinary natural Hom comparison descends uniquely after K-injective restriction.

Source: Stacks Project, Tags 08J7, 0A95 and 08JB.
(auxiliary; not a blueprint node).

Proof: precompose with Q in the source variable and with the K-injective inclusion followed
by Q in the target variable. Both are localizations. The augmentation is invertible on
K-injective targets, and remains so after T because T preserves K-injectives. Conjugate the
localized ordinary comparison by these augmentations and the exact-functor factorization.
Fully faithful precomposition descends this natural isomorphism. Its component equation is
exactly Normalized. This uses no boundedness assumption. -/
theorem comparison_exists
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (R : Sheaf J CommRingCat.{u}) (S : Sheaf K CommRingCat.{u})
    [HasDerivedCategory.{w} (Modules R)] [HasDerivedCategory.{w} (Modules S)]
    (T : Modules R ⥤ Modules S) [T.Additive]
    [PreservesFiniteLimits T] [PreservesFiniteColimits T]
    (hT : ∀ I : Complex R, I.IsKInjective →
      CochainComplex.IsKInjective ((T.mapHomologicalComplex (.up ℤ)).obj I))
    (a : ordinary R ⋙ T.mapHomologicalComplex (.up ℤ) ≅
      ((T.mapHomologicalComplex (.up ℤ)).op.prod
        (T.mapHomologicalComplex (.up ℤ))) ⋙ ordinary S) :
    ∃ e : derivedInternalHom.{u, w} J R ⋙ T.mapDerivedCategory ≅
      (T.mapDerivedCategory.op.prod T.mapDerivedCategory) ⋙ derivedInternalHom.{u, w} K S,
      Normalized R S T a e := by
  classical
  let A := Modules R
  let : IsGrothendieckAbelian.{u} A := SheafOfModules.isGrothendieckAbelian _
  let Q : Complex R ⥤ DerivedCategory A := DerivedCategory.Q
  let ι : CochainComplex.KInjectives A ⥤ Complex R := CochainComplex.KInjectives.ι
  let B := (𝟭 (Complex R)ᵒᵖ).prod ι
  let P := Q.op.prod (ι ⋙ Q)
  let : (CochainComplex.KInjectives.quasiIso A).ContainsIdentities := ⟨fun X ↦ by
    change QuasiIso (𝟙 X.obj)
    infer_instance⟩
  let W := (HomologicalComplex.quasiIso A (.up ℤ)).op.prod
    (CochainComplex.KInjectives.quasiIso A)
  have : (ι ⋙ Q).IsLocalization (CochainComplex.KInjectives.quasiIso A) :=
    inferInstanceAs (((CochainComplex.KInjectives.localizerMorphism A).functor ⋙
      DerivedCategory.Q).IsLocalization (CochainComplex.KInjectives.quasiIso A))
  let Tc := T.mapHomologicalComplex (.up ℤ)
  let α := Functor.whiskerLeft B (augmentation J R)
  have : IsIso α := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro X
    have : X.2.obj.IsKInjective := X.2.property
    exact augmentation_isIso J R X.1.unop X.2.obj
  let β := Functor.whiskerLeft (B ⋙ (Tc.op.prod Tc)) (augmentation K S)
  have : IsIso β := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro X
    have : CochainComplex.IsKInjective (Tc.obj X.2.obj) := hT X.2.obj X.2.property
    change IsIso ((augmentation K S).app (op (Tc.obj X.1.unop), Tc.obj X.2.obj))
    exact augmentation_isIso K S _ _
  let q : P ⋙ (T.mapDerivedCategory.op.prod T.mapDerivedCategory) ≅
      B ⋙ (Tc.op.prod Tc) ⋙ (DerivedCategory.Q.op.prod DerivedCategory.Q) :=
    NatIso.ofComponents (fun X ↦
      ((T.mapDerivedCategoryFactors.app X.1.unop).symm.op).prod
        (T.mapDerivedCategoryFactors.app X.2.obj)) (by
      intro X Y f
      apply Prod.ext
      · exact congrArg Quiver.Hom.op
          (T.mapDerivedCategoryFactors.inv.naturality f.1.unop).symm
      · exact T.mapDerivedCategoryFactors.hom.naturality f.2.hom)
  let p : P ⋙ (derivedInternalHom.{u, w} J R ⋙ T.mapDerivedCategory) ≅
      P ⋙ ((T.mapDerivedCategory.op.prod T.mapDerivedCategory) ⋙
        derivedInternalHom.{u, w} K S) :=
    (Functor.isoWhiskerRight (asIso α) T.mapDerivedCategory).symm ≪≫
      Functor.isoWhiskerLeft (B ⋙ ordinary R) T.mapDerivedCategoryFactors ≪≫
      Functor.isoWhiskerRight (Functor.isoWhiskerLeft B a) DerivedCategory.Q ≪≫
      asIso β ≪≫ (Functor.isoWhiskerRight q (derivedInternalHom.{u, w} K S)).symm
  let FF := Localization.fullyFaithfulWhiskeringLeft P W (DerivedCategory (Modules S))
  let e := FF.preimageIso p
  refine ⟨e, ?_⟩
  intro L I hI
  have : IsIso ((augmentation J R).app (op L, I)) := augmentation_isIso J R L I
  have hp := NatTrans.congr_app (FF.map_preimage p.hom) (op L,
    CochainComplex.KInjectives.mk I)
  change e.hom.app (op (DerivedCategory.Q.obj L), DerivedCategory.Q.obj I) =
    p.hom.app (op L, CochainComplex.KInjectives.mk I) at hp
  rw [hp]
  simp [p, α, β, q, B, Tc, ι, CochainComplex.KInjectives.ι,
    Category.assoc, ← Functor.map_comp]

/-- The representative equation determines a derived comparison uniquely.
Source: Stacks 08J7, 0A95 and 08JB
(auxiliary; not a blueprint node).
Proof: evaluate after Q in the first variable and K-injective representatives in the
second. Cancel the invertible augmentation and restriction factorization. The product of
these localizations is essentially surjective, so equality there is equality everywhere. -/
theorem comparison_unique
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (R : Sheaf J CommRingCat.{u}) (S : Sheaf K CommRingCat.{u})
    [HasDerivedCategory.{w} (Modules R)] [HasDerivedCategory.{w} (Modules S)]
    (T : Modules R ⥤ Modules S) [T.Additive]
    [PreservesFiniteLimits T] [PreservesFiniteColimits T]
    (a : ordinary R ⋙ T.mapHomologicalComplex (.up ℤ) ≅
      ((T.mapHomologicalComplex (.up ℤ)).op.prod
        (T.mapHomologicalComplex (.up ℤ))) ⋙ ordinary S)
    (e e' : derivedInternalHom.{u, w} J R ⋙ T.mapDerivedCategory ≅
      (T.mapDerivedCategory.op.prod T.mapDerivedCategory) ⋙ derivedInternalHom.{u, w} K S)
    (he : Normalized R S T a e) (he' : Normalized R S T a e') : e = e' := by
  let A := Modules R
  let : IsGrothendieckAbelian.{u} A := SheafOfModules.isGrothendieckAbelian _
  let Q : Complex R ⥤ DerivedCategory A := DerivedCategory.Q
  let ι : CochainComplex.KInjectives A ⥤ Complex R := CochainComplex.KInjectives.ι
  let P := Q.op.prod (ι ⋙ Q)
  let : (CochainComplex.KInjectives.quasiIso A).ContainsIdentities := ⟨fun X ↦ by
    change QuasiIso (𝟙 X.obj)
    infer_instance⟩
  let W := (HomologicalComplex.quasiIso A (.up ℤ)).op.prod
    (CochainComplex.KInjectives.quasiIso A)
  have : (ι ⋙ Q).IsLocalization (CochainComplex.KInjectives.quasiIso A) :=
    inferInstanceAs (((CochainComplex.KInjectives.localizerMorphism A).functor ⋙
      DerivedCategory.Q).IsLocalization (CochainComplex.KInjectives.quasiIso A))
  apply Iso.ext
  apply Localization.natTrans_ext P W
  rintro ⟨⟨L⟩, I⟩
  have : I.obj.IsKInjective := I.property
  have : IsIso ((augmentation J R).app (op L, I.obj)) := augmentation_isIso J R _ _
  let q := ((T.mapDerivedCategoryFactors.app L).symm.op).prod
    (T.mapDerivedCategoryFactors.app I.obj)
  apply (cancel_epi (T.mapDerivedCategory.map ((augmentation J R).app (op L, I.obj)))).mp
  apply (cancel_mono ((derivedInternalHom.{u, w} K S).map q.hom)).mp
  have h := (he L I.obj).trans (he' L I.obj).symm
  simpa [q, P, Q, ι, Prod.mkHom, Category.assoc] using h

end CategoryTheory.RingedHomRestriction
