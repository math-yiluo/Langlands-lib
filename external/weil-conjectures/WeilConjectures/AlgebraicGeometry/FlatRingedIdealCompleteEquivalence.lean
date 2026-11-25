/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
public import WeilConjectures.AlgebraicGeometry.RingedSiteIdeal
public import WeilConjectures.CategoryTheory.LocalExtendedCechDescription
public import WeilConjectures.CategoryTheory.LocallyDerivedRingedIdealComplete
public import WeilConjectures.CategoryTheory.RingedCompletionUnit
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RestrictScalars
import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMap
import WeilConjectures.AlgebraicGeometry.CoefficientHomAugmentation
import WeilConjectures.AlgebraicGeometry.ExtendedCechCompletionModel
import WeilConjectures.AlgebraicGeometry.FlatRingedCechBaseChange
import WeilConjectures.AlgebraicGeometry.RestrictedCoefficientHom
import WeilConjectures.AlgebraicGeometry.RestrictionLocalCompleteness
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-!
# Flat ringed-site equivalence on locally derived complete objects

Source: Stacks Project, Algebraization, Tags 099I and 0999
(auxiliary; not a blueprint node).
-/

@[expose] public section
set_option Elab.async false

universe u w

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

attribute [local instance 20000] ringedCompletionHasSheafCompose

-- All computations with the chosen Hom complex use its public projection API.
attribute [local irreducible] homComplexFunctor ringedHomUnitEvaluationIso

/-- Restriction of scalars is exact on module sheaves.
Source: Stacks Project, Algebraization, Tag 099C
(auxiliary; not a blueprint node).
Proof: the underlying additive sheaf is unchanged. Kernels are sectionwise kernels with
restricted action; cokernels are sheafifications of the same additive presheaf cokernels.
The same description applies to finite products and coproducts. -/
theorem siteRestrictScalars_exact {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} {R B : Sheaf J CommRingCat.{u}} (φ : R ⟶ B) :
    PreservesFiniteLimits
      (SheafOfModules.restrictScalars.{u}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)) ∧
    PreservesFiniteColimits
      (SheafOfModules.restrictScalars.{u}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)) := by
  let F := SheafOfModules.restrictScalars.{u}
    ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)
  have : PreservesFiniteLimits (F ⋙ SheafOfModules.toSheaf.{u} (siteModuleRings R)) :=
    inferInstanceAs (PreservesFiniteLimits (SheafOfModules.toSheaf.{u} (siteModuleRings B)))
  have : PreservesFiniteColimits (F ⋙ SheafOfModules.toSheaf.{u} (siteModuleRings R)) :=
    inferInstanceAs (PreservesFiniteColimits (SheafOfModules.toSheaf.{u} (siteModuleRings B)))
  have : ReflectsFiniteColimits (SheafOfModules.toSheaf.{u} (siteModuleRings R)) :=
    { reflects := fun _ _ _ ↦ reflectsColimitsOfShape_of_reflectsIsomorphisms }
  exact ⟨preservesFiniteLimits_of_reflects_of_preserves F
      (SheafOfModules.toSheaf.{u} (siteModuleRings R)),
    preservesFiniteColimits_of_reflects_of_preserves F
      (SheafOfModules.toSheaf.{u} (siteModuleRings R))⟩

/-- Restriction of scalars reflects isomorphisms of sheaves of modules.
Source: Stacks Project, Algebraization, Tag 099I, first paragraph
(auxiliary; not a blueprint node).
Proof: its composite with the forgetful functor to abelian sheaves is precisely the
forgetful functor over B, which reflects isomorphisms. -/
theorem siteRestrictScalars_reflectsIsomorphisms
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    {R B : Sheaf J CommRingCat.{u}} (φ : R ⟶ B) :
    (SheafOfModules.restrictScalars.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)).ReflectsIsomorphisms := by
  let F := SheafOfModules.restrictScalars.{u}
    ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)
  have : (F ⋙ SheafOfModules.toSheaf.{u} (siteModuleRings R)).ReflectsIsomorphisms :=
    inferInstanceAs ((SheafOfModules.toSheaf.{u} (siteModuleRings B)).ReflectsIsomorphisms)
  exact reflectsIsomorphisms_of_comp F (SheafOfModules.toSheaf.{u} (siteModuleRings R))

/-- Termwise restriction preserves and reflects quasi-isomorphisms.
Source: Stacks Project, Algebraization, Tag 099I, the construction of E prime
(auxiliary; not a blueprint node).
Proof: exactness identifies the restricted cohomology maps with restriction of the
original cohomology maps. Restriction reflects isomorphisms of these sheaves. -/
theorem siteRestrictScalars_quasiIso_iff
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    {R B : Sheaf J CommRingCat.{u}} (φ : R ⟶ B)
    {K L : CochainComplex (SheafOfModules.{u} (siteModuleRings B)) ℤ} (f : K ⟶ L) :
    QuasiIso (((SheafOfModules.restrictScalars.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)).mapHomologicalComplex
        (.up ℤ)).map f) ↔ QuasiIso f := by
  let := (siteRestrictScalars_exact φ).1
  let := (siteRestrictScalars_exact φ).2
  have := siteRestrictScalars_reflectsIsomorphisms φ
  exact HomologicalComplex.quasiIso_map_iff_of_preservesHomology f _

/-- Derived restriction of scalars, using Mathlib's restriction of scalars and its exact
functor localization, rather than an unspecified functor between derived categories.
Source: Stacks Project, Algebraization, Tags 099C and 099I
(auxiliary; not a blueprint node). -/
noncomputable def siteDerivedRestrictScalars {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} {R B : Sheaf J CommRingCat.{u}} (φ : R ⟶ B)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (siteModuleRings R))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (siteModuleRings B))] :
    DerivedCategory (SheafOfModules.{u} (siteModuleRings B)) ⥤
      DerivedCategory (SheafOfModules.{u} (siteModuleRings R)) :=
  letI := (siteRestrictScalars_exact φ).1
  letI := (siteRestrictScalars_exact φ).2
  (SheafOfModules.restrictScalars.{u}
    ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)).mapDerivedCategory

/-- Derived restriction of scalars reflects isomorphisms.
Source: Stacks Project, Algebraization, Tag 099I, first paragraph
(auxiliary; not a blueprint node).
Proof: the forgetful functor to abelian sheaves reflects isomorphisms, and its composite
with restriction is the same forgetful functor over B. Exactness commutes restriction
with every cohomology functor. Thus invertibility after restriction implies invertibility
on every cohomology sheaf, which detects isomorphisms of unbounded derived objects. -/
theorem siteDerivedRestrictScalars_reflectsIsomorphisms
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    {R B : Sheaf J CommRingCat.{u}} (φ : R ⟶ B)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (siteModuleRings R))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (siteModuleRings B))] :
    (siteDerivedRestrictScalars φ).ReflectsIsomorphisms := by
  let F := SheafOfModules.restrictScalars.{u}
    ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)
  let := (siteRestrictScalars_exact φ).1
  let := (siteRestrictScalars_exact φ).2
  have : F.ReflectsIsomorphisms := siteRestrictScalars_reflectsIsomorphisms φ
  constructor
  intro X Y f hf
  change IsIso (F.mapDerivedCategory.map f) at hf
  have := hf
  apply (DerivedCategory.isIso_iff _ f).mpr
  intro n
  have h : IsIso ((F.mapDerivedCategory ⋙
      DerivedCategory.homologyFunctor (SheafOfModules.{u} (siteModuleRings R)) n).map f) :=
    by
      change IsIso ((DerivedCategory.homologyFunctor _ n).map
        (F.mapDerivedCategory.map f))
      infer_instance
  have : IsIso ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (siteModuleRings B)) n ⋙ F).map f) :=
    (NatIso.isIso_map_iff (F.mapDerivedCategoryHomologyFunctorIso n) f).mpr h
  change IsIso (F.map ((DerivedCategory.homologyFunctor _ n).map f)) at this
  exact isIso_of_reflects_iso _ F

private theorem locallyDerivedRingedIdealComplete_of_iso
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u}) (I : RingedSiteIdeal R)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (siteModuleRings R))]
    [∀ U : C, HasDerivedCategory.{w}
      (SheafOfModules.{u} (siteModuleRings (R.over U)))]
    {M N : ringedSiteDerived R} (e : M ≅ N)
    (hN : IsLocallyDerivedRingedIdealComplete R I.module I.inclusion N) :
    IsLocallyDerivedRingedIdealComplete R I.module I.inclusion M := by
  intro U f hf
  exact (hN U f hf).of_iso ((derivedInternalHom (J.over U) (R.over U)).mapIso
    ((Iso.refl _).prod ((ringedDerivedRestriction R U).mapIso e)))

set_option backward.isDefEq.respectTransparency false in
/-- The specified exact derived restriction preserves and reflects local completeness.
Source: Stacks Project, Algebraization, Tag 099C
(auxiliary; not a blueprint node).
Proof: the extension ideal's unique local-membership description is the hypothesis of
restrictScalars_locallyDerivedComplete_iff. Identify its image of the chosen complex
representative with the exact derived functor using mapDerivedCategoryFactors and the
representative isomorphism. Local completeness is invariant under these isomorphisms
since each of its defining internal-Hom objects is functorial. -/
theorem siteDerivedRestrictScalars_locallyDerivedComplete_iff
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    {R B : Sheaf J CommRingCat.{u}} (φ : R ⟶ B) (I : RingedSiteIdeal R)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (siteModuleRings R))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (siteModuleRings B))]
    [∀ U : C, HasDerivedCategory.{w}
      (SheafOfModules.{u} (siteModuleRings (R.over U)))]
    [∀ U : C, HasDerivedCategory.{w}
      (SheafOfModules.{u} (siteModuleRings (B.over U)))]
    (M : ringedSiteDerived B) :
    IsLocallyDerivedRingedIdealComplete R I.module I.inclusion
        ((siteDerivedRestrictScalars φ).obj M) ↔
      IsLocallyDerivedRingedIdealComplete B
        (I.extension φ).module (I.extension φ).inclusion M := by
  let F := SheafOfModules.restrictScalars.{u}
    ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)
  let := (siteRestrictScalars_exact φ).1
  let := (siteRestrictScalars_exact φ).2
  have hIB : ∀ (U : C) (b : B.obj.obj (Opposite.op U)),
      b ∈ (I.extension φ).sections U ↔ ∃ S : Sieve U, S ∈ J U ∧
        ∀ (V : C) (g : V ⟶ U), S g →
          B.obj.map g.op b ∈ Ideal.map (φ.hom.app (Opposite.op V)).hom (I.sections V) := by
    intro U b
    have he (V : C) :
        Ideal.map (φ.hom.app (Opposite.op V)).hom (I.sections V) =
          Ideal.span (Set.range (fun a : I.sections V ↦ φ.hom.app (Opposite.op V) a)) := by
      unfold Ideal.map
      rw [Set.image_eq_range]
      rfl
    simp_rw [he]
    exact (Classical.choose_spec (I.existsUnique_extension φ).exists) U b
  have h := restrictScalars_locallyDerivedComplete_iff J R B φ I (I.extension φ) hIB M
  let e : F.mapDerivedCategory.obj M ≅
      DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj
        (DerivedCategory.Q.objPreimage M)) :=
    F.mapDerivedCategory.mapIso (DerivedCategory.Q.objObjPreimageIso M).symm ≪≫
      F.mapDerivedCategoryFactors.app (DerivedCategory.Q.objPreimage M)
  exact ⟨fun hM ↦ h.mp
      (locallyDerivedRingedIdealComplete_of_iso R I e.symm hM),
    fun hM ↦ locallyDerivedRingedIdealComplete_of_iso R I e (h.mpr hM)⟩

/-- Restriction of scalars on the full subcategories of locally derived complete objects.
Source: Stacks Project, Algebraization, Tag 099I, first paragraph
(auxiliary; not a blueprint node).
This is the lift of the specified exact derived restriction, with no choices of objects. -/
noncomputable def siteCompleteRestrictScalars
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    {R B : Sheaf J CommRingCat.{u}} (φ : R ⟶ B) (I : RingedSiteIdeal R)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (siteModuleRings R))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (siteModuleRings B))]
    [∀ U : C, HasDerivedCategory.{w}
      (SheafOfModules.{u} (siteModuleRings (R.over U)))]
    [∀ U : C, HasDerivedCategory.{w}
      (SheafOfModules.{u} (siteModuleRings (B.over U)))] :
    ObjectProperty.FullSubcategory
        (IsLocallyDerivedRingedIdealComplete B (I.extension φ).module (I.extension φ).inclusion) ⥤
      ObjectProperty.FullSubcategory
        (IsLocallyDerivedRingedIdealComplete R I.module I.inclusion) :=
  ObjectProperty.lift (IsLocallyDerivedRingedIdealComplete R I.module I.inclusion)
    (ObjectProperty.ι
      (IsLocallyDerivedRingedIdealComplete B (I.extension φ).module (I.extension φ).inclusion) ⋙
        siteDerivedRestrictScalars φ)
    (fun M ↦ (siteDerivedRestrictScalars_locallyDerivedComplete_iff φ I M.obj).mpr M.property)

/-- Restriction on locally derived complete objects is conservative.
Source: Stacks Project, Algebraization, Tag 099I, first paragraph
(auxiliary; not a blueprint node).
Proof: compose with the fully faithful inclusion into the ambient derived category.
This composite is the ambient conservative restriction after a fully faithful inclusion,
and hence reflects isomorphisms. Reflection by the composite implies reflection by the
restriction functor itself. -/
theorem siteCompleteRestrictScalars_reflectsIsomorphisms
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    {R B : Sheaf J CommRingCat.{u}} (φ : R ⟶ B) (I : RingedSiteIdeal R)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (siteModuleRings R))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (siteModuleRings B))]
    [∀ U : C, HasDerivedCategory.{w}
      (SheafOfModules.{u} (siteModuleRings (R.over U)))]
    [∀ U : C, HasDerivedCategory.{w}
      (SheafOfModules.{u} (siteModuleRings (B.over U)))] :
    (siteCompleteRestrictScalars φ I).ReflectsIsomorphisms := by
  have := siteDerivedRestrictScalars_reflectsIsomorphisms φ
  let P := IsLocallyDerivedRingedIdealComplete R I.module I.inclusion
  have : (siteCompleteRestrictScalars φ I ⋙ ObjectProperty.ι P).ReflectsIsomorphisms :=
    inferInstanceAs ((ObjectProperty.ι (IsLocallyDerivedRingedIdealComplete B
      (I.extension φ).module (I.extension φ).inclusion) ⋙
        siteDerivedRestrictScalars φ).ReflectsIsomorphisms)
  exact reflectsIsomorphisms_of_comp (siteCompleteRestrictScalars φ I)
    (ObjectProperty.ι (IsLocallyDerivedRingedIdealComplete R I.module I.inclusion))

/-- The categorical last step of the complete-restriction equivalence argument.
Source: Stacks Project, Algebraization, Tag 099I, final paragraph
(auxiliary; not a blueprint node).
Proof: reflection of isomorphisms makes every component of beta invertible.
Use beta as the unit and the inverse of alpha as the counit; the standard
adjointification of an equivalence supplies the triangle identity. Its forward
functor is the explicit complete restriction, whose ambient composite is the
specified exact derived restriction. -/
theorem siteCompleteRestrictScalars_equivalence_of_inverse
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    {R B : Sheaf J CommRingCat.{u}} (φ : R ⟶ B) (I : RingedSiteIdeal R)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (siteModuleRings R))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (siteModuleRings B))]
    [∀ U : C, HasDerivedCategory.{w}
      (SheafOfModules.{u} (siteModuleRings (R.over U)))]
    [∀ U : C, HasDerivedCategory.{w}
      (SheafOfModules.{u} (siteModuleRings (B.over U)))]
    (F : ObjectProperty.FullSubcategory
        (IsLocallyDerivedRingedIdealComplete R I.module I.inclusion) ⥤
      ObjectProperty.FullSubcategory
        (IsLocallyDerivedRingedIdealComplete B (I.extension φ).module (I.extension φ).inclusion))
    (α : 𝟭 _ ≅ F ⋙ siteCompleteRestrictScalars φ I)
    (β : 𝟭 _ ⟶ siteCompleteRestrictScalars φ I ⋙ F)
    (hβ : ∀ M, IsIso ((siteCompleteRestrictScalars φ I).map (β.app M))) :
    ∃ e : ObjectProperty.FullSubcategory
        (IsLocallyDerivedRingedIdealComplete B (I.extension φ).module (I.extension φ).inclusion) ≌
        ObjectProperty.FullSubcategory
          (IsLocallyDerivedRingedIdealComplete R I.module I.inclusion),
      Nonempty (e.functor ⋙
        ObjectProperty.ι (IsLocallyDerivedRingedIdealComplete R I.module I.inclusion) ≅
        ObjectProperty.ι
          (IsLocallyDerivedRingedIdealComplete B (I.extension φ).module (I.extension φ).inclusion) ⋙
          siteDerivedRestrictScalars φ) := by
  have := siteCompleteRestrictScalars_reflectsIsomorphisms φ I
  have : ∀ M, IsIso (β.app M) := by
    intro M
    have := hβ M
    exact isIso_of_reflects_iso _ (siteCompleteRestrictScalars φ I)
  have : IsIso β := NatIso.isIso_of_isIso_app β
  let e := Equivalence.mk (siteCompleteRestrictScalars φ I) F (asIso β) α.symm
  exact ⟨e, ⟨Iso.refl _⟩⟩

set_option backward.isDefEq.respectTransparency false in
/-- An ambient coefficient-Hom construction with its augmentation comparison gives
an equivalence on complete objects.
Source: Stacks Project, Algebraization, Tag 099I, the last two paragraphs
(auxiliary; not a blueprint node).
Proof: the extended Cech reflector theorem makes the completion of every object
complete. Transport along theta and reflect completeness by restriction to lift F
to the complete subcategories. On a complete object the completion unit is invertible;
composing it with theta inverse gives the R-side natural isomorphism. Lift beta to
the B-side subcategory. Its restriction is invertible because its composite with
theta is the completion unit. Apply the conservative equivalence assembly lemma. -/
theorem siteCompleteRestrictScalars_equivalence_of_completion
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    {R B : Sheaf J CommRingCat.{u}} (φ : R ⟶ B) (I : RingedSiteIdeal R)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (siteModuleRings R))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (siteModuleRings B))]
    [∀ U : C, HasDerivedCategory.{w}
      (SheafOfModules.{u} (siteModuleRings (R.over U)))]
    [∀ U : C, HasDerivedCategory.{w}
      (SheafOfModules.{u} (siteModuleRings (B.over U)))]
    (hI : SheafOfModules.IsFiniteType.{u, u, u} I.module)
    (K : ringedSiteComplex R) (ε : K ⟶ ringedSiteRingComplex R)
    (hK : HasLocalExtendedCechDescription R I.module I.inclusion K ε)
    (F : ringedSiteDerived R ⥤ ringedSiteDerived B)
    (θ : F ⋙ siteDerivedRestrictScalars φ ≅ ringedCechCompletionFunctor R K)
    (β : 𝟭 (ringedSiteDerived B) ⟶ siteDerivedRestrictScalars φ ⋙ F)
    (hβ : ∀ M : ringedSiteDerived B,
      (siteDerivedRestrictScalars φ).map (β.app M) ≫
          θ.hom.app ((siteDerivedRestrictScalars φ).obj M) =
        ringedCechCompletionUnit R K ε ((siteDerivedRestrictScalars φ).obj M)) :
    ∃ e : ObjectProperty.FullSubcategory
        (IsLocallyDerivedRingedIdealComplete B (I.extension φ).module (I.extension φ).inclusion) ≌
        ObjectProperty.FullSubcategory
          (IsLocallyDerivedRingedIdealComplete R I.module I.inclusion),
      Nonempty (e.functor ⋙
        ObjectProperty.ι (IsLocallyDerivedRingedIdealComplete R I.module I.inclusion) ≅
        ObjectProperty.ι
          (IsLocallyDerivedRingedIdealComplete B (I.extension φ).module (I.extension φ).inclusion) ⋙
          siteDerivedRestrictScalars φ) := by
  let := hI
  have : Mono I.inclusion := by
    constructor
    intro Z f g h
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro X
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    apply Subtype.ext
    exact congrArg (fun k ↦ k.val.app X z) h
  let P : ObjectProperty (ringedSiteDerived R) :=
    IsLocallyDerivedRingedIdealComplete R I.module I.inclusion
  let Q : ObjectProperty (ringedSiteDerived B) := IsLocallyDerivedRingedIdealComplete B
    (I.extension φ).module (I.extension φ).inclusion
  let r := siteDerivedRestrictScalars φ
  let s := siteCompleteRestrictScalars φ I
  obtain ⟨hcomplete, hnatural, _, hunit⟩ :=
    ringedExtendedCech_reflector_properties J R I.module I.inclusion K ε hK
  have hF (E : ringedSiteDerived R) : Q (F.obj E) :=
    (siteDerivedRestrictScalars_locallyDerivedComplete_iff φ I (F.obj E)).mp
      (locallyDerivedRingedIdealComplete_of_iso R I (θ.app E) (hcomplete E))
  let G : P.FullSubcategory ⥤ Q.FullSubcategory :=
    ObjectProperty.lift Q (ObjectProperty.ι P ⋙ F) (fun E ↦ hF E.obj)
  have hη (E : P.FullSubcategory) :
      IsIso (ringedCechCompletionUnit R K ε E.obj) := hunit E.obj E.property
  let α : 𝟭 P.FullSubcategory ≅ G ⋙ s :=
    NatIso.ofComponents (fun E ↦ ObjectProperty.isoMk P
      (asIso (ringedCechCompletionUnit R K ε E.obj) ≪≫ (θ.app E.obj).symm)) (by
        intro E E' f
        apply ObjectProperty.hom_ext
        change f.hom ≫ (ringedCechCompletionUnit R K ε E'.obj ≫ θ.inv.app E'.obj) =
          (ringedCechCompletionUnit R K ε E.obj ≫ θ.inv.app E.obj) ≫
            r.map (F.map f.hom)
        rw [← Category.assoc, ← hnatural E.obj E'.obj f.hom, Category.assoc]
        rw [θ.inv.naturality f.hom]
        exact (Category.assoc _ _ _).symm)
  let β' : 𝟭 Q.FullSubcategory ⟶ s ⋙ G :=
    { app M := ObjectProperty.homMk (β.app M.obj)
      naturality M N f := by
        apply ObjectProperty.hom_ext
        exact β.naturality f.hom }
  apply siteCompleteRestrictScalars_equivalence_of_inverse φ I G α β'
  intro M
  apply (ObjectProperty.isIso_hom_iff _).mp
  change IsIso (r.map (β.app M.obj))
  have : IsIso (ringedCechCompletionUnit R K ε (r.obj M.obj)) :=
    hunit _ (s.obj M).property
  have : IsIso (r.map (β.app M.obj) ≫ θ.hom.app (r.obj M.obj)) := by
    rw [hβ]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (θ.hom.app (r.obj M.obj))

-- The localization comparison contains both product variables and resolution functors.
set_option backward.isDefEq.respectTransparency false in
private theorem ringedDerivedHomUnit_Q_obj
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (siteModuleRings O))]
    (M : ringedSiteComplex O) :
    let A := SheafOfModules.{u} (siteModuleRings O)
    letI : IsGrothendieckAbelian.{u} A := SheafOfModules.isGrothendieckAbelian _
    let I := CochainComplex.kInjectiveResolutionFunctor.{u} A
    let η := CochainComplex.toKInjectiveResolution.{u} A
    let Q := DerivedCategory.Q (C := A)
    let c := Localization.fac
      ((𝟭 _).prod I ⋙ Functor.uncurry.obj (homComplexFunctor (R := O)) ⋙ Q)
      (derivedInternalHom_inverts J O I η (fun M ↦
        ⟨(CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{u} A M).2,
          CochainComplex.isKInjective_kInjectiveResolutionFunctor_obj.{u} A M⟩))
      (Q.op.prod Q)
    ringedDerivedHomUnit O (Q.obj M) =
      Q.map (η.app M) ≫ (Q.mapIso (ringedHomUnitEvaluationIso O (I.obj M))).inv ≫
        c.inv.app (Opposite.op (ringedSiteRingComplex O), M) := by
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
      exact ringedHomUnitEvaluationIso_naturality O f)
  let v : Q ⋙ F ≅ I ⋙ (homComplexFunctor (R := O)).obj
      (Opposite.op (ringedSiteRingComplex O)) ⋙ Q :=
    NatIso.ofComponents (fun M ↦ c.app (Opposite.op (ringedSiteRingComplex O), M)) (by
      intro M N f
      have hc := c.hom.naturality
        (X := (Opposite.op (ringedSiteRingComplex O), M))
        (Y := (Opposite.op (ringedSiteRingComplex O), N)) (𝟙 _, f)
      dsimp at hc
      simp only [Functor.map_id, NatTrans.id_app, Category.id_comp, op_id] at hc
      change H.map
          (X := (Opposite.op (Q.obj (ringedSiteRingComplex O)), Q.obj M))
          (Y := (Opposite.op (Q.obj (ringedSiteRingComplex O)), Q.obj N))
          (𝟙 _, Q.map f) ≫ c.hom.app (Opposite.op (ringedSiteRingComplex O), N) =
        c.hom.app (Opposite.op (ringedSiteRingComplex O), M) ≫
          Q.map (((homComplexFunctor (R := O)).obj
            (Opposite.op (ringedSiteRingComplex O))).map (I.map f))
      exact hc)
  let t : Q ⋙ 𝟭 _ ⟶ Q ⋙ F :=
    Functor.whiskerRight η Q ≫
      Functor.whiskerRight (Functor.whiskerLeft I a.inv) Q ≫ v.inv
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
    simp only [ringedDerivedHomUnit, t, v, a, e, Q, I, η, c,
      NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Category.assoc, Iso.hom_inv_id_assoc]
    rfl
  exact (hu (Q.obj M)).trans (hd M)

-- Computing the unit unfolds the product localization and its chosen resolution.
set_option backward.isDefEq.respectTransparency false in
private theorem ringedCechCompletionUnit_Q_obj
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (siteModuleRings R))]
    (K : ringedSiteComplex R) (ε : K ⟶ ringedSiteRingComplex R)
    (M : ringedSiteComplex R) :
    let A := SheafOfModules.{u} (siteModuleRings R)
    letI : IsGrothendieckAbelian.{u} A := SheafOfModules.isGrothendieckAbelian _
    let I := CochainComplex.kInjectiveResolutionFunctor.{u} A
    let η := CochainComplex.toKInjectiveResolution.{u} A
    let Q := DerivedCategory.Q (C := A)
    let c : Q.op.prod Q ⋙ derivedInternalHom J R ≅
        (𝟭 _).prod I ⋙ Functor.uncurry.obj (homComplexFunctor (R := R)) ⋙ Q :=
      Localization.fac
      ((𝟭 _).prod I ⋙ Functor.uncurry.obj (homComplexFunctor (R := R)) ⋙ Q)
      (derivedInternalHom_inverts J R I η (fun M ↦
        ⟨(CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{u} A M).2,
          CochainComplex.isKInjective_kInjectiveResolutionFunctor_obj.{u} A M⟩))
      (Q.op.prod Q)
    ringedCechCompletionUnit R K ε (Q.obj M) =
      Q.map (η.app M ≫ (ringedHomUnitEvaluationIso R (I.obj M)).inv ≫
        ((homComplexFunctor (R := R)).map ε.op).app (I.obj M)) ≫
          c.inv.app (Opposite.op K, M) := by
  let A := SheafOfModules.{u} (siteModuleRings R)
  let : IsGrothendieckAbelian.{u} A := SheafOfModules.isGrothendieckAbelian _
  let I := CochainComplex.kInjectiveResolutionFunctor.{u} A
  let η := CochainComplex.toKInjectiveResolution.{u} A
  let Q := DerivedCategory.Q (C := A)
  let c : Q.op.prod Q ⋙ derivedInternalHom J R ≅
      (𝟭 _).prod I ⋙ Functor.uncurry.obj (homComplexFunctor (R := R)) ⋙ Q :=
    Localization.fac
    ((𝟭 _).prod I ⋙ Functor.uncurry.obj (homComplexFunctor (R := R)) ⋙ Q)
    (derivedInternalHom_inverts J R I η (fun M ↦
      ⟨(CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{u} A M).2,
        CochainComplex.isKInjective_kInjectiveResolutionFunctor_obj.{u} A M⟩))
    (Q.op.prod Q)
  change ringedCechCompletionUnit R K ε (Q.obj M) =
    Q.map (η.app M ≫ (ringedHomUnitEvaluationIso R (I.obj M)).inv ≫
      ((homComplexFunctor (R := R)).map ε.op).app (I.obj M)) ≫
        c.inv.app (Opposite.op K, M)
  have hc := c.inv.naturality (X := (Opposite.op (ringedSiteRingComplex R), M))
    (Y := (Opposite.op K, M)) (ε.op, 𝟙 M)
  dsimp at hc
  simp only [Functor.map_id, Category.comp_id] at hc
  unfold ringedCechCompletionUnit
  have hu := ringedDerivedHomUnit_Q_obj R M
  change ringedDerivedHomUnit R (Q.obj M) =
    Q.map (η.app M) ≫ Q.map (ringedHomUnitEvaluationIso R (I.obj M)).inv ≫
      c.inv.app (Opposite.op (ringedSiteRingComplex R), M) at hu
  rw [hu]
  simp only [Functor.map_comp, Category.assoc]
  rw [← hc]

set_option backward.isDefEq.respectTransparency false in
private theorem derivedCoefficientHomFunctor
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    {R B : Sheaf J CommRingCat.{u}} (φ : R ⟶ B)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (siteModuleRings R))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (siteModuleRings B))]
    (L : ringedSiteComplex B)
    (G : ringedSiteComplex R ⥤ ringedSiteComplex B)
    (c : G ⋙ (SheafOfModules.restrictScalars.{u}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)).mapHomologicalComplex
          (.up ℤ) ≅
      (homComplexFunctor (R := R)).obj
        (Opposite.op (((SheafOfModules.restrictScalars.{u}
          ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)).mapHomologicalComplex
            (.up ℤ)).obj L))) :
    let A := SheafOfModules.{u} (siteModuleRings R)
    letI : IsGrothendieckAbelian.{u} A := SheafOfModules.isGrothendieckAbelian _
    let I := CochainComplex.kInjectiveResolutionFunctor.{u} A
    let QR := DerivedCategory.Q (C := A)
    let QB := DerivedCategory.Q (C := SheafOfModules.{u} (siteModuleRings B))
    ∃ (F : ringedSiteDerived R ⥤ ringedSiteDerived B),
      Nonempty (QR ⋙ F ≅ I ⋙ G ⋙ QB) := by
  let A := SheafOfModules.{u} (siteModuleRings R)
  let : IsGrothendieckAbelian.{u} A := SheafOfModules.isGrothendieckAbelian _
  let r := SheafOfModules.restrictScalars.{u}
    ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)
  let := (siteRestrictScalars_exact φ).1
  let := (siteRestrictScalars_exact φ).2
  let rc := r.mapHomologicalComplex (.up ℤ)
  let I := CochainComplex.kInjectiveResolutionFunctor.{u} A
  let η := CochainComplex.toKInjectiveResolution.{u} A
  let QR := DerivedCategory.Q (C := A)
  let QB := DerivedCategory.Q (C := SheafOfModules.{u} (siteModuleRings B))
  let H := (homComplexFunctor (R := R)).obj (Opposite.op (rc.obj L))
  let cL : G ⋙ rc ≅ H := c
  have hinv : (HomologicalComplex.quasiIso A (.up ℤ)).IsInvertedBy
      (I ⋙ G ⋙ QB) := by
    intro M N f hf
    have : QuasiIso f := hf
    have : QuasiIso (η.app M) :=
      (CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{u} A M).2
    have : QuasiIso (η.app N) :=
      (CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{u} A N).2
    have hη : QuasiIso (η.app M ≫ I.map f) := by
      rw [← η.naturality f]
      dsimp
      infer_instance
    have : QuasiIso (I.map f) := (quasiIso_iff_comp_left _ _).mp hη
    have : (I.obj M).IsKInjective :=
      CochainComplex.isKInjective_kInjectiveResolutionFunctor_obj.{u} A M
    have : (I.obj N).IsKInjective :=
      CochainComplex.isKInjective_kInjectiveResolutionFunctor_obj.{u} A N
    have hh : QuasiIso (H.map (I.map f)) := by
      simpa [H] using quasiIso_homComplex_map (I.map f) (𝟙 (rc.obj L))
    have hr : QuasiIso (rc.map ((G).map (I.map f))) := by
      exact (quasiIso_iff_of_arrow_mk_iso
        (rc.map ((G).map (I.map f))) (H.map (I.map f))
        (Arrow.isoMk (cL.app (I.obj M)) (cL.app (I.obj N))
          (cL.hom.naturality (I.map f)).symm)).mpr hh
    have : QuasiIso ((G).map (I.map f)) :=
      (siteRestrictScalars_quasiIso_iff φ _).mp hr
    exact (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).mpr inferInstance
  let F := Localization.lift (I ⋙ G ⋙ QB) hinv QR
  let fF := Localization.fac (I ⋙ G ⋙ QB) hinv QR
  exact ⟨F, ⟨fF⟩⟩

-- Check unit compatibility after transporting to a representative and a comparison object.
-- Keeping the cancellation argument categorical avoids unfolding the concrete resolutions.
private theorem unitCompatibility_of_representative
    {A B : Type*} [Category A] [Category B]
    (F : A ⥤ B) (r : B ⥤ A) (H : A ⥤ A)
    (β : 𝟭 B ⟶ r ⋙ F) (θ : F ⋙ r ⟶ H) (η : 𝟭 A ⟶ H)
    {X : B} {Y Z : A} {W : B}
    (e : r.obj X ≅ Y) (a : F.obj Y ≅ W) (b : X ⟶ W)
    (d : H.obj Y ≅ Z) (v : r.obj W ⟶ Z)
    (hβ : β.app X = b ≫ a.inv ≫ F.map e.inv)
    (hθ : θ.app Y ≫ d.hom = r.map a.hom ≫ v)
    (hb : r.map b ≫ v = e.hom ≫ η.app Y ≫ d.hom) :
    r.map (β.app X) ≫ θ.app (r.obj X) = η.app (r.obj X) := by
  apply (cancel_mono (H.map e.hom)).mp
  apply (cancel_mono d.hom).mp
  have hn := θ.naturality e.hom
  change r.map (F.map e.hom) ≫ θ.app Y = θ.app (r.obj X) ≫ H.map e.hom at hn
  have hη := η.naturality e.hom
  change e.hom ≫ η.app Y = η.app (r.obj X) ≫ H.map e.hom at hη
  have hc : β.app X ≫ F.map e.hom = b ≫ a.inv := by
    rw [hβ]
    simp only [Category.assoc, ← F.map_comp, Iso.inv_hom_id, F.map_id, Category.comp_id]
  calc
    ((r.map (β.app X) ≫ θ.app (r.obj X)) ≫ H.map e.hom) ≫ d.hom =
        r.map (β.app X ≫ F.map e.hom) ≫ (θ.app Y ≫ d.hom) := by
      rw [r.map_comp]
      simp only [Category.assoc]
      rw [reassoc_of% hn]
    _ = r.map b ≫ v := by
      rw [hc, hθ]
      simpa only [Functor.map_comp, Functor.mapIso_inv, Functor.mapIso_hom, Category.assoc] using
        congrArg (fun z ↦ r.map b ≫ z) ((r.mapIso a).inv_hom_id_assoc v)
    _ = e.hom ≫ η.app Y ≫ d.hom := hb
    _ = (η.app (r.obj X) ≫ H.map e.hom) ≫ d.hom := by
      rw [← Category.assoc, hη]

-- The localization comparison involves three resolutions and several whiskered isomorphisms.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Restriction of scalars along a flat ring-sheaf map which is an isomorphism modulo a
locally finitely generated ideal induces an equivalence of the locally derived complete
full subcategories. The natural isomorphism in the conclusion identifies the equivalence
with the specified derived restriction functor on the ambient categories.

Source: Stacks Project, Algebraization, Tags 099I and 0999
(auxiliary; not a blueprint node).

Proof:
1. Restriction of scalars is exact and conservative, since its underlying additive sheaf
is unchanged. It therefore induces the stated derived functor. By
`lem-weil-pbc-restriction-local-completeness`, it preserves and reflects local completeness.
2. Choose the augmented extended Cech model `K → R[0]` from
`lem-weil-pbc-extended-cech-completion-model`. Flatness makes termwise tensoring with `B`
exact, giving `K_B → B[0]` and `u : K → r K_B`. On every generating slice, localization
commutes with tensor: `(a/f^n) ⊗ b ↦ φ(a)b/φ(f)^n` with inverse
`b/φ(f)^n ↦ (1/f^n) ⊗ b`. Finite products in this model are finite direct sums.
Slice restriction is exact (`lem-weil-pbc-site-restriction-exact`) and preserves quotients;
flatness restricts (`lem-weil-pbc-slice-restriction-flat`). Apply
`lem-weil-pbc-flat-extended-cech-comparison` locally to deduce that `u` is a quasi-isomorphism.
3. Define `F(E)` by the Hom complex from `r K_B` into the functorial K-injective replacement
of a representative of `E`, with action `(b h)(k) = h(bk)`. This action commutes with the
Hom differential and with restrictions. Naturality and two-out-of-three show replacement
maps preserve quasi-isomorphisms; `lem-pur-rhom-well-defined` then makes the Hom maps
quasi-isomorphisms. Thus the construction descends to a functor `D(R) → D(B)`.
4. Precomposition with `u` identifies `r F(E)` with `RHom_R(K,E)`. For complete `E`, the
completion unit identifies this with `E`, naturally. Completeness is reflected by `r`,
so `F` also restricts to the complete subcategories.
5. For complete `M` over `B`, send a homogeneous `m` to the cochain
`k ↦ q(ε_B(k)m)`, zero off degree zero of `k`. This is a chain map because `ε_B d_K = 0`
and `q` is a chain map. It is `B`-linear under the action in step 3, and natural. After
precomposition with `u`, it is exactly the completion unit of `r M`. Hence its restriction
is an isomorphism by step 4; conservativity of restriction makes it an isomorphism over
`B`. These two natural isomorphisms exhibit the equivalence asserted here. -/
theorem flat_ringed_ideal_complete_equivalence
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    {R B : Sheaf J CommRingCat.{u}} (φ : R ⟶ B) (I : RingedSiteIdeal R)
    [HasDerivedCategory.{w} (ringedSiteModules.{u} (siteModuleRings R))]
    [HasDerivedCategory.{w} (ringedSiteModules.{u} (siteModuleRings B))]
    [∀ U : C, HasDerivedCategory.{w}
      (ringedSiteModules.{u} (siteModuleRings (R.over U)))]
    [∀ U : C, HasDerivedCategory.{w}
      (ringedSiteModules.{u} (siteModuleRings (B.over U)))]
    (hI : SheafOfModules.IsFiniteType.{u, u, u} I.module)
    (hflat : SheafOfModules.IsFlat
      ((SheafOfModules.restrictScalars.{u}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)).obj
          (SheafOfModules.unit (siteModuleRings B))))
    (hquot : I.IsQuotientIso φ) :
    ∃ e : ObjectProperty.FullSubcategory
        (IsLocallyDerivedRingedIdealComplete B (I.extension φ).module (I.extension φ).inclusion) ≌
        ObjectProperty.FullSubcategory
          (IsLocallyDerivedRingedIdealComplete R I.module I.inclusion),
      Nonempty (e.functor ⋙
        ObjectProperty.ι (IsLocallyDerivedRingedIdealComplete R I.module I.inclusion) ≅
        ObjectProperty.ι
          (IsLocallyDerivedRingedIdealComplete B (I.extension φ).module (I.extension φ).inclusion) ⋙
          siteDerivedRestrictScalars φ) := by
  let := hI
  have : Mono I.inclusion := by
    constructor
    intro Z f g h
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro X
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    apply Subtype.ext
    exact congrArg (fun k ↦ k.val.app X z) h
  obtain ⟨K, ε, hK⟩ := exists_ringedExtendedCech_global_model J R I.module I.inclusion
  obtain ⟨L, δ, u, hu, haug⟩ :=
    exists_flat_ringedCech_baseChange φ I hI hflat hquot K ε hK
  have : QuasiIso u := hu
  let A := SheafOfModules.{u} (siteModuleRings R)
  let : IsGrothendieckAbelian.{u} A := SheafOfModules.isGrothendieckAbelian _
  let T := CochainComplex.kInjectiveResolutionFunctor.{u} A
  let η := CochainComplex.toKInjectiveResolution.{u} A
  let QR := DerivedCategory.Q (C := A)
  let QB := DerivedCategory.Q (C := SheafOfModules.{u} (siteModuleRings B))
  let r := SheafOfModules.restrictScalars.{u}
    ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)
  let := (siteRestrictScalars_exact φ).1
  let := (siteRestrictScalars_exact φ).2
  let rc := r.mapHomologicalComplex (.up ℤ)
  let rD := siteDerivedRestrictScalars φ
  let eR : QB ⋙ rD ≅ rc ⋙ QR := r.mapDerivedCategoryFactors
  obtain ⟨G, c, b, hb⟩ := exists_coefficientHom_augmentation φ K ε L δ T η u haug
  obtain ⟨F, ⟨a₀⟩⟩ := derivedCoefficientHomFunctor φ L G c
  let a : QR ⋙ F ≅ T ⋙ G ⋙ QB := a₀
  let d : QR.op.prod QR ⋙ derivedInternalHom J R ≅
      (𝟭 _).prod T ⋙ Functor.uncurry.obj (homComplexFunctor (R := R)) ⋙ QR :=
    Localization.fac
      ((𝟭 _).prod T ⋙ Functor.uncurry.obj (homComplexFunctor (R := R)) ⋙ QR)
      (derivedInternalHom_inverts J R T η (fun M ↦
        ⟨(CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{u} A M).2,
          CochainComplex.isKInjective_kInjectiveResolutionFunctor_obj.{u} A M⟩))
      (QR.op.prod QR)
  let dL : QR ⋙ ringedCechCompletionFunctor R (rc.obj L) ≅
      T ⋙ (homComplexFunctor (R := R)).obj (Opposite.op (rc.obj L)) ⋙ QR :=
    NatIso.ofComponents (fun M ↦ d.app (Opposite.op (rc.obj L), M)) (by
      intro M N f
      simpa [ringedCechCompletionFunctor] using d.hom.naturality
        (X := (Opposite.op (rc.obj L), M))
        (Y := (Opposite.op (rc.obj L), N)) (𝟙 _, f))
  let e : QR ⋙ (F ⋙ rD) ≅ QR ⋙ ringedCechCompletionFunctor R (rc.obj L) :=
    Functor.isoWhiskerRight a rD ≪≫ Functor.isoWhiskerLeft (T ⋙ G) eR ≪≫
      Functor.isoWhiskerRight (Functor.isoWhiskerLeft T c) QR ≪≫ dL.symm
  let fullR := Localization.fullyFaithfulWhiskeringLeft QR
    (HomologicalComplex.quasiIso A (.up ℤ)) (ringedSiteDerived R)
  let θ : F ⋙ rD ≅ ringedCechCompletionFunctor R (rc.obj L) := fullR.preimageIso e
  have hθ (M : ringedSiteComplex R) : θ.hom.app (QR.obj M) = e.hom.app M :=
    congrArg (fun z ↦ z.app M) (fullR.map_preimage e.hom)
  have : IsIso (QR.map u) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ u).mpr hu
  let τ : ringedCechCompletionFunctor R (rc.obj L) ⟶ ringedCechCompletionFunctor R K :=
    (Functor.curry.obj (derivedInternalHom J R)).map (QR.map u).op
  have : IsIso τ := by dsimp [τ]; infer_instance
  let Θ : F ⋙ rD ≅ ringedCechCompletionFunctor R K := θ ≪≫ asIso τ
  let t : QB ⋙ 𝟭 (ringedSiteDerived B) ⟶ QB ⋙ (rD ⋙ F) :=
    Functor.whiskerRight b QB ≫ Functor.whiskerLeft rc a.inv ≫
      Functor.whiskerRight eR.inv F
  let fullB := Localization.fullyFaithfulWhiskeringLeft QB
    (HomologicalComplex.quasiIso (SheafOfModules.{u} (siteModuleRings B)) (.up ℤ))
    (ringedSiteDerived B)
  let β : 𝟭 (ringedSiteDerived B) ⟶ rD ⋙ F := fullB.preimage t
  have hβQ (M : ringedSiteComplex B) : β.app (QB.obj M) =
      QB.map (b.app M) ≫ a.inv.app (rc.obj M) ≫ F.map (eR.inv.app M) := by
    exact congrArg (fun z ↦ z.app M) (fullB.map_preimage t)
  obtain ⟨_, hnatural, _, _⟩ :=
    ringedExtendedCech_reflector_properties J R I.module I.inclusion K ε hK
  let dK (M : ringedSiteComplex R) :
      (ringedCechCompletionFunctor R K).obj (QR.obj M) ≅
        QR.obj (((homComplexFunctor (R := R)).obj (Opposite.op K)).obj (T.obj M)) := by
    exact d.app (Opposite.op K, M)
  have hΘ (M : ringedSiteComplex R) :
      Θ.hom.app (QR.obj M) ≫ (dK M).hom =
        rD.map (a.hom.app M) ≫ eR.hom.app (G.obj (T.obj M)) ≫
          QR.map (c.hom.app (T.obj M) ≫
            ((homComplexFunctor (R := R)).map u.op).app (T.obj M)) := by
    have hd := d.hom.naturality (X := (Opposite.op (rc.obj L), M))
      (Y := (Opposite.op K, M)) (u.op, 𝟙 M)
    dsimp at hd
    simp only [Functor.map_id, Category.comp_id] at hd
    change τ.app (QR.obj M) ≫ (dK M).hom =
      dL.hom.app M ≫ QR.map
        (((homComplexFunctor (R := R)).map u.op).app (T.obj M)) at hd
    change (θ.hom.app (QR.obj M) ≫ τ.app (QR.obj M)) ≫ _ = _
    rw [Category.assoc, hd, ← Category.assoc, hθ M]
    simp only [e, dL, Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerRight_hom,
      Functor.isoWhiskerLeft_hom, NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app, Functor.comp_obj, Category.assoc, Functor.map_comp,
      Iso.inv_hom_id_app, Category.comp_id]
  have hunitQ (M : ringedSiteComplex R) :
      ringedCechCompletionUnit R K ε (QR.obj M) ≫ (dK M).hom =
        QR.map (η.app M ≫ (ringedHomUnitEvaluationIso R (T.obj M)).inv ≫
          ((homComplexFunctor (R := R)).map ε.op).app (T.obj M)) := by
    have h := ringedCechCompletionUnit_Q_obj R K ε M
    change ringedCechCompletionUnit R K ε (QR.obj M) =
      QR.map (η.app M ≫ (ringedHomUnitEvaluationIso R (T.obj M)).inv ≫
        ((homComplexFunctor (R := R)).map ε.op).app (T.obj M)) ≫
          (dK M).inv at h
    exact (Iso.eq_comp_inv (dK M)).mp h
  let ηK : 𝟭 (ringedSiteDerived R) ⟶ ringedCechCompletionFunctor R K :=
    { app := ringedCechCompletionUnit R K ε
      naturality E E' f := (hnatural E E' f).symm }
  have hrep (M : ringedSiteComplex B) :
      rD.map (β.app (QB.obj M)) ≫ Θ.hom.app (rD.obj (QB.obj M)) =
        ringedCechCompletionUnit R K ε (rD.obj (QB.obj M)) := by
    refine unitCompatibility_of_representative F rD (ringedCechCompletionFunctor R K)
      β Θ.hom ηK (eR.app M) (a.app (rc.obj M)) (QB.map (b.app M)) (dK (rc.obj M))
      (eR.hom.app (G.obj (T.obj (rc.obj M))) ≫
        QR.map (c.hom.app (T.obj (rc.obj M)) ≫
          ((homComplexFunctor (R := R)).map u.op).app (T.obj (rc.obj M))))
      (hβQ M) (hΘ (rc.obj M)) ?_
    have heR : rD.map (QB.map (b.app M)) ≫ eR.hom.app (G.obj (T.obj (rc.obj M))) =
        eR.hom.app M ≫ QR.map (rc.map (b.app M)) :=
      eR.hom.naturality (b.app M)
    rw [← Category.assoc, heR, Category.assoc, ← QR.map_comp]
    rw [hb M]
    exact congrArg (fun z ↦ eR.hom.app M ≫ z) (hunitQ (rc.obj M)).symm
  -- Equality on complex representatives descends to all derived objects.
  have hβ : Functor.whiskerRight β rD ≫ Functor.whiskerLeft rD Θ.hom =
      Functor.whiskerLeft rD ηK := by
    apply Localization.natTrans_ext QB
      (HomologicalComplex.quasiIso (SheafOfModules.{u} (siteModuleRings B)) (.up ℤ))
    intro M
    exact hrep M
  apply siteCompleteRestrictScalars_equivalence_of_completion φ I hI K ε hK F Θ β
  intro M
  exact congrArg (fun z ↦ z.app M) hβ

end CategoryTheory
