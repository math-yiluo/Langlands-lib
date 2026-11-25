/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Abelian.RightDerived.ResolutionNaturality
public import WeilConjectures.AlgebraicGeometry.Cohomology.Restriction
public import WeilConjectures.AlgebraicGeometry.Cohomology.Derived.Basic
public import WeilConjectures.AlgebraicGeometry.Cohomology.Flasque

/-!
# Cohomology of an open subscheme computed by complexes on the ambient scheme

Let `Ω` be an open of a scheme `X`. A complex `A` of `𝒪_X`-modules with an augmentation
`ℱ ⟶ A⁰` is an **`Ω`-resolution** of `ℱ` (`AlgebraicGeometry.Scheme.Modules.IsOpenResolution`)
if its restriction to `Ω` is a resolution of `ℱ|_Ω` by modules which are acyclic for the global
sections functor of `Ω`. Then the cohomology `H^q(Ω, ℱ)` is the cohomology of the complex
`Γ(Ω, A)` of sections of `A` over `Ω`.

The point of working with complexes on `X` rather than on `Ω` is that the same complex can be an
`Ω`-resolution for several opens `Ω`, and that the restriction maps `Γ(Ω₁, A) ⟶ Γ(Ω₂, A)` for
`Ω₂ ≤ Ω₁` are then compatible with the identifications of the cohomologies of two resolutions
(`AlgebraicGeometry.Scheme.Modules.openComparison_naturality`).

## Main definitions

- `AlgebraicGeometry.Scheme.Modules.IsOpenResolution`: `Ω`-resolutions.
- `AlgebraicGeometry.Scheme.Modules.openComparison`: the identification
  `H^q(Γ(Ω, A)) ≅ H^q(Γ(Ω, B))` for two `Ω`-resolutions `A` and `B` of the same module.

## Main statements

- `AlgebraicGeometry.Scheme.Modules.openComparison_hom_eq`: the identification is induced by any
  cochain map `A ⟶ B` compatible with the augmentations.
- `AlgebraicGeometry.Scheme.Modules.openComparison_naturality`: the identification commutes with
  the restriction to a smaller open.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- Flasque modules are acyclic for the global sections functor. -/
theorem rightAcyclic_globalSections_of_isFlasque (ℱ : X.Modules)
    (h : TopCat.Presheaf.IsFlasque ℱ.presheaf) : (globalSectionsFunctor X).rightAcyclic ℱ :=
  rightAcyclic_of_isFlasque _ (fun _ hS h₁ ↦ epi_app_of_shortExact_of_isFlasque hS h₁ ⊤) ℱ h

variable (Ω : X.Opens)

/-- The restriction to the open `Ω` of an augmentation `ℱ ⟶ A` of a complex of `𝒪_X`-modules. -/
noncomputable def restrictAugmentation {ℱ : X.Modules} {A : CochainComplex X.Modules ℕ}
    (ι : (CochainComplex.single₀ X.Modules).obj ℱ ⟶ A) :
    (CochainComplex.single₀ Ω.toScheme.Modules).obj (ℱ.restrict Ω.ι) ⟶ restrictComplex Ω.ι A :=
  (HomologicalComplex.singleMapHomologicalComplex (restrictFunctor Ω.ι) (ComplexShape.up ℕ)
    0).inv.app ℱ ≫ ((restrictFunctor Ω.ι).mapHomologicalComplex _).map ι

/-- The functor of sections over the open `Ω`, as the global sections of the restriction. -/
noncomputable abbrev sectionsOver : X.Modules ⥤ Ab.{u} :=
  restrictFunctor Ω.ι ⋙ globalSectionsFunctor Ω

/-- The complex `Γ(Ω, A)` of sections over `Ω` of a complex of `𝒪_X`-modules. -/
noncomputable abbrev sectionsComplex (A : CochainComplex X.Modules ℕ) : CochainComplex Ab.{u} ℕ :=
  ((sectionsOver Ω).mapHomologicalComplex _).obj A

/-- A complex `A` of `𝒪_X`-modules with augmentation `ι : ℱ ⟶ A` is an **`Ω`-resolution** of `ℱ`
if its restriction to `Ω` is a resolution of `ℱ|_Ω` by modules which are acyclic for the global
sections functor of `Ω`. -/
structure IsOpenResolution {ℱ : X.Modules} {A : CochainComplex X.Modules ℕ}
    (ι : (CochainComplex.single₀ X.Modules).obj ℱ ⟶ A) : Prop where
  quasiIso : QuasiIso (restrictAugmentation Ω ι)
  rightAcyclic (n : ℕ) : (globalSectionsFunctor Ω).rightAcyclic ((A.X n).restrict Ω.ι)

variable {Ω}

/-- The restriction of a compatible pair of a morphism and a cochain map. -/
@[reassoc]
lemma restrictAugmentation_comp {ℱ 𝒢 : X.Modules} {A B : CochainComplex X.Modules ℕ}
    {ι : (CochainComplex.single₀ X.Modules).obj ℱ ⟶ A}
    {ι' : (CochainComplex.single₀ X.Modules).obj 𝒢 ⟶ B} (φ : ℱ ⟶ 𝒢) (c : A ⟶ B)
    (comm : ι ≫ c = (CochainComplex.single₀ X.Modules).map φ ≫ ι') :
    restrictAugmentation Ω ι ≫ ((restrictFunctor Ω.ι).mapHomologicalComplex _).map c =
      (CochainComplex.single₀ _).map ((restrictFunctor Ω.ι).map φ) ≫
        restrictAugmentation Ω ι' := by
  have h := (HomologicalComplex.singleMapHomologicalComplex (restrictFunctor Ω.ι)
    (ComplexShape.up ℕ) 0).inv.naturality φ
  dsimp only [Functor.comp_map] at h
  rw [restrictAugmentation, restrictAugmentation, Category.assoc, ← Functor.map_comp, comm,
    Functor.map_comp, ← Category.assoc, ← h, Category.assoc]

/-- The identification `H^q(Ω, ℱ) ≅ H^q(Γ(Ω, A))` for an `Ω`-resolution `A` of `ℱ`. -/
noncomputable def IsOpenResolution.iso {ℱ : X.Modules} {A : CochainComplex X.Modules ℕ}
    {ι : (CochainComplex.single₀ X.Modules).obj ℱ ⟶ A} (h : IsOpenResolution Ω ι) (q : ℕ) :
    ((globalSectionsFunctor Ω).rightDerived q).obj (ℱ.restrict Ω.ι) ≅
      (sectionsComplex Ω A).homology q :=
  haveI := h.quasiIso
  (globalSectionsFunctor Ω).rightDerivedObjIsoOfResolution (restrictAugmentation Ω ι)
    h.rightAcyclic q

/-- **Naturality of `IsOpenResolution.iso`** for a cochain map of complexes on `Ω`. -/
lemma IsOpenResolution.iso_hom_naturality' {ℱ 𝒢 : X.Modules} {A B : CochainComplex X.Modules ℕ}
    {ι : (CochainComplex.single₀ X.Modules).obj ℱ ⟶ A}
    {ι' : (CochainComplex.single₀ X.Modules).obj 𝒢 ⟶ B}
    (hA : IsOpenResolution Ω ι) (hB : IsOpenResolution Ω ι')
    (φ : ℱ.restrict Ω.ι ⟶ 𝒢.restrict Ω.ι) (c : restrictComplex Ω.ι A ⟶ restrictComplex Ω.ι B)
    (comm : restrictAugmentation Ω ι ≫ c =
      (CochainComplex.single₀ _).map φ ≫ restrictAugmentation Ω ι') (q : ℕ) :
    ((globalSectionsFunctor Ω).rightDerived q).map φ ≫ (hB.iso q).hom =
      (hA.iso q).hom ≫ HomologicalComplex.homologyMap
        (((globalSectionsFunctor Ω).mapHomologicalComplex _).map c) q := by
  have := hA.quasiIso
  have := hB.quasiIso
  refine (globalSectionsFunctor Ω).rightDerivedObjIsoOfResolution_hom_naturality _ _ _ _ φ c
    ?_ q
  have := congrArg (fun h ↦ HomologicalComplex.Hom.f h 0) comm
  simpa using this

/-- **Naturality of `IsOpenResolution.iso`** for a cochain map of complexes on `X`. -/
lemma IsOpenResolution.iso_hom_naturality {ℱ 𝒢 : X.Modules} {A B : CochainComplex X.Modules ℕ}
    {ι : (CochainComplex.single₀ X.Modules).obj ℱ ⟶ A}
    {ι' : (CochainComplex.single₀ X.Modules).obj 𝒢 ⟶ B}
    (hA : IsOpenResolution Ω ι) (hB : IsOpenResolution Ω ι') (φ : ℱ ⟶ 𝒢) (c : A ⟶ B)
    (comm : ι ≫ c = (CochainComplex.single₀ X.Modules).map φ ≫ ι') (q : ℕ) :
    ((globalSectionsFunctor Ω).rightDerived q).map ((restrictFunctor Ω.ι).map φ) ≫
        (hB.iso q).hom =
      (hA.iso q).hom ≫ HomologicalComplex.homologyMap
        (((sectionsOver Ω).mapHomologicalComplex _).map c) q :=
  hA.iso_hom_naturality' hB _ _ (restrictAugmentation_comp φ c comm) q

/-- The identification `H^q(Γ(Ω, A)) ≅ H^q(Γ(Ω, B))` of the cohomologies of two `Ω`-resolutions
of the same module, through `H^q(Ω, ℱ)`. -/
noncomputable def openComparison {ℱ : X.Modules} {A B : CochainComplex X.Modules ℕ}
    {ι : (CochainComplex.single₀ X.Modules).obj ℱ ⟶ A}
    {ι' : (CochainComplex.single₀ X.Modules).obj ℱ ⟶ B}
    (hA : IsOpenResolution Ω ι) (hB : IsOpenResolution Ω ι') (q : ℕ) :
    (sectionsComplex Ω A).homology q ≅ (sectionsComplex Ω B).homology q :=
  (hA.iso q).symm ≪≫ hB.iso q

lemma openComparison_refl {ℱ : X.Modules} {A : CochainComplex X.Modules ℕ}
    {ι : (CochainComplex.single₀ X.Modules).obj ℱ ⟶ A} (hA : IsOpenResolution Ω ι) (q : ℕ) :
    openComparison hA hA q = Iso.refl _ := by
  ext
  simp [openComparison]

lemma openComparison_trans {ℱ : X.Modules} {A B C : CochainComplex X.Modules ℕ}
    {ι : (CochainComplex.single₀ X.Modules).obj ℱ ⟶ A}
    {ι' : (CochainComplex.single₀ X.Modules).obj ℱ ⟶ B}
    {ι'' : (CochainComplex.single₀ X.Modules).obj ℱ ⟶ C}
    (hA : IsOpenResolution Ω ι) (hB : IsOpenResolution Ω ι') (hC : IsOpenResolution Ω ι'')
    (q : ℕ) : openComparison hA hB q ≪≫ openComparison hB hC q = openComparison hA hC q := by
  ext
  simp [openComparison]

lemma openComparison_symm {ℱ : X.Modules} {A B : CochainComplex X.Modules ℕ}
    {ι : (CochainComplex.single₀ X.Modules).obj ℱ ⟶ A}
    {ι' : (CochainComplex.single₀ X.Modules).obj ℱ ⟶ B}
    (hA : IsOpenResolution Ω ι) (hB : IsOpenResolution Ω ι') (q : ℕ) :
    (openComparison hA hB q).symm = openComparison hB hA q := by
  ext
  simp [openComparison]

/-- The identification of the cohomologies of two `Ω`-resolutions is induced by any cochain map
between them which is compatible with the augmentations. -/
lemma openComparison_hom_eq {ℱ : X.Modules} {A B : CochainComplex X.Modules ℕ}
    {ι : (CochainComplex.single₀ X.Modules).obj ℱ ⟶ A}
    {ι' : (CochainComplex.single₀ X.Modules).obj ℱ ⟶ B}
    (hA : IsOpenResolution Ω ι) (hB : IsOpenResolution Ω ι') (c : A ⟶ B) (comm : ι ≫ c = ι')
    (q : ℕ) :
    (openComparison hA hB q).hom =
      HomologicalComplex.homologyMap (((sectionsOver Ω).mapHomologicalComplex _).map c) q := by
  have h := hA.iso_hom_naturality hB (𝟙 ℱ) c (by rw [comm, CategoryTheory.Functor.map_id,
    Category.id_comp]) q
  rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, Category.id_comp] at h
  rw [openComparison, Iso.trans_hom, Iso.symm_hom, h, Iso.inv_hom_id_assoc]

/-- If two `Ω`-resolutions `A` and `B` of `ℱ` map compatibly to an `Ω`-resolution `P` of a module
`𝒢`, along a morphism `ℱ ⟶ 𝒢` which is an isomorphism on `Ω`, then their identification is
compatible with the induced maps to `H^q(Γ(Ω, P))`. -/
lemma openComparison_hom_comp_eq {ℱ 𝒢 : X.Modules} {A B P : CochainComplex X.Modules ℕ}
    {ι : (CochainComplex.single₀ X.Modules).obj ℱ ⟶ A}
    {ι' : (CochainComplex.single₀ X.Modules).obj ℱ ⟶ B}
    {ιP : (CochainComplex.single₀ X.Modules).obj 𝒢 ⟶ P}
    (hA : IsOpenResolution Ω ι) (hB : IsOpenResolution Ω ι') (hP : IsOpenResolution Ω ιP)
    (φ : ℱ ⟶ 𝒢) (a : A ⟶ P) (b : B ⟶ P)
    (ha : ι ≫ a = (CochainComplex.single₀ X.Modules).map φ ≫ ιP)
    (hb : ι' ≫ b = (CochainComplex.single₀ X.Modules).map φ ≫ ιP) (q : ℕ) :
    (openComparison hA hB q).hom ≫
        HomologicalComplex.homologyMap (((sectionsOver Ω).mapHomologicalComplex _).map b) q =
      HomologicalComplex.homologyMap (((sectionsOver Ω).mapHomologicalComplex _).map a) q := by
  have h₁ := hA.iso_hom_naturality hP φ a ha q
  have h₂ := hB.iso_hom_naturality hP φ b hb q
  rw [openComparison, Iso.trans_hom, Iso.symm_hom, Category.assoc, ← h₂,
    ← cancel_epi (hA.iso q).hom, Iso.hom_inv_id_assoc, h₁]

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

section Restrict

variable {Ω₁ Ω₂ : X.Opens} (h : Ω₂ ≤ Ω₁)

include h in
lemma ι_image_top_le : Ω₂.ι ''ᵁ ⊤ ≤ Ω₁.ι ''ᵁ ⊤ := by
  rw [Scheme.Opens.ι_image_top, Scheme.Opens.ι_image_top]
  exact h

/-- The restriction of sections `Γ(Ω₁, -) ⟶ Γ(Ω₂, -)` for opens `Ω₂ ≤ Ω₁`. -/
@[simps]
noncomputable def sectionsOverRestrict : sectionsOver Ω₁ ⟶ sectionsOver Ω₂ where
  app M := M.presheaf.map (homOfLE (ι_image_top_le h)).op
  naturality _ _ φ := (φ.mapPresheaf.naturality (homOfLE (ι_image_top_le h)).op).symm

/-- Restriction to `Ω₂` factors through restriction to `Ω₁ ≥ Ω₂`. -/
noncomputable def restrictFunctorIsoOfLE :
    restrictFunctor Ω₂.ι ≅ restrictFunctor Ω₁.ι ⋙ restrictFunctor (X.homOfLE h) :=
  restrictFunctorCongr (X.homOfLE_ι h).symm ≪≫ restrictFunctorComp (X.homOfLE h) Ω₁.ι

include h in
/-- A complex on `X` whose augmentation is a quasi-isomorphism on `Ω₁` is a quasi-isomorphism on
every smaller open `Ω₂`. -/
lemma quasiIso_restrictAugmentation_of_le {ℱ : X.Modules} {A : CochainComplex X.Modules ℕ}
    (ι : (CochainComplex.single₀ X.Modules).obj ℱ ⟶ A)
    (hι : QuasiIso (restrictAugmentation Ω₁ ι)) : QuasiIso (restrictAugmentation Ω₂ ι) := by
  let k := X.homOfLE h
  let e := restrictFunctorIsoOfLE h
  let iso : Arrow.mk (restrictAugmentation Ω₂ ι) ≅
      Arrow.mk (((restrictFunctor k).mapHomologicalComplex _).map (restrictAugmentation Ω₁ ι)) :=
    Arrow.isoMk ((CochainComplex.single₀ _).mapIso (e.app ℱ) ≪≫
      ((HomologicalComplex.singleMapHomologicalComplex (restrictFunctor k) (ComplexShape.up ℕ)
        0).app (ℱ.restrict Ω₁.ι)).symm)
      ((NatIso.mapHomologicalComplex e _).app A) (by
        refine HomologicalComplex.from_single_hom_ext ?_
        simp only [restrictAugmentation, e, k, CochainComplex.single₀_obj_zero, Arrow.mk_right,
          Arrow.mk_left, Functor.comp_obj, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom,
          Iso.symm_hom, Iso.app_inv, Arrow.mk_hom, Category.assoc, HomologicalComplex.comp_f,
          CochainComplex.single₀_map_f_zero,
          HomologicalComplex.singleMapHomologicalComplex_inv_app_self,
          CochainComplex.single₀ObjXSelf, Iso.refl_hom, Iso.refl_inv,
          CategoryTheory.Functor.map_id,
          Category.comp_id, Functor.mapHomologicalComplex_map_f,
          NatIso.mapHomologicalComplex_hom_app_f, Category.id_comp, Functor.map_comp]
        exact ((restrictFunctorIsoOfLE h).hom.naturality _).symm)
  exact (quasiIso_iff_of_arrow_mk_iso _ _ iso).2 inferInstance

end Restrict

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

section Pushforward

variable (Ω : X.Opens) (ℱ : X.Modules)

/-- The pushforward to `X` of the chosen injective resolution of `ℱ|_Ω`. -/
noncomputable def pushforwardResolution : CochainComplex X.Modules ℕ :=
  ((pushforward Ω.ι).mapHomologicalComplex _).obj (injectiveResolution (ℱ.restrict Ω.ι)).cocomplex

/-- The augmentation `j_* (ℱ|_Ω) ⟶ j_* I` of
`AlgebraicGeometry.Scheme.Modules.pushforwardResolution`, for `j : Ω ⟶ X` the inclusion. -/
noncomputable def pushforwardResolutionι :
    (CochainComplex.single₀ X.Modules).obj ((pushforward Ω.ι).obj (ℱ.restrict Ω.ι)) ⟶
      pushforwardResolution Ω ℱ :=
  (HomologicalComplex.singleMapHomologicalComplex (pushforward Ω.ι) (ComplexShape.up ℕ)
    0).inv.app _ ≫
    ((pushforward Ω.ι).mapHomologicalComplex _).map (injectiveResolution (ℱ.restrict Ω.ι)).ι

lemma isFlasque_restrict_pushforwardResolution_X {Ω' : X.Opens} (n : ℕ) :
    TopCat.Presheaf.IsFlasque (((pushforwardResolution Ω ℱ).X n).restrict Ω'.ι).presheaf :=
  isFlasque_restrict _ _ (isFlasque_pushforward _ _ (isFlasque_of_injective _))

lemma isOpenResolution_pushforwardResolution :
    IsOpenResolution Ω (pushforwardResolutionι Ω ℱ) := by
  refine ⟨?_, fun n ↦ rightAcyclic_globalSections_of_isFlasque _
    (isFlasque_restrict_pushforwardResolution_X Ω ℱ n)⟩
  let J := injectiveResolution (ℱ.restrict Ω.ι)
  let c := restrictFunctorAdjCounitIso Ω.ι
  let iso : Arrow.mk (restrictAugmentation Ω (pushforwardResolutionι Ω ℱ)) ≅ Arrow.mk J.ι :=
    Arrow.isoMk ((CochainComplex.single₀ _).mapIso (c.app _))
      ((NatIso.mapHomologicalComplex c _).app J.cocomplex ≪≫
        (Functor.mapHomologicalComplexIdIso _ _).app J.cocomplex) (by
        refine HomologicalComplex.from_single_hom_ext ?_
        simp only [restrictAugmentation, pushforwardResolutionι, c, J,
          CochainComplex.single₀_obj_zero,
          Arrow.mk_right, Arrow.mk_left, Functor.mapIso_hom, Iso.app_hom, Arrow.mk_hom,
          HomologicalComplex.comp_f, CochainComplex.single₀_map_f_zero, Iso.trans_hom,
          NatIso.mapHomologicalComplex_hom_app_f, Functor.mapHomologicalComplexIdIso_hom_app_f]
        erw [Category.id_comp, Category.comp_id]
        exact ((restrictFunctorAdjCounitIso Ω.ι).hom.naturality _).symm)
  exact (quasiIso_iff_of_arrow_mk_iso _ _ iso).2 inferInstance

lemma isOpenResolution_pushforwardResolution_of_le {Ω' : X.Opens} (h : Ω' ≤ Ω) :
    IsOpenResolution Ω' (pushforwardResolutionι Ω ℱ) :=
  ⟨quasiIso_restrictAugmentation_of_le h _
      (isOpenResolution_pushforwardResolution Ω ℱ).quasiIso,
    fun n ↦ rightAcyclic_globalSections_of_isFlasque _
      (isFlasque_restrict_pushforwardResolution_X Ω ℱ n)⟩

variable {Ω ℱ} {A : CochainComplex X.Modules ℕ}
  {ι : (CochainComplex.single₀ X.Modules).obj ℱ ⟶ A}

/-- A lift `A|_Ω ⟶ I` of the identity of `ℱ|_Ω` to the injective resolution of `ℱ|_Ω`. -/
noncomputable def IsOpenResolution.descRestrict (hA : IsOpenResolution Ω ι) :
    restrictComplex Ω.ι A ⟶ (injectiveResolution (ℱ.restrict Ω.ι)).cocomplex :=
  have := hA.quasiIso
  InjectiveResolution.descOfQuasiIso (𝟙 _) _ (restrictAugmentation Ω ι)

lemma IsOpenResolution.descRestrict_comm (hA : IsOpenResolution Ω ι) :
    (restrictAugmentation Ω ι).f 0 ≫ hA.descRestrict.f 0 =
      (injectiveResolution (ℱ.restrict Ω.ι)).ι.f 0 := by
  have := hA.quasiIso
  have h := congrArg (fun h ↦ HomologicalComplex.Hom.f h 0)
    (InjectiveResolution.descOfQuasiIso_commutes (𝟙 _) (injectiveResolution (ℱ.restrict Ω.ι))
      (restrictAugmentation Ω ι))
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, CategoryTheory.Functor.map_id,
    HomologicalComplex.id_f, Category.id_comp] at h
  exact h

/-- The cochain map from an `Ω`-resolution of `ℱ` to the pushforward of the injective resolution
of `ℱ|_Ω`, adjoint to a lift of the identity of `ℱ|_Ω`. -/
noncomputable def IsOpenResolution.toPushforwardResolution (hA : IsOpenResolution Ω ι) :
    A ⟶ pushforwardResolution Ω ℱ where
  f n := (restrictAdjunction Ω.ι).unit.app (A.X n) ≫ (pushforward Ω.ι).map (hA.descRestrict.f n)
  comm' i j _ := by
    have h₁ := (restrictAdjunction Ω.ι).unit.naturality (A.d i j)
    have h₂ := hA.descRestrict.comm i j
    dsimp only [Functor.id_map, Functor.comp_map] at h₁
    rw [reassoc_of% h₁, Category.assoc]
    congr 1
    change (pushforward Ω.ι).map _ ≫ (pushforward Ω.ι).map
      ((injectiveResolution (ℱ.restrict Ω.ι)).cocomplex.d i j) = _
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact congrArg _ h₂

lemma IsOpenResolution.comp_toPushforwardResolution (hA : IsOpenResolution Ω ι) :
    ι ≫ hA.toPushforwardResolution = (CochainComplex.single₀ X.Modules).map
      ((restrictAdjunction Ω.ι).unit.app ℱ) ≫ pushforwardResolutionι Ω ℱ := by
  have h := hA.descRestrict_comm
  refine HomologicalComplex.from_single_hom_ext ?_
  have h₁ := (restrictAdjunction Ω.ι).unit.naturality (ι.f 0)
  dsimp only [Functor.id_map, Functor.comp_map] at h₁
  simp only [HomologicalComplex.comp_f, toPushforwardResolution, pushforwardResolutionι,
    CochainComplex.single₀_map_f_zero]
  rw [reassoc_of% h₁, ← Functor.map_comp]
  simp only [restrictAugmentation, HomologicalComplex.comp_f,
    HomologicalComplex.singleMapHomologicalComplex_inv_app_self] at h
  simp only [HomologicalComplex.singleMapHomologicalComplex_inv_app_self]
  simp only [Functor.mapHomologicalComplex_map_f]
  rw [← h]
  simp [Functor.map_comp]

end Pushforward

section Comparison

variable {Ω : X.Opens}

/-- A cochain map between `Ω`-resolutions over a morphism which is an isomorphism on `Ω` induces
isomorphisms on the cohomology of the sections over `Ω`. -/
lemma IsOpenResolution.isIso_homologyMap {ℱ 𝒢 : X.Modules} {A B : CochainComplex X.Modules ℕ}
    {ι : (CochainComplex.single₀ X.Modules).obj ℱ ⟶ A}
    {ι' : (CochainComplex.single₀ X.Modules).obj 𝒢 ⟶ B}
    (hA : IsOpenResolution Ω ι) (hB : IsOpenResolution Ω ι') (φ : ℱ ⟶ 𝒢)
    [IsIso ((restrictFunctor Ω.ι).map φ)] (c : A ⟶ B)
    (comm : ι ≫ c = (CochainComplex.single₀ X.Modules).map φ ≫ ι') (q : ℕ) :
    IsIso (HomologicalComplex.homologyMap
      (((sectionsOver Ω).mapHomologicalComplex _).map c) q) := by
  have h := hA.iso_hom_naturality hB φ c comm q
  have : IsIso (((globalSectionsFunctor Ω).rightDerived q).map ((restrictFunctor Ω.ι).map φ) ≫
      (hB.iso q).hom) := inferInstance
  rw [h] at this
  exact IsIso.of_isIso_comp_left (hA.iso q).hom _

/-- The restriction to `Ω₂ ≤ Ω₁` of the unit `ℱ ⟶ j_* (ℱ|_{Ω₁})` is an isomorphism. -/
instance isIso_restrict_map_unit {Ω₁ Ω₂ : X.Opens} [Fact (Ω₂ ≤ Ω₁)] (ℱ : X.Modules) :
    IsIso ((restrictFunctor Ω₂.ι).map ((restrictAdjunction Ω₁.ι).unit.app ℱ)) := by
  have h₁ : IsIso ((restrictFunctor Ω₁.ι).map ((restrictAdjunction Ω₁.ι).unit.app ℱ)) := by
    have := (restrictAdjunction Ω₁.ι).left_triangle_components ℱ
    have : IsIso ((restrictFunctor Ω₁.ι).map ((restrictAdjunction Ω₁.ι).unit.app ℱ) ≫
        (restrictAdjunction Ω₁.ι).counit.app ((restrictFunctor Ω₁.ι).obj ℱ)) := by
      rw [this]
      infer_instance
    exact IsIso.of_isIso_comp_right _ ((restrictAdjunction Ω₁.ι).counit.app _)
  exact (NatIso.isIso_map_iff (restrictFunctorIsoOfLE (Fact.out : Ω₂ ≤ Ω₁)) _).2
    (inferInstanceAs (IsIso ((restrictFunctor (X.homOfLE _)).map
      ((restrictFunctor Ω₁.ι).map ((restrictAdjunction Ω₁.ι).unit.app ℱ)))))

/-- **Naturality of `openComparison` for the restriction to a smaller open.** -/
lemma openComparison_naturality {Ω₁ Ω₂ : X.Opens} (h : Ω₂ ≤ Ω₁) {ℱ : X.Modules}
    {A B : CochainComplex X.Modules ℕ}
    {ι : (CochainComplex.single₀ X.Modules).obj ℱ ⟶ A}
    {ι' : (CochainComplex.single₀ X.Modules).obj ℱ ⟶ B}
    (hA₁ : IsOpenResolution Ω₁ ι) (hB₁ : IsOpenResolution Ω₁ ι')
    (hA₂ : IsOpenResolution Ω₂ ι) (hB₂ : IsOpenResolution Ω₂ ι') (q : ℕ) :
    (openComparison hA₁ hB₁ q).hom ≫ HomologicalComplex.homologyMap
        ((NatTrans.mapHomologicalComplex (sectionsOverRestrict h) _).app B) q =
      HomologicalComplex.homologyMap
        ((NatTrans.mapHomologicalComplex (sectionsOverRestrict h) _).app A) q ≫
        (openComparison hA₂ hB₂ q).hom := by
  have : Fact (Ω₂ ≤ Ω₁) := ⟨h⟩
  have hP₁ := isOpenResolution_pushforwardResolution Ω₁ ℱ
  have hP₂ := isOpenResolution_pushforwardResolution_of_le Ω₁ ℱ h
  have ha := hA₁.comp_toPushforwardResolution
  have hb := hB₁.comp_toPushforwardResolution
  have e₁ := openComparison_hom_comp_eq hA₁ hB₁ hP₁ _ _ _ ha hb q
  have e₂ := openComparison_hom_comp_eq hA₂ hB₂ hP₂ _ _ _ ha hb q
  have := hB₂.isIso_homologyMap hP₂ _ _ hb q
  have nat (C D : CochainComplex X.Modules ℕ) (c : C ⟶ D) :
      HomologicalComplex.homologyMap (((sectionsOver Ω₁).mapHomologicalComplex _).map c) q ≫
        HomologicalComplex.homologyMap
          ((NatTrans.mapHomologicalComplex (sectionsOverRestrict h) _).app D) q =
      HomologicalComplex.homologyMap
          ((NatTrans.mapHomologicalComplex (sectionsOverRestrict h) _).app C) q ≫
        HomologicalComplex.homologyMap (((sectionsOver Ω₂).mapHomologicalComplex _).map c) q := by
    rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp,
      (NatTrans.mapHomologicalComplex (sectionsOverRestrict h) _).naturality]
  rw [← cancel_mono (HomologicalComplex.homologyMap
    (((sectionsOver Ω₂).mapHomologicalComplex _).map hB₁.toPushforwardResolution) q),
    Category.assoc, ← nat, reassoc_of% e₁, nat, Category.assoc, e₂]

/-- An injective resolution of `ℱ` on `X` is an `Ω`-resolution for every open `Ω`. -/
lemma isOpenResolution_injectiveResolution {ℱ : X.Modules} (I : InjectiveResolution ℱ)
    (Ω : X.Opens) : IsOpenResolution Ω I.ι := by
  refine ⟨?_, fun n ↦ rightAcyclic_globalSections_of_isFlasque _
    (isFlasque_restrict _ _ (isFlasque_of_injective _))⟩
  dsimp only [restrictAugmentation]
  infer_instance

end Comparison

end AlgebraicGeometry.Scheme.Modules
