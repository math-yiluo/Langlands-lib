/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.InternalScalarPullbackNormalizationData

/-! # Universal scalar computation under section reconstruction

Source: Stacks Project, Tags 03EK, 06YS, 06YY, 0D6D and 07A6.
(auxiliary; not a blueprint node)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
open CategoryTheory.InternalAbelianSheafModule

private theorem map_id_cleanup
    {A C D : Type*} [Category A] [Category C] [Category D]
    (F : A ⥤ D) (G : C ⥤ D) {x : A} {y : C} (t : F.obj x ⟶ G.obj y) :
    F.map (𝟙 x) ≫ t ≫ G.map (𝟙 y) ≫ 𝟙 _ = t := by
  simp only [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]

private theorem map_id_cleanup_left
    {A B : Type*} [Category A] [Category B]
    (F : A ⥤ B) {x : A} {y : B} (t : F.obj x ⟶ y) :
    F.map (𝟙 x) ≫ t ≫ 𝟙 y = t := by
  simp only [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]


private theorem natTrans_app_eq_of_epi
    {A B : Type*} [Category A] [Category B] {F G : A ⥤ B}
    (θ₁ θ₂ : F ⟶ G) {P K : A} (f : K ⟶ P) [Epi (F.map f)]
    (h : θ₁.app K = θ₂.app K) : θ₁.app P = θ₂.app P := by
  apply (cancel_epi (F.map f)).mp
  rw [θ₁.naturality, h, ← θ₂.naturality]

private theorem cochain_comparison_app
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    [Preadditive A] [Preadditive B] [Preadditive C] [Preadditive D]
    {F : A ⥤ B} {G : B ⥤ D} {H : A ⥤ C} {I : C ⥤ D}
    [F.Additive] [G.Additive] [H.Additive] [I.Additive]
    (e : F ⋙ G ≅ H ⋙ I) (P : CochainComplex A ℤ) :
    ((Functor.mapHomologicalComplexCompIso e (.up ℤ) ≪≫
      (Functor.mapHomologicalComplexCompIso (Iso.refl (H ⋙ I)) (.up ℤ)).symm).hom.app P) =
      (NatIso.mapHomologicalComplex e (.up ℤ)).hom.app P := by
  apply HomologicalComplex.hom_ext
  intro n
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    HomologicalComplex.comp_f, Functor.mapHomologicalComplexCompIso_hom_app_f,
    Functor.mapHomologicalComplexCompIso_inv_app_f, Iso.refl_inv, NatTrans.id_app,
    NatIso.mapHomologicalComplex_hom_app_f]
  erw [Category.comp_id]

universe uc vc w

private theorem resolution_properties_of_iso
    {C : Type uc} [Category.{vc} C] [EssentiallySmall.{w} C]
    {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    [HasSheafify J AddCommGrpCat.{w}] {R : Sheaf J CommRingCat.{w}}
    {P Q : CochainComplex (SheafOfModules.{w}
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R)) ℤ}
    (e : P ≅ Q) (hQ : CochainComplex.IsKFlatIndependentCoefficients (R := R) Q)
    (hflat : letI := SheafOfModules.isMonoidal_W_independentCoefficients R
      ∀ n : ℤ, exactFunctor _ _
        (@MonoidalCategory.tensorRight _ _ (SheafOfModules.monoidalCategory R) (Q.X n))) :
    CochainComplex.IsKFlatIndependentCoefficients (R := R) P ∧
      (∀ n : ℤ, SheafOfModules.IsFlatOnSite (R := R) (P.X n)) := by
  have (I : Type w) : HasColimitsOfShape (Discrete I) (PresheafOfModules.{w}
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R).obj) :=
    PresheafOfModules.hasColimitsOfShape _ _
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients R
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients R
  constructor
  · intro Z hZ n
    exact (hQ Z hZ n).of_iso
      ((((MonoidalCategory.curriedTensor _).map₂CochainComplex).obj Z).mapIso e.symm)
  · intro n
    let en := (HomologicalComplex.eval _ (.up ℤ) n).mapIso e
    have hn := (exactFunctor _ _).prop_of_iso
      ((MonoidalCategory.curriedTensor _).flip.mapIso en.symm) (hflat n)
    exact (exactFunctor _ _).prop_of_iso
      (SheafOfModules.siteSheafTensorRightIso R _).symm hn

namespace AlgebraicGeometry.ProEtale.QuotientChange
variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
  [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (ModuleRingedComparison.modules Λ T)]
  [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (ModuleRingedComparison.modules Λ' T)]

-- Track the specified localization and termwise-equivalence instances through the diagram.
/-- The normalized scalar comparison intertwines the universal computation maps on
all complexes, without flatness hypotheses on their terms.
Source: Stacks Project, Tags 06YS, 06YY and 07A6.
(auxiliary; not a blueprint node)

Proof: both displayed paths are components of natural transformations on internal
cochain complexes. Resolve the section image of an arbitrary complex by a flat-term
K-flat complex (06YS). Lift this resolution through the termwise section equivalence.
Its counit identifies the section image of the lift with the chosen resolution.
Tensoring preserves isomorphisms, so K-flatness and termwise flatness transport along
this counit. Apply SectionScalarNormalized to the lift. Naturality along the lifted
quasi-isomorphism then gives the equation at the original complex, since its image
under localization, the section equivalence and the derived scalar functor is an
isomorphism and hence cancellable. -/
theorem section_scalar_computation_all (a : Λ ⟶ Λ') [IsMonHom a] (T : Scheme.{u})
    (s : SectionScalarComparison a T) (h : SectionScalarNormalized a T s)
    (P : CochainComplex (Modules Λ T) ℤ) :
    @Eq ((ModuleRingedComparison.derivedEquivalence Λ' T).functor.obj
      ((D a T).obj (DerivedCategory.Q.obj P)) ⟶
      DerivedCategory.Q.obj ((s.pair.extension.mapHomologicalComplex (.up ℤ)).obj
        (((ModuleRingedComparison.equivalence Λ T).functor.mapHomologicalComplex (.up ℤ)).obj
          P)))
      ((ModuleRingedComparison.derivedEquivalence Λ' T).functor.map (compute a T P) ≫
        (ModuleRingedComparison.sectionLocalizationComparison Λ' T
          (((extension a T).mapHomologicalComplex (.up ℤ)).obj P)).hom ≫
        DerivedCategory.Q.map ((Functor.mapHomologicalComplexCompIso s.ordinary (.up ℤ) ≪≫
          (Functor.mapHomologicalComplexCompIso (Iso.refl
            ((ModuleRingedComparison.equivalence Λ T).functor ⋙ s.pair.extension))
            (.up ℤ)).symm).hom.app P))
      (s.derived.hom.app (DerivedCategory.Q.obj P) ≫
        s.pair.derived.map (ModuleRingedComparison.sectionLocalizationComparison Λ T P).hom ≫
        SheafOfModules.scalarPairComplexComparison.{u + 1, u, u + 1, u + 1}
          s.pair.extension s.pair.extension_additive s.pair.derived s.pair.counit
          (((ModuleRingedComparison.equivalence Λ T).functor.mapHomologicalComplex (.up ℤ)).obj
            P)) := by
  classical
  let ER := (ModuleRingedComparison.equivalence Λ T).functor
  let ec := (ModuleRingedComparison.equivalence Λ T).mapHomologicalComplex (.up ℤ)
  obtain ⟨R, r, hR, hflat, hr, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients
      (R := ModuleRingedComparison.ring Λ T) (ec.functor.obj P)
  let K := ec.inverse.obj R
  let e : ec.functor.obj K ≅ R := ec.counitIso.app R
  let f : K ⟶ P := ec.functor.preimage (e.hom ≫ r)
  have hfmap : ec.functor.map f = e.hom ≫ r := ec.functor.map_preimage _
  have : QuasiIso r := hr
  have hf : QuasiIso f := by
    apply (HomologicalComplex.quasiIso_map_iff_of_preservesHomology f ER).mp
    change QuasiIso (ec.functor.map f)
    rw [hfmap]
    infer_instance
  have hproperties := resolution_properties_of_iso
    (R := ModuleRingedComparison.ring Λ T) e hR hflat
  have hK := hproperties.1
  have hKflat := hproperties.2
  let ES := (ModuleRingedComparison.equivalence Λ' T).functor
  let ED := (ModuleRingedComparison.derivedEquivalence Λ' T).functor
  let E := (extension a T).mapHomologicalComplex (.up ℤ)
  let ε : DerivedCategory.Q ⋙ D a T ⟶ E ⋙ DerivedCategory.Q :=
    Functor.whiskerRight (DerivedCategory.quotientCompQhIso _).inv (D a T) ≫
      Functor.whiskerLeft (HomotopyCategory.quotient _ (.up ℤ)) (scalarCounit a T) ≫
      Functor.whiskerRight ((extension a T).mapHomotopyCategoryFactors (.up ℤ)).hom
        DerivedCategory.Qh ≫
      Functor.whiskerLeft E (DerivedCategory.quotientCompQhIso _).hom
  let ε' : DerivedCategory.Q ⋙ s.pair.derived ⟶
      s.pair.extension.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
    Functor.whiskerRight (DerivedCategory.quotientCompQhIso _).inv s.pair.derived ≫
      Functor.whiskerLeft (HomotopyCategory.quotient _ (.up ℤ)) s.pair.counit ≫
      Functor.whiskerLeft (s.pair.extension.mapHomologicalComplex (.up ℤ))
        (DerivedCategory.quotientCompQhIso _).hom
  have he (K : CochainComplex (Modules Λ T) ℤ) : compute a T K = ε.app K := by
    rfl
  have he' (K : CochainComplex (ModuleRingedComparison.modules Λ T) ℤ) :
      SheafOfModules.scalarPairComplexComparison s.pair.extension s.pair.extension_additive
        s.pair.derived s.pair.counit K = ε'.app K := by
    rfl
  let α := Functor.mapHomologicalComplexCompIso s.ordinary (.up ℤ) ≪≫
    (Functor.mapHomologicalComplexCompIso (Iso.refl
      ((ModuleRingedComparison.equivalence Λ T).functor ⋙ s.pair.extension)) (.up ℤ)).symm
  let θ₁ : DerivedCategory.Q ⋙ D a T ⋙ ED ⟶
      ec.functor ⋙ s.pair.extension.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
    Functor.whiskerRight ε ED ≫
      Functor.whiskerLeft E ES.mapDerivedCategoryFactors.hom ≫
      Functor.whiskerRight α.hom
        DerivedCategory.Q
  let θ₂ : DerivedCategory.Q ⋙ D a T ⋙ ED ⟶
      ec.functor ⋙ s.pair.extension.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
    Functor.whiskerLeft DerivedCategory.Q s.derived.hom ≫
      Functor.whiskerRight ER.mapDerivedCategoryFactors.hom s.pair.derived ≫
      Functor.whiskerLeft ec.functor ε'
  have hgood : θ₁.app K = θ₂.app K := by
    simpa only [θ₁, θ₂, α, cochain_comparison_app, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, he, he', ED, ES, ER, E, ec,
      ModuleRingedComparison.sectionLocalizationComparison, Iso.app_hom,
      Equivalence.mapHomologicalComplex_functor, Functor.comp_obj] using h.2.2 K hK hKflat
  have hall : θ₁.app P = θ₂.app P := by
    have : QuasiIso f := hf
    have : IsIso ((DerivedCategory.Q ⋙ D a T ⋙ ED).map f) := by
      change IsIso (ED.map ((D a T).map (DerivedCategory.Q.map f)))
      infer_instance
    exact natTrans_app_eq_of_epi θ₁ θ₂ f hgood
  simpa only [θ₁, θ₂, α, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, he, he', ED, ES, ER, E, ec,
    ModuleRingedComparison.sectionLocalizationComparison, Iso.app_hom,
      Equivalence.mapHomologicalComplex_functor, Functor.comp_obj] using hall

end AlgebraicGeometry.ProEtale.QuotientChange
