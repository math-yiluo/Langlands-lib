/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedMayerVietorisCanonicalData
import WeilConjectures.AlgebraicGeometry.DerivedDirectImageKInjectiveShiftComparison
import WeilConjectures.AlgebraicGeometry.DerivedMayerVietorisImageResolutionComparison

/-! # DerivedMayerVietorisDirectImageBoundary

Source: Stacks Project, Cohomology, Tags 08BV and 0D5T; Derived Categories of Schemes,
Tag 0DJ9 (blueprint: lem-pc-derived-mayer-vietoris-direct-image-boundary).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits TopologicalSpace Pretriangulated

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048

noncomputable section
namespace AlgebraicGeometry

attribute [local instance 2000] schemeMVModuleAbelian

private theorem openImage_isKInjective (X : Scheme.{u}) (U : X.Opens)
    (I : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    [I.IsKInjective] : (schemeOpenModuleImageComplex X U I).IsKInjective := by
  have : (Scheme.Modules.pushforward U.ι).Additive :=
    Functor.additive_of_preserves_binary_products _
  have := isKInjective_schemeOpenRestriction X U I
  have := (schemeOpenModuleAdjunction X U).preservesKInjectiveComplexes
  change CochainComplex.IsKInjective
    (((Scheme.Modules.pushforward U.ι).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (((schemeOpenRestriction X U).mapHomologicalComplex (ComplexShape.up ℤ)).obj I))
  infer_instance

private theorem biprod_isKInjective
    {A : Type*} [Category A] [Abelian A]
    (I J : CochainComplex A ℤ) [I.IsKInjective] [J.IsKInjective] :
    (I ⊞ J).IsKInjective := by
  constructor
  intro K f hK
  have hI := (CochainComplex.IsKInjective.homotopyZero (f ≫ biprod.fst) hK).compRight
    (biprod.inl : I ⟶ I ⊞ J)
  have hJ := (CochainComplex.IsKInjective.homotopyZero (f ≫ biprod.snd) hK).compRight
    (biprod.inr : J ⟶ I ⊞ J)
  have he : (f ≫ biprod.fst) ≫ biprod.inl + (f ≫ biprod.snd) ≫ biprod.inr = f := by
    rw [Category.assoc, Category.assoc, ← Preadditive.comp_add,
      biprod.total, Category.comp_id]
  have ht := hI.add hJ
  rw [he] at ht
  exact ⟨ht.trans (Homotopy.ofEq (by simp))⟩

private theorem mv_degreewise_split (X : Scheme.{u}) (U V : X.Opens)
    (hcover : U ⊔ V = ⊤)
    (I : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (hI : ∀ n : ℤ, Injective (I.X n)) (n : ℤ) :
    Nonempty (((schemeMayerVietorisComplex X U V I).map
      (HomologicalComplex.eval (SheafOfModules.{u} (moduleRings X.toRingedSpace))
        (ComplexShape.up ℤ) n)).Splitting) := by
  have : Injective (((schemeMayerVietorisComplex X U V I).map
      (HomologicalComplex.eval (SheafOfModules.{u} (moduleRings X.toRingedSpace))
        (ComplexShape.up ℤ) n)).X₁) := hI n
  exact ⟨((schemeMayerVietorisComplex_shortExact X U V hcover I hI).map_of_exact
    (HomologicalComplex.eval _ _ n)).splittingOfInjective⟩

/-- The explicitly constructed boundary commutes with the recorded direct-image comparisons.
Source: Stacks Tags 08BV, 0D5T and 0DJ9
(blueprint: lem-pc-derived-mayer-vietoris-direct-image-boundary).

Proof:
1. Use the fixed K-injective representative I of E with injective terms. Its concrete
   Mayer--Vietoris sequence is short exact and split in each degree, since its first
   term is injective. Its other terms are K-injective: restriction preserves this
   property, open direct image is right adjoint to exact restriction, and biproducts
   of K-injective complexes are K-injective.
2. Apply the termwise-split short-exact-sequence triangle comparison for h_*.
   It identifies the image boundary, including the commutation with shift, with the
   boundary of the termwise image sequence.
3. Resolve h_*I by a K-injective complex J with injective terms. The resolution map
   and its restrictions induce a map from the image sequence to the Mayer--Vietoris
   sequence of J. The intersection component is the direct-image composition followed
   by the inverse open-restriction comparison, by their K-injective computation formulas.
4. Apply triangleOfSESδ_naturality to this map of short exact sequences. Compose with
   the resolution isomorphisms and the explicit intersection comparisons used in
   schemeMVBoundary. Cancel the computation isomorphisms. Naturality of these comparisons
   and of commutation with shift gives the displayed equation for E. No assertion
   about the other two triangle squares is used here.
-/
theorem schemeMV_directImage_boundary
    (X Y : Scheme.{u}) (h : X ⟶ Y) (U V : Y.Opens)
    (hcover : U ⊔ V = ⊤)
    (hcover' : (h ⁻¹ᵁ U) ⊔ (h ⁻¹ᵁ V) = ⊤)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ T : X.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings T.toScheme.toRingedSpace))]
    [∀ T : Y.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings T.toScheme.toRingedSpace))]
    (E : schemeDerivedCategory X) :
    (schemeMVImageTriangle h
      (schemeMVTriangle X (h ⁻¹ᵁ U) (h ⁻¹ᵁ V) hcover' E)).mor₃ =
      (schemeMVOpenComparison h (U ⊓ V) E).hom ≫
        schemeMVBoundary Y U V hcover ((schemeDerivedDirectImage h).obj E) := by
  let I := schemeMVResolution X E
  let J := schemeMVResolution Y ((schemeDerivedDirectImage h).obj E)
  let S := schemeMayerVietorisComplex X (h ⁻¹ᵁ U) (h ⁻¹ᵁ V) I
  let T := schemeMayerVietorisComplex Y U V J
  let g := h.toLRSHom.toShHom
  let R := schemeDerivedDirectImage h
  have hI (n : ℤ) : Injective (I.X n) := inferInstance
  have hS : S.ShortExact :=
    schemeMayerVietorisComplex_shortExact X _ _ hcover' I hI
  have hT : T.ShortExact :=
    schemeMayerVietorisComplex_shortExact Y _ _ hcover J (fun _ ↦ inferInstance)
  have hU := openImage_isKInjective X (h ⁻¹ᵁ U) I
  have hV := openImage_isKInjective X (h ⁻¹ᵁ V) I
  have hW := openImage_isKInjective X ((h ⁻¹ᵁ U) ⊓ (h ⁻¹ᵁ V)) I
  have : S.X₁.IsKInjective := inferInstanceAs I.IsKInjective
  have : S.X₂.IsKInjective := biprod_isKInjective _ _
  have : S.X₃.IsKInjective := hW
  obtain ⟨hImage, _, _, _, hδ, _⟩ :=
    RingedSpace.derivedModuleDirectImage_termwise_split_ses_triangle g S hS
      (mv_degreewise_split X _ _ hcover' I hI)
  obtain ⟨m, hm₁, hm₃⟩ := schemeMV_image_resolution_comparison X Y h U V E
  let e₁ := RingedSpace.derivedModuleDirectImageKInjectiveIso g S.X₁
  let e₃ := RingedSpace.derivedModuleDirectImageKInjectiveIso g S.X₃
  let rX := schemeMVResolutionIso X E
  let rY := schemeMVResolutionIso Y (R.obj E)
  let a := (((schemeMVDerivedRestriction X ((h ⁻¹ᵁ U) ⊓ (h ⁻¹ᵁ V))) ⋙
    schemeDerivedDirectImage ((h ⁻¹ᵁ U) ⊓ (h ⁻¹ᵁ V)).ι).map rX.inv ≫
      (schemeOpenModuleImageComplexComparison X ((h ⁻¹ᵁ U) ⊓ (h ⁻¹ᵁ V)) I
        (schemeMVAdjunction X ((h ⁻¹ᵁ U) ⊓ (h ⁻¹ᵁ V)))).inv)
  let b := (((schemeMVDerivedRestriction Y (U ⊓ V)) ⋙
    schemeDerivedDirectImage (U ⊓ V).ι).map rY.inv ≫
      (schemeOpenModuleImageComplexComparison Y (U ⊓ V) J
        (schemeMVAdjunction Y (U ⊓ V))).inv)
  have hd : R.map (DerivedCategory.triangleOfSESδ hS) ≫
      (R.commShiftIso (1 : ℤ)).hom.app (DerivedCategory.Q.obj I) ≫ e₁.hom⟦(1 : ℤ)⟧' =
      e₃.hom ≫ DerivedCategory.triangleOfSESδ hImage := by
    simpa only [S, I, R, e₁, e₃, schemeMayerVietorisComplex,
      Category.assoc,
      RingedSpace.derivedModuleDirectImageKInjectiveIso_shift] using hδ
  have hfirst : e₁.hom ≫ DerivedCategory.Q.map m.τ₁ ≫ rY.hom = R.map rX.hom := hm₁
  have hthird : R.map a ≫ e₃.hom ≫ DerivedCategory.Q.map m.τ₃ =
      (schemeMVOpenComparison h (U ⊓ V) E).hom ≫ b := hm₃
  have hn := DerivedCategory.triangleOfSESδ_naturality hImage hT m
  change R.map (schemeMVBoundary X (h ⁻¹ᵁ U) (h ⁻¹ᵁ V) hcover' E) ≫
      (R.commShiftIso (1 : ℤ)).hom.app E =
    (schemeMVOpenComparison h (U ⊓ V) E).hom ≫
      schemeMVBoundary Y U V hcover (R.obj E)
  dsimp only [schemeMVBoundary]
  suffices hc : R.map (a ≫ DerivedCategory.triangleOfSESδ hS ≫ rX.hom⟦(1 : ℤ)⟧') ≫
      (R.commShiftIso (1 : ℤ)).hom.app E =
    (schemeMVOpenComparison h (U ⊓ V) E).hom ≫
      (b ≫ DerivedCategory.triangleOfSESδ hT ≫ rY.hom⟦(1 : ℤ)⟧') by
    simpa only [a, b, Category.assoc] using hc
  simp only [Functor.map_comp, Category.assoc]
  have hshift := (R.commShiftIso (1 : ℤ)).hom.naturality rX.hom
  simp only [Functor.comp_map] at hshift
  erw [hshift]
  change R.map a ≫ R.map (DerivedCategory.triangleOfSESδ hS) ≫
      (R.commShiftIso (1 : ℤ)).hom.app (DerivedCategory.Q.obj I) ≫
      (R.map rX.hom)⟦(1 : ℤ)⟧' = _
  rw [← hfirst]
  simp only [Functor.map_comp]
  erw [reassoc_of% hd, reassoc_of% hn, reassoc_of% hthird]

end AlgebraicGeometry
